# SPDX-License-Identifier: Apache-2.0

# Copyright (c) 2021 Ryan Lipscombe
# 
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
#     http://www.apache.org/licenses/LICENSE-2.0
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

## This module generates code to perform ECS state changes like adding
## and removing components or entities.
## 
## `newStateChangeDetails` creates a `StateChangeDetails` object to hold
## the state change parameters and context.
## 
## Use `applyChange` to input state changes to `StateChangeDetails`.
## 
## Once the state change has been set up, calling `buildStateChange`
## populates `StateChangeDetails` with the code for the required tasks
## involved, such as updating entity metadata, syncing systems, and
## running user events.
## 
## By default, `buildStateChange` uses `StateChangeDetails.values`
## to access user parameters where appropriate.
## 
## This behaviour can be changed by passing procedures that generate
## 'get' and 'has' code. This is used for example in `construct` and
## `clone` to access a run time hash table for the operation parameters.
## 
## The resultant task code in `StateChangeDetails` can then be assembled
## into user facing state change operations, such as `newEntityWith`,
## `addComponents`, `construct`, and so on.


import macros, macrocache, strutils, sets, tables
import ../sharedtypes, ecsstatedb
import utils, eventutils, statechangeutils, mutationtracking


# ---------------------------
# System state change parsing
# ---------------------------

type
  ComponentGroup* = object
    required*: ComponentSet
    requiredOr*: ComponentSet
    negated*: ComponentSet

  SystemUpdate* = ref object
    sysFetches*: SystemSet    # Check/get the entity in these systems.
    update*: NimNode
    events*: NimNode
    deferredEvents*: NimNode  # System events triggered by negation to be run after system state changes.
    # Calls to shared per-system procs (see `makeSystemStateProcs`).
    # These perform their own system fetch, so don't need `sysFetches`.
    procUpdate*: NimNode
    procEvents*: NimNode
    procDeferredEvents*: NimNode
  
  # The update groups and event groups must be executed in the order
  # they're provided so that the user can rely on predictable state
  # changes.
  ComponentUpdateGroups*  = OrderedTable[ComponentGroup, SystemUpdate]
  SystemUpdateGroups*     = OrderedTable[SystemIndex, SystemUpdate]
  
  StateChangeDetailsKind* = enum
    scdkNewEntity = "New entity",
    scdkAdd = "Add component(s)",
    scdkRemove = "Remove components(s)",
    scdkDelete = "Delete entity",
    scdkConstruct = "Construct entity",
    scdkClone = "Clone entity"

  ## Stores state changes details and code output.
  StateChangeDetails* = ref object

    kind*: StateChangeDetailsKind

    # User passed data.
    values*: NimNode

    passed*: seq[ComponentTypeId]
    passedSet*: ComponentSet
    
    # Generated ident postfix for this operation.
    suffix*: string

    newComps*: ComponentSet         # Create a new slot for this component.
    compFetches*: ComponentSet      # Fetch these from the entity at the start of the op.
    compRemoves*: ComponentSet      # Remove these components from the entity.

    componentGroups*: ComponentUpdateGroups   # Guard updates by component set.
    systemGroups*: SystemUpdateGroups         # Guard updates by system.
    compAccess*: ComponentAccessProc          # A proc taking typeId and returning code to read a component's data.
    compValid*: ComponentValidProc            # A proc returning a bool statement for component existence.

    sysProcessed*: NimNode    # Set to a set[SysEnum] ident.
    iterating*: NimNode       # A for var expected to contain the typed component index.

    newDecls*: NimNode        # Declare and variable init code.
    fetches*: NimNode         # Code to perform fetches.
    postFetches*: NimNode     # Run time checks after fetched have been performed.
    asserts*: NimNode         # Code to assert expected states.
    systemUpdates*: NimNode   # Perform the state change for systems.
    allEvents*: NimNode       # All user events.
    deferredEvents*: NimNode  # Events that need to be run after system state changes.


proc newSystemUpdate*(): SystemUpdate =
  SystemUpdate(
    update: newStmtList(),
    events: newStmtList(),
    deferredEvents: newStmtList(),
    procUpdate: newStmtList(),
    procEvents: newStmtList(),
    procDeferredEvents: newStmtList()
  )


# -------------------------
# Shared per-system procs
# -------------------------

# Removing an entity from a system, and the events for entities being added to
# or removed from a system, don't depend on the state change that causes them.
# Instead of generating this code at every state change for every system
# affected, it's generated once per system in `makeSystemStateProcs` and
# state changes call these procs.
#
# State changes within events still generate their code inline, as these
# perform extra compile time checks that depend on the event environment.

const sysProcSuffix = "SysProc"

proc sysProcsTable(id: EcsIdentity): CacheTable {.compileTime.} =
  CacheTable(id.string & "SysStateProcs")

proc getSysProc(id: EcsIdentity, kind: string, sys: SystemIndex): NimNode =
  ## Returns the ident of a shared proc for `sys`, or nil if it's not available.
  if id.ecsEventEnv.len > 0:
    return nil
  let key = kind & $sys.int
  if key in id.sysProcsTable: id.sysProcsTable[key]
  else: nil

proc buildAddSystemEvents(id: EcsIdentity, entity: NimNode, sys: SystemBuildInfo, sysRow: NimNode): tuple[events: NimNode, used: bool] =
  ## Builds the events for `entity` being added to `sys`.
  var
    events = newStmtList()
    context = id.newEventContext(entity, sys, sysRow)

  for c in id.building(id.ecsSysRequirements sys.index):
    let
      sysVar = sys.variable
      fieldIdent = ident c.lcName
      inst = quote do:
        `sysVar`.groups[`sysRow`].`fieldIdent`
    
    context.component = (c, inst)

    events.invokeEvent(id, context, ekCompAddTo)
    events.invokeEvent(id, context, ekSystemAddAny)

  # System events.

  events.invokeEvent(id, context, ekRowAdded)
  events.invokeEvent(id, context, ekRowAddedCb)

  (events, context.used)

proc buildRemoveSystemEvents(id: EcsIdentity, entity: NimNode, sys: SystemBuildInfo, sysRow: NimNode): tuple[events: NimNode, used: bool] =
  ## Builds the events for `entity` being removed from `sys`.
  let
    sysVar = sys.variable
  var
    context = newEventContext(id, entity, sys, sysRow)
    sysEvents = newStmtList()

  for c in id.building(id.ecsSysRequirements sys.index):
    let
      fieldIdent = ident c.lcName
      inst =
        quote do:
          `sysVar`.groups[`sysRow`].`fieldIdent`

    context.component = (c, inst)

    sysEvents.invokeEvent(id, context, ekCompRemoveFrom)
    sysEvents.invokeEvent(id, context, ekSystemRemoveAny)

  sysEvents.invokeEvent(id, context, ekRowRemoved)
  sysEvents.invokeEvent(id, context, ekRowRemovedCb)

  (sysEvents, context.used)

proc makeSystemStateProcs*(id: EcsIdentity): tuple[forwardDecls, procs: NimNode] =
  ## Generates shared procs for removing an entity from each system and for
  ## system add/remove events.
  ## The forward declarations must be placed before any state changes, and the
  ## procs after state change operations are defined so that events can use them.
  result = (newStmtList(), newStmtList())

  let
    entity = ident "entity"
    entId = newDotExpr(entity, ident "entityId")
    table = id.sysProcsTable

  proc addProc(res: var tuple[forwardDecls, procs: NimNode], name, body: NimNode) =
    res.forwardDecls.add(quote do:
      proc `name`(`entity`: EntityRef)
    )
    res.procs.add(quote do:
      proc `name`(`entity`: EntityRef) =
        `body`
    )

  for sys in id.building(id.allUnsealedSystems):
    let
      sysName = sys.name.capitalizeAscii
      sysFetch = sys.fetchedIdent sysProcSuffix
      row = sysFetch.newDotExpr ident"row"
    var
      fetch = newStmtList()
    fetch.buildFetchSystems(id, entity, @[sys.index], sysProcSuffix)

    # Remove the entity's row.
    block:
      let
        name = ident("ecsRemoveRow" & sysName)
        unregister = id.unregister(sys.index, sys.variable, row, entId)
        body = quote do:
          `fetch`
          if `sysFetch`.found:
            `unregister`
      result.addProc(name, body)
      table["removeRow" & $sys.index.int] = name

    # Events for when the entity is removed.
    block:
      var (events, used) = id.buildRemoveSystemEvents(entity, sys, row)
      if used:
        events.trackMutation(id, ekEntityRemove, id.ecsSysRequirements(sys.index), announce = false)
        let
          name = ident("ecsRemoveEvents" & sysName)
          fetchCopy = fetch.copy
          body = quote do:
            `fetchCopy`
            if `sysFetch`.found:
              `events`
        result.addProc(name, body)
        table["removeEvents" & $sys.index.int] = name

    # Events for when the entity is added.
    block:
      var (events, used) = id.buildAddSystemEvents(entity, sys, row)
      if used:
        events.trackMutation(id, ekEntityAdd, id.ecsSysRequirements(sys.index), announce = false)
        let
          name = ident("ecsAddEvents" & sysName)
          fetchCopy = fetch.copy
          body = quote do:
            `fetchCopy`
            if `sysFetch`.found:
              `events`
        result.addProc(name, body)
        table["addEvents" & $sys.index.int] = name


proc initCode*(scd: var StateChangeDetails) =
  ## Clear generated code but not the state change parameters.
  scd.asserts = newStmtList()
  scd.newDecls = nnkVarSection.newTree()
  scd.fetches = newStmtList()
  scd.postFetches = newStmtList()
  scd.systemUpdates = newStmtList()
  scd.allEvents = newStmtList()
  scd.deferredEvents = newStmtList()
  scd.componentGroups.clear
  scd.systemGroups.clear


proc newStateChangeDetails*(
    kind: StateChangeDetailsKind,
    compAccess: ComponentAccessProc = byFetchedIdent,
    compValid = checkInstanceValid): StateChangeDetails =
  
  result = StateChangeDetails()
  result.kind = kind
  result.compAccess = compAccess
  result.compValid = compValid
  result.initCode


proc newStateChangeDetails*(
    id: EcsIdentity,
    kind: StateChangeDetailsKind,
    values: NimNode,
    compAccess: ComponentAccessProc = byFetchedIdent,
    compValid = checkInstanceValid): StateChangeDetails =
  
  result = newStateChangeDetails(kind, compAccess, compValid)
  result.values = values
  result.passed = id.toTypeList(values)
  result.passedSet = result.passed.toHashSet


proc createComponents(id: EcsIdentity, entity: NimNode, details: var StateChangeDetails) =
  ## Creates the passed components.
  
  if details.values.len == 0:
    return

  assert details.passed.len == details.values.len,
    "Internal error: passed/values mismatch when creating components"

  for i in 0 ..< details.passed.len:
    let
      c = id.getInfo details.passed[i]
      typeId = c.typeId

    details.newComps.incl typeId

    let
      fieldSym = details.compAccess(c, details.suffix)
      instType = c.instanceTy

    if c.isOwned:
      let
        sysVar = id.instantiation c.owner
        # The owned instance referred to here is yet to be created.
        nextSystemRow = quote do:
          `sysVar`.count.`instType`

      details.newDecls.add newIdentDefs(fieldSym, newEmptyNode(), nextSystemRow)
    
    else:
      let
        value = details.values[i]
        newInstance = quote do:
          newInstance(`value`)
      
      details.newDecls.add newIdentDefs(fieldSym, newEmptyNode(), newInstance)


proc buildRemoveCompEvents(id: EcsIdentity, context: var EventContext, c: ComponentBuildInfo): NimNode =
  result = newStmtList()

  result.invokeEvent(id, context, ekRemove)
  result.invokeEvent(id, context, ekRemoveCb)

  if c.isOwned:
    # For unowned components ekDeleteComp is invoked within the component's finalisation proc.
    result.invokeEvent(id, context, ekDeleteComp)


proc removeComponentEvents(id: EcsIdentity, entity: NimNode, details: var StateChangeDetails) =
  ## Invoke remove events for details.passed.

  if not details.iterating.isNil:
    assert details.passed.len > 0, "Internal error: there must be at least one component passed when iterating"
    let c = id.getInfo(details.passed[0])
    var context = newEventContext(entity, c, details.iterating)
    let events = id.buildRemoveCompEvents(context, c)
    if events.len > 0:
      details.allEvents.add events

  else:
    for c in id.building(details.passed):
      let fetchedIdent = details.compAccess(c, details.suffix)
      var context = newEventContext(entity, c, fetchedIdent)
      let events = id.buildRemoveCompEvents(context, c)
      
      if events.len > 0:
        details.allEvents.add events
        details.compFetches.incl c.typeId


proc buildAddCompEvents(node: NimNode, id: EcsIdentity, context: var EventContext, c: ComponentBuildInfo) =
  if c.isOwned:
    node.invokeEvent(id, context, ekInit)
  
  node.invokeEvent(id, context, ekAdd)
  node.invokeEvent(id, context, ekAddCb)


proc addComponentEvents(id: EcsIdentity, entity: NimNode, details: var StateChangeDetails) =
  # Invoke component add events for details.passed.

  if not details.iterating.isNil:
    # We are processing a run time entity.
    # Since delete never calls add events, this means either 'construct' or 'clone'.
    assert details.passed.len > 0, "Internal error: there must be at least one component when iterating"
    let c = id.getInfo(details.passed[0])
    var context = newEventContext(entity, c, details.iterating)

    details.allEvents.buildAddCompEvents(id, context, c)

  else:
    # We know the components given to us at compile time.
    for c in id.building(details.passed):
      let fetchedIdent = details.compAccess(c, details.suffix)
      var context = newEventContext(entity, c, fetchedIdent)
      details.allEvents.buildAddCompEvents(id, context, c)


proc gateSystemActions(details: var StateChangeDetails, sys: SystemBuildInfo, actions: NimNode): NimNode =
  ## Perform `actions` when `sys` is available at run time.

  if not details.sysProcessed.isNil:
    # Constrain to one execution per system.

    let
      sysProcessed = details.sysProcessed
      thisSystem = ident sysEnum(sys.name)

    result = quote do:
      if `thisSystem` notin `sysProcessed`:
        `sysProcessed`.incl `thisSystem`
        `actions`
  
  else:
    result = actions


proc gateSystemUpdates(details: var StateChangeDetails, sys: SystemBuildInfo, sysUpdate: SystemUpdate): SystemUpdate =
  ## Build the update and event code for `sysUpdate`.
  
  result = newSystemUpdate()
  result.sysFetches = sysUpdate.sysFetches

  let
    sysFetch = sys.fetchedIdent details.suffix
  
  if sysUpdate.update.len > 0:
    let
      updateActions = sysUpdate.update
      updates = quote do:
        if `sysFetch`.found:
          `updateActions`
    
    result.update = details.gateSystemActions(sys, updates)

  if sysUpdate.events.len > 0:
    let
      eventActions = sysUpdate.events
      events = quote do:
        if `sysFetch`.found:
          `eventActions`

    result.events = details.gateSystemActions(sys, events)

  if sysUpdate.deferredEvents.len > 0:
    let
      eventActions = sysUpdate.deferredEvents
      events = quote do:
        if `sysFetch`.found:
          `eventActions`

    result.deferredEvents = details.gateSystemActions(sys, events)


proc addToSystem(id: EcsIdentity, entity: NimNode, details: var StateChangeDetails, change: SystemChange) =
  ## 'Add' state change for a system.

  assert change.kind == sckAdd

  if id.ecsEventEnv.len > 0:
    # This is an embedded event.

    if id.eventOccurred({ekRowAdded, ekRowAddedCB}, [change.sys.int]):
      error "A system add event is trying to invoke itself in system \"" &
        id.getSystemName(change.sys) & "\":\n" & id.eventMutationsStr

  if details.kind == scdkDelete:
    # Delete should not invoke add operations.
    # Note: this should never occur since delete uses remove state
    # changes explicitly.
    return

  if details.kind != scdkNewEntity:
    if change.fromNegation:
      # Adds invoked from negations need to check that the component is
      # present to be removed.
      details.compFetches.incl details.passedSet
    else:
      details.compFetches.excl details.passedSet
  
    details.compFetches.incl (change.checkIncl + change.checkExcl + change.checkInclOr)
  
  let
    sys = id.getInfo change.sys

    orderedReq = id.ecsSysRequirements sys.index

    (possible, sysItemValue, ownedStateUpdates) = id.buildSysItem(
      entity,
      sys,
      orderedReq,
      details.passed,
      details.values,
      details.suffix,
      details.compAccess
    )

  if possible:
    # This system can be added if conditions are met.

    if sys.isOwner:
      # Ensure the required components to complete the owner system are
      # present at run time.
      # The run time response for failing to satisfy the owner is given
      # by ECSErrorResponses.
      details.postFetches.add id.checkRequired(
        entity,
        sys.index,
        change.checkIncl,
        change.checkInclOr,
        change.checkExcl,
        details.suffix,
        details.compValid
      )

    # Append system updates by component set.
    let
      insertRow = genSym(nskVar, "row")
      entId = entity.newDotExpr ident"entityId"

    # Update system index.
    let
      idxFmt = id.indexFormat(sys.index)
      hasEntity = sys.variable.indexHasKey(entId, idxFmt)
      writeIndex = sys.variable.indexWrite(entId, insertRow, idxFmt)
      sysInt = sys.index.int

    var
      addCompGroup = details.componentGroups.mgetOrPut(
        ComponentGroup(
          required: change.checkIncl,
          requiredOr: change.checkInclOr,
          negated: change.checkExcl
        ),
        newSystemUpdate()
      )
      stateUpdate = newStmtList()
    
    if details.kind != scdkNewEntity:
      let
        dupMsg1 = newLit "Duplicate insert of entityId "
        dupMsg2 = newLit " for system \"" & sys.name & "\""
      
      stateUpdate.add(quote do:
        {.line.}:
          assert not(`hasEntity`), `dupMsg1` & $`entId`.int & `dupMsg2`
      )
    
    stateUpdate.add(quote do:
      var `insertRow`: int
    )
    stateUpdate.add id.assignSysItemGetRow(sys, sysItemValue, insertRow, id.storageFormat(sys.index))
    stateUpdate.add writeIndex

    # Record this mutation in the output code.
    if not defined(ecsPermissive):
      stateUpdate.add(quote do:
        static:
          recordMutation(`id`, ekRowAdded, [`sysInt`])
      )

    if ownedStateUpdates.len > 0:
      stateUpdate.add ownedStateUpdates
  
    # Gate updates to only be performed once.
    addCompGroup.update.add details.gateSystemActions(sys, stateUpdate)

    # Component-system events.

    let
      sysRow = sys.fetchedIdent(details.suffix).newDotExpr(ident "row")
      eventsProc = id.getSysProc("addEvents", sys.index)
    var
      addSystemGroup = details.systemGroups.mgetOrPut(
        sys.index,
        newSystemUpdate()
      )

    if not eventsProc.isNil:
      let call = newCall(eventsProc, entity)
      if change.fromNegation:
        addSystemGroup.procDeferredEvents.add call
      else:
        addSystemGroup.procEvents.add call

    let (events, used) =
      if eventsProc.isNil: id.buildAddSystemEvents(entity, sys, sysRow)
      else: (newStmtList(), false)
    
    if used:
      addSystemGroup.sysFetches.incl sys.index
      
      if change.fromNegation:
        # System events invoked from the negation of components must be
        # triggered after the system state has been resolved.
        # Normally remove operations invoke their events before system
        # state changes so that you can access the system being removed.
        # Within an add context, events are already invoked after system
        # state changes so there is no need to special case this.
        addSystemGroup.deferredEvents.add events
      else:
        addSystemGroup.events.add events

  else:
    # One or more owned components for this system were missing from
    # the passed components.

    if details.values.len > 0:
      # The user has provided components but not enough to create a row
      # in the system.
      let
        owned = id.ecsOwnedComponents(sys.index).toHashSet
        ownedPassed = owned.intersection details.passedSet
        ownedMissing = owned - details.passedSet
      
      if ownedPassed.len > 0:
        error "The owned components [" & id.commaSeparate(ownedPassed) & 
          "] must be passed with [" &
          id.commaSeparate(ownedMissing) &
          "] to satisfy the system owner \"" & sys.name & "\". Given: [" &
          id.commaSeparate(details.passed) & "]"
    
    else:
      # No new values means we cannot create owned components and owner
      # systems cannot participate here.
      discard


proc removeFromSystem(id: EcsIdentity, entity: NimNode, details: var StateChangeDetails, change: SystemChange) =
  ## 'Remove' state change for a system.

  assert change.kind == sckRemove

  if id.ecsEventEnv.len > 0:
    # This is an embedded event.

    if id.eventOccurred({ekRowRemoved, ekRowRemovedCb}, [change.sys.int]):
      # This state change would be recursive at compile time.
      error "A system remove event is trying to invoke itself in system \"" &
        id.getSystemName(change.sys) & "\":\n" & id.eventMutationsStr

  let
    sys = id.getInfo change.sys

  var
    removeSystemRow = details.systemGroups.mgetOrPut(
      sys.index,
      newSystemUpdate()
    )
  
  if sys.isOwner:
    # Removing a row from an owner system removes all of that system's
    # owned components from the entity.
    for c in id.ecsOwnedComponents(sys.index):
      details.compRemoves.incl c

  let
    entId = newDotExpr(entity, ident "entityId")
    sysFetch = sys.fetchedIdent details.suffix
    row = sysFetch.newDotExpr ident"row"
    sysInt = sys.index.int
    removeRowProc = id.getSysProc("removeRow", sys.index)
    eventsProc = id.getSysProc("removeEvents", sys.index)

  if removeRowProc.isNil:
    removeSystemRow.sysFetches.incl sys.index
    removeSystemRow.update.add id.unregister(sys.index, sys.variable, row, entId)
  else:
    removeSystemRow.procUpdate.add newCall(removeRowProc, entity)
  
  # Record this mutation in the output code.
  if not defined(ecsPermissive):
    let recordMut = quote do:
      static:
        recordMutation(`id`, ekRowRemoved, [`sysInt`])
    if removeRowProc.isNil: removeSystemRow.update.add recordMut
    else: removeSystemRow.procUpdate.add recordMut

  # Events

  for c in id.building(id.ecsSysRequirements sys.index):
    # Extend to remove dependent owned components.
    for depComp in id.dependentComps(c.typeId):
      if depComp notin details.passedSet:
        details.compFetches.incl depComp  # For events.

  if not eventsProc.isNil:
    removeSystemRow.procEvents.add newCall(eventsProc, entity)
  else:
    let (sysEvents, used) = id.buildRemoveSystemEvents(entity, sys, row)
    if used:
      removeSystemRow.sysFetches.incl sys.index
      removeSystemRow.events.add sysEvents


proc applyChange*(id: EcsIdentity, entity: NimNode, details: var StateChangeDetails, change: SystemChange) =
  case change.kind
    of sckAdd:
      id.addToSystem(entity, details, change)

    of sckRemove:
      id.removeFromSystem(entity, details, change)


proc doSysUpdate(id: EcsIdentity, entity: NimNode, sysUpdate: SystemUpdate, guard: NimNode, details: var StateChangeDetails) =
  ## Generate code that removes this entity from relevant systems.
  ## 
  ## Removal code is gated by 'guard' checks to ensure the entity is a
  ## member of the system.
  var
    updateRows = sysUpdate.update
  
  if sysUpdate.sysFetches.len > 0:
    var
      systemFetches = newStmtList()

    systemFetches.buildFetchSystems(id, entity, sysUpdate.sysFetches, details.suffix)

    # Duplicate the system fetch operation for events if required.
    
    if updateRows.len > 0:
      var update = newStmtList()
      update.add systemFetches.copy
      update.add maybeIf(guard, updateRows)
      details.systemUpdates.add update

    # System events for this group.
    if sysUpdate.events.len > 0:
      var events = newStmtList()
      events.add systemFetches.copy
      events.add sysUpdate.events
      details.allEvents.add newBlockStmt(maybeIf(guard, events))

    if sysUpdate.deferredEvents.len > 0:
      var events = newStmtList()
      events.add systemFetches.copy
      events.add sysUpdate.deferredEvents
      details.deferredEvents.add newBlockStmt(maybeIf(guard, events))

  else:
    details.systemUpdates.add maybeIf(guard, updateRows)

    if sysUpdate.events.len > 0:
      # System events for this group.
      details.allEvents.add maybeIf(guard, sysUpdate.events)

    if sysUpdate.deferredEvents.len > 0:
      details.deferredEvents.add maybeIf(guard, sysUpdate.deferredEvents)


proc buildSystemUpdates(id: EcsIdentity, entity: NimNode, details: var StateChangeDetails) =
  ## Build modifications to systems.
  ## Expects `details` to be fully populated.

  # Actions depending on component presence.
  for group, sysUpdate in details.componentGroups:
    let
      guard = id.buildSysCheck(
        group.required,
        group.requiredOr,
        group.negated,
        details.suffix,
        details.compValid)

    id.doSysUpdate(
      entity,
      sysUpdate,
      guard,
      details
    )

  # Actions depending on system presence.
  for sys, sysUpdate in details.systemGroups:
    let
      info = id.getInfo sys
      updateSystem = details.gateSystemUpdates(info, sysUpdate)
    
    id.doSysUpdate(
      entity,
      updateSystem,
      nil,
      details
    )

    # Calls to shared procs, which check the system themselves.
    if sysUpdate.procUpdate.len > 0:
      details.systemUpdates.add details.gateSystemActions(info, sysUpdate.procUpdate)
    if sysUpdate.procEvents.len > 0:
      details.allEvents.add details.gateSystemActions(info, sysUpdate.procEvents)
    if sysUpdate.procDeferredEvents.len > 0:
      details.deferredEvents.add details.gateSystemActions(info, sysUpdate.procDeferredEvents)


proc buildStateChange*(id: EcsIdentity, entity: NimNode, details: var StateChangeDetails) =
  ## Build the current state change operation within `details`.

  case details.kind
    of scdkNewEntity, scdkConstruct, scdkClone, scdkAdd:
      id.createComponents(entity, details)
      id.addComponentEvents(entity, details)

    of scdkRemove, scdkDelete:
      id.removeComponentEvents(entity, details)

  details.fetches.buildFetchComponents(
    id,
    entity,
    details.compFetches - details.newComps,
    details.suffix,
    earlyExit = true,
    details.compAccess
  )
  
  details.fetches.add details.postFetches

  id.buildSystemUpdates(entity, details)

