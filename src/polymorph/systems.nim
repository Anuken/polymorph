# SPDX-License-Identifier: Apache-2.0

# Copyright (c) 2020 Ryan Lipscombe
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

import macros, strutils, strformat, sequtils, times, sharedtypes,
  private/[ecsstatedb, utils, debugging], tables
from private/eventutils import userEntAccess
from std/cpuinfo import countProcessors
import random


proc indexInit(sysNode: NimNode, options: ECSSysOptions): NimNode =
  let
    initTab = bindSym "initTable"

  case options.indexFormat
    of sifTable:
      quote do:
        `sysNode`.index = `initTab`[EntityId, int]() 
    of sifArray:
      newStmtList()
    of sifAllocatedSeq:
      # Requires + 1 for array as 0 is invalid.
      let initSize = newIntLitNode(options.maxEntities + 1)
      quote do:
        `sysNode`.index = newSeq[tuple[exists: bool, row: Natural]](`initSize`)


# -------------------------------------
# Processing system component arguments
# -------------------------------------


type
  UnpackedPrefixKind = enum upNone = "", upNot = "not", upOwn = "own", upCustom
  
  UnpackedPrefix = object
    kind: UnpackedPrefixKind
    custom: NimNode
  
  UnpackedArg = object
    typeName: string
    typeId: ComponentTypeId
    prefix: UnpackedPrefix


proc unpackComponentArg(id: EcsIdentity, node: NimNode): UnpackedArg =
  ## Parse a system requirement of the form '<Type>|<prefix> <Type>'.
  ## The prefixes `not` and `own` have special semantics.

  const
    sysPre = "System components "

  result =
    case node.kind
      
      of nnkIdent, nnkSym:
        UnpackedArg(
          typeName: node.strVal,
          typeId: id.typeStringToId node.strVal,
          prefix: UnpackedPrefix(kind: upNone)
        )
      
      of nnkPrefix:

        node.expectMinLen 2

        var
          prefixOp: string

        case node[0].kind
          of nnkIdent, nnkSym:
            prefixOp = node[0].strVal
          of nnkOpenSymChoice, nnkClosedSymChoice:
            node[0].expectMinLen 1
            prefixOp = node[0][0].strVal
          else:
            error sysPre & "expected an ident or symbol as a type prefix but got " & $node.kind & ":\n'" & node.treerepr & "'"
        
        if prefixOp != "not":
          error sysPre & "unknown type prefix '" & node[0].strVal & "'"

        UnpackedArg(
          typeName: node[1].strVal,
          typeId: id.typeStringToId node[1].strVal,
          prefix: UnpackedPrefix(kind: upNot)
        )

      of nnkCommand:
        if node[1].kind notin [nnkIdent, nnkSym]:
          error sysPre & "expected a type ident to own but got " & $node[1].kind & ": '" & node[1].repr & "'"
        
        UnpackedArg(
          typeName: node[1].strVal,
          typeId: id.typeStringToId node[1].strVal,
          prefix:
            case node[0].strVal
              of "own": UnpackedPrefix(kind: upOwn)
              else:     UnpackedPrefix(kind: upCustom, custom: copy node[0])
        )

      else:
        error sysPre & "expected 'type' or 'not type' but got " &
          $node.kind & ": '" & node.repr & "'"
        
        UnpackedArg(
          typeName: "",
          typeId: InvalidComponent,
          prefix: UnpackedPrefix(kind: upNone)
        )


proc unpackArgs(id: EcsIdentity, componentTypes: NimNode): tuple[uArgs: seq[UnpackedArg], names: string] =
  ## Parse `componentTypes` to UnpackedArg.

  # TODO: `repr` might give mangled type names when creating a private ECS inside a block.
  
  result.uArgs.setLen componentTypes.len

  for i in 0 ..< componentTypes.len:
    let
      uArg = id.unpackComponentArg(componentTypes[i])
      tName =
        case uArg.prefix.kind
          of upNone: uArg.typeName
          of upNot, upOwn: $uArg.prefix.kind & " " & uArg.typeName
          of upCustom: uArg.prefix.custom.repr & " " & uArg.typeName
    
    result.uArgs[i] = uArg

    if uArg.typeName.len == 0:
      error "Cannot resolve type from " & componentTypes[i].repr

    if result.names.len > 0:
      result.names &= ", " & tName
    else:
      result.names = tName


# ---------------------
# Creating system types
# ---------------------

proc threadParamType(sysType: NimNode): NimNode =
  let
    sys = ident "sys"
    rows = ident "rows"
    r1 = ident "r1"
    r2 = ident "r2"
  quote do:
    tuple[`sys`: ptr `sysType`, `rows`: tuple[`r1`, `r2`: int]]


proc makeSystemType(id: EcsIdentity, sysIndex: SystemIndex, extraFields: seq[NimNode]): NimNode =
  ## Generates the type declaration for this system.
  let
    name = id.getSystemName sysIndex
    sysTypeName = systemTypeName(name)
    sysIdent = ident sysTypeName
    itemTypeIdent = ident(itemTypeName(name))
    options = id.getOptions(sysIndex)
  result = newStmtList()

  # Generate the type for this system
  result.add(quote do:
    type
      `sysIdent`* = object
        id*: SystemIndex
        lastIndex*: int           ## Records the last item position processed for streaming.
        streamRate*: Natural      ## Rate at which this system streams items by default, overridden if defined using `stream x:`.
        # TODO: Currently writable, use sys.name to get a generated constant by system type.
        systemName*: string       ## Name is automatically set up at code construction in defineSystem.
        disabled*: bool           ## Doesn't run doProc if true, no work is done.
        paused*: bool             ## Pauses this system's entity processing, but still runs init & finish. 
        initialised*: bool        ## Automatically set to true after an `init` body is called.
        deleteList*: seq[EntityRef] ## Anything added to this list is deleted after the `finish` block. This avoids affecting the main loop when iterating.
  )

  var
    # Extract field list so we can edit them.
    fields = result.recList(sysTypeName)
    highIdx, count: NimNode

  doAssert fields.kind != nnkEmpty, "Internal error: Cannot retrieve fields from system type `" & name & "`"

  # Create requirements array
  let
    reqCount = id.len_ecsSysRequirements(sysIndex)
  
  fields.add genField("requirements", false, genArray(reqCount, ident "ComponentTypeId"))

  # Append groups field to the system type.
  case options.storageFormat

    of ssSeq:
      fields.add genField("groups", true, genSeq(itemTypeIdent))
      
      highIdx = quote do:
        template high*(system: `sysIdent`): int = system.groups.high
      count = quote do:
        template count*(system: `sysIdent`): int = system.groups.len

    of ssArray:
      let
        maxEntities = options.maxEntities
      
      fields.add genField("groups", true, genArray(maxEntities + 1, itemTypeIdent))
      # TODO: Make nextFreeIdx private. This is exposed due to `newEntityWith` not building a proc, so needs internal access.
      fields.add genField("nextFreeIdx", true, ident "int")
      
      highIdx = quote do:
        template high*(system: `sysIdent`): int = system.nextFreeIdx - 1
      count = quote do:
        template count*(system: `sysIdent`): int = system.nextFreeIdx

  # Define the `index` field, used to translate from entityId to the groups row. 
  case options.indexFormat

    of sifTable:
      fields.add genField("index", true, genTable(ident "EntityId", ident "int"))

    of sifArray:
      let existsTuple = quote: tuple[exists: bool, row: Natural]
      # Requires + 1 for array as 0 is invalid.
      fields.add genField("index", true, genArray(options.maxEntities + 1, existsTuple))

    of sifAllocatedSeq:
      let existsTuple = quote: tuple[exists: bool, row: Natural]
      fields.add genField("index", true, genSeq(existsTuple))

  # Add fields to support timing the system.

  if options.timings == stProfiling:
    # Time to run one tick's worth of items based on past performance
    fields.add genField("timePerGroupRun", true, ident "float")
    # Calculate time taken to perform one row item based on past performance
    fields.add genField("timePerGroupItem", true, ident "float")
    fields.add genField("minTimePerGroupItem", true, ident "float")
    fields.add genField("maxTimePerGroupItem", true, ident "float")
    fields.add genField("minTimePerGroupRun", true, ident "float")
    fields.add genField("maxTimePerGroupRun", true, ident "float")
  
  case options.threading:
    of sthNone:
      discard
    of sthDistribute:
      let
        paramTy = threadParamType(sysIdent)
      fields.add genField("threads", true, quote do: seq[Thread[`paramTy`]])
      fields.add genField("cores", true, ident "int")

  
  if options.timings in [stRunEvery, stProfiling]:
    # Keeps track of the last time a tick was issued
    fields.add genField("lastRun", true, ident "float")
    # In theory, inputting a negative curTime() + x in runEvery would allow no trigger until x
    # had passed, then act as if runEvery is zero (ie; always run)
    ## If runEvery is non-zero, this system's do proc will only trigger after this delay
    fields.add genField("runEvery", true, ident "float")

  # Finally, add extra fields (provided by the user) to the type.
  
  if extraFields.len > 0:
    fields.add(extraFields)

  result.add(quote do:
    `highIdx`
    `count`
  )


proc instantiateSystem(id: EcsIdentity, sysIndex: SystemIndex, sysName: string, fieldSetup: seq[tuple[fieldName, value: NimNode]]): NimNode =
  ## Generates an init proc that instantiates the system and system variable, and assigns any user default values.
  let
    typeName = ($sysName).capitalizeAscii
    sysType = ident systemTypeName(typeName)
    initParam = ident "value"
    initIdent = ident systemInitName(sysName)
    options = id.getOptions(sysIndex)
    initIndex = initParam.indexInit(options)
    sysTypeName = systemTypeName(sysName)
    sysIdent = ident sysTypeName

  result = newStmtList()
  var fieldInits = newStmtList()

  for setupState in fieldSetup:
    # `value.myVar = myValue`.
    fieldInits.add newAssignment(newDotExpr(initParam, setupState.fieldName), setupState.value)

  # Build this system's requirements array for assignment in init.
  var reqsConst = nnkBracket.newTree()
  for i, req in id.ecsSysRequirements(sysIndex):
    reqsConst.add newDotExpr(newLit req.int, ident "ComponentTypeId")

  # Create variable for this system.
  let
    sysVar = ident systemVarName(typeName)
    typeIdent = ident itemTypeName(typeName)
    systemVarDecl =
      if options.useThreadVar:
        quote:
          var `sysVar`* {.threadVar.}: `sysIdent`
      else:
        quote:
          var `sysVar`*: `sysIdent`

  let docCmt = newCommentStmtNode "Returns the type of 'item' for the " & sysName & " system."
  result.add(quote do:
    `systemVarDecl`
    `docCmt`
    template itemType*(system: `sysType`): untyped = `typeIdent`
  )

  # Add timing utilities for this system.
  let timingsProcs =
    if options.timings == stProfiling:
      quote do:
        proc timePerItem*(sys: `sysIdent`): float {.inline.} = sys.timePerGroupItem
        proc minTimePerItem*(sys: `sysIdent`): float {.inline.} = sys.minTimePerGroupItem
        proc maxTimePerItem*(sys: `sysIdent`): float {.inline.} = sys.maxTimePerGroupItem
        proc minTimePerRun*(sys: `sysIdent`): float {.inline.} = sys.minTimePerGroupRun
        proc maxTimePerRun*(sys: `sysIdent`): float {.inline.} = sys.maxTimePerGroupRun
        proc resetMinMax*(sys: var `sysIdent`) {.inline.} =
          sys.minTimePerGroupItem = 0.0
          sys.maxTimePerGroupItem = 0.0
          sys.minTimePerGroupRun = 0.0
          sys.maxTimePerGroupRun = 0.0
        proc timePerRun*(sys: `sysIdent`): float {.inline.} = sys.timePerGroupRun
    else: newStmtList()
  
  let threadInits =
    case options.threading
      of sthNone: newStmtList()
      of sthDistribute:
        let countCores = bindSym("countProcessors")
        quote do:
          `initParam`.cores = `countCores`()
          `initParam`.threads.setLen `initParam`.cores          

  let
    entity = ident "entity"
    sysHasEntity = sysVar.indexHasKey(quote do: `entity`.entityId, options.indexFormat)

  result.add(quote do:

    proc `initIdent`*(`initParam`: var `sysIdent`) =
      ## Initialise the system.

      template sys: untyped {.used.} = `initParam`  ## The `sys` template represents the system variable being passed.
      template self: untyped {.used.} = `initParam` ## The `self` template represents the system variable being passed.

      `initIndex`
      `initParam`.streamRate = 1  # Default items to process per frame when using `stream:`.
      `initParam`.requirements = `reqsConst`
      `initParam`.systemName = `sysName`
      `fieldInits`
      `threadInits`
      sys.id = `sysIndex`.SystemIndex

    `timingsProcs`

    func name*(sys: `sysIdent`): string = `sysName`
    
    # Call init proc to set up the system's variable.
    # Initialising in-place guarantees no copies.
    `sysVar`.`initIdent`()

    proc contains*(sys: `sysIdent`, `entity`: EntityRef): bool =
      `sysHasEntity`  
  )

proc processPragma(identNode, valueType: NimNode): tuple[ident: NimNode, def: NimNode] =
  ## Process and remove `public` pragma if present.
  identNode[1].expectKind nnkPragma
  for pIdx in countDown(identNode[1].len - 1, 0):
    if identNode[1][pIdx].kind == nnkIdent:
      let pragmaStr = identNode[1][pIdx].strVal

      if pragmaStr == "public" or pragmaStr == "pub":
        identNode[1].del(pIdx)
        # Mark as exported.
        identNode[0] = postFix(identNode[0], "*")
        break

  var a, b: NimNode

  if identNode[0].len > 1:
    a = identNode[0][1]
  else:
    a = identNode[0]

  if identNode[1].len == 0:
    # Public was the only pragma so remove the pragma tree entirely.
    b = newIdentDefs(identNode[0], valueType)
  else:
    b = newIdentDefs(identNode, valueType)
  (a, b)


proc parsePublicPragma(identNode, valueType: NimNode): (NimNode, NimNode) =
  ## Parse the ident node for an ident def and if it finds a {.public.}
  ## annotation, postfix the ident with `*` so the field is exported.
  ## This is necessary because `ident*` is invalid syntax in an
  ## untyped block.
  case identNode.kind
    of nnkPragmaExpr:
      # Strip out public pragma (but keep others).
      identNode.processPragma(valueType)
    of nnkInfix:
      if identNode.len >= 1:
        if identNode[1].kind == nnkPragmaExpr:
          identNode[1].processPragma(valueType)
        else:
          (identNode[1], newIdentDefs(identNode[1], valueType))
      else:
        (identNode, newIdentDefs(identNode, valueType))
    else:
      (identNode, newIdentDefs(identNode, valueType))


proc matchesTypeProvided(node: NimNode): bool =
  ## Tests to see if we're doing `field -> type`.
  node.kind == nnkInfix and node[0].kind == nnkIdent and node[0].strVal == "->"


proc makeSystemItemType(node: var NimNode, id: EcsIdentity, sysName: string, sysIndex: SystemIndex, components, owned: ComponentIterable) =
  ## Build the 'item' type that contains fields for the entity and each component accessible by this system.

  var
    elements = nnkRecList.newTree()
  
  # Add the 'entity' field.
  elements.add(
    nnkIdentDefs.newTree(
      nnkPragmaExpr.newTree(
        postFix(ident("entity"), "*"),
        nnkPragma.newTree(
          ident "hostEntity"
        )
      ),
      ident("EntityRef"),
      newEmptyNode())
    )
  
  # Add components to the field list.
  for c in id.building components:
    let
      typeId = c.typeId
      tyName = c.name

    if typeId in owned:
      # Owned component storage is the system itself.

      id.set_systemOwner typeId, sysIndex
      id.set_isOwned typeId, true
      
      elements.add(
        nnkIdentDefs.newTree(
          postfix(ident(c.lcName), "*"),
          ident(tyName),
          newEmptyNode()
        )
      )

    else:
      # If not owned the component instance type is used.
      
      elements.add(
        nnkIdentDefs.newTree(
          postfix(ident(c.lcName), "*"),
          c.instanceTy,
          newEmptyNode()
        )
      )

  node.add nnkTypeSection.newTree(
    nnkTypeDef.newTree(
      postfix(ident itemTypeName(sysName), "*"),
      newEmptyNode(),
      nnkObjectTy.newTree(
        newEmptyNode(),
        newEmptyNode(),
        elements
      )
    )
  )


proc createSystem(id: EcsIdentity, sysName: string, componentTypes: NimNode, extraFields: NimNode, sysOptions: ECSSysOptions): NimNode =
  ## Create a system type then init an instance.
  
  result = newStmtList()

  if id.findSystemIndex(sysName).found:
    error "System \"" & sysName & "\" has already been defined"
  
  if sysOptions.indexFormat in [sifArray, sifAllocatedSeq] and sysOptions.maxEntities == 0:
    error "System \"" & sysName & "\", system options: maxEntities cannot be zero when using the fixed size option '" &
      $sysOptions.indexFormat & "'"

  if sysOptions.storageFormat in [ssArray] and sysOptions.maxEntities == 0:
    error "System \"" & sysName & "\", system options: maxEntities cannot be zero when using the fixed size option '" &
      $sysOptions.storageFormat & "'"

  var
    passedComponentIds: seq[ComponentTypeId]
    passedNegationIds: seq[ComponentTypeId]
    ownedComponentIds: seq[ComponentTypeId]
  let
    (uArgs, componentTypesStr) = id.unpackArgs(componentTypes)

  for uArg in uArgs:
    let
      typeId = uArg.typeId
      typeName = id.typeName(typeId)
      errPre = "Component '" & typeName & "' cannot be "
      errPost = " multiple times for system \"" & sysName & "\""

    if typeId in id.ecsSealedComponents:
      error "Component " & typeName &
        " has already been sealed with makeEcs and cannot be extended to system \"" & sysName &
        "\". Use 'defineSystem' to forward declare the system or place this 'makeSystem' before 'makeEcs'."

    case uArg.prefix.kind:
      of upNone:
        if typeId in passedComponentIds:
          error errPre & "included" & errPost

        passedComponentIds.add typeId

      of upNot:
        if typeId in passedNegationIds:
          error errPre & "negated" & errPost

        passedNegationIds.add typeId

      of upOwn:
        if typeId in ownedComponentIds:
          error errPre & "owned" & errPost
        
        if typeId notin passedComponentIds:
          # Allow [A, own A].
          passedComponentIds.add typeId
        
        ownedComponentIds.add typeId

      of upCustom:
        error errPre & "cannot process a type modifier of '" & uArg.prefix.custom.repr & "'"

  when defined(ecsLog) or defined(ecsLogDetails):
    echo "Defining body for system \"", sysName, "\" with types [", componentTypesStr, "]"

  for typeId in passedComponentIds:
    let
      curOwner = id.systemOwner typeId

    if curOwner != InvalidSystemIndex and typeId in ownedComponentIds:
      error "Component " & id.typeName(typeId) & " is already owned by system \"" & id.getSystemName(curOwner) & "\""
    
    if typeId in passedNegationIds:
      error "Component " & id.typeName(typeId) & " cannot be used and negated in the same system \"" & sysName & "\""

  # Conditions have now been met to add the system.

  let sourceLoc = componentTypes.lineInfo

  when defined(ecsLog) or defined(ecsLogDetails):

    echo "[ System generation for \"" & sysName & "\" " & sourceLoc & " ]"

  when defined(ecsLogDetails):
    echo "System \"", sysName, "\" options:\n", sysOptions.repr, "\n"

  let typeName = ($sysName).capitalizeAscii
  # Create the node for the variable for this system.
  let inst = ident(systemVarName(typeName))

  # Create a new system index.
  let
    sysIndex = id.addSystem sysName

  id.set_ecsSystemSourceLoc(sysIndex, sourceLoc)

  id.setOptions(sysIndex, sysOptions)

  # Store variable ident for this system.
  id.set_Instantiation(sysIndex, inst)

  # Append to the commitSystems order.
  id.add_systemOrder sysIndex

  assert id.len_ecsOwnedComponents(sysIndex) == 0, "Internal error: owned components have already been initialised"

  # Add this system's requirements to the macrocache.

  for compId in ownedComponentIds:
    id.add_ecsOwnedComponents sysIndex, compId

  for compId in passedNegationIds:
    id.add_ecsSysNegations sysIndex, compId
    id.add_systems compId, sysIndex

  for compId in passedComponentIds:
    id.add_ecsSysRequirements sysIndex, compId
    id.add_systems compId, sysIndex

  # Create a type to hold components for a system row.
  result.makeSystemItemType(id, sysName, sysIndex, passedComponentIds, ownedComponentIds)

  # Add user defined fields to this System's type.
  # These can be defined as `Field: Value`, `Field = Value`, or `Field -> Type = Value`.
  var
    fieldSetup: seq[tuple[fieldName, value: NimNode]]
    extraFieldDefs: seq[NimNode]

  if extraFields.kind != nnkEmpty:
    
    # Store extra fields for this system.
    # This allows checking later `fields:` components match the original
    # definition.
    id.set_extraFields(sysIndex, extraFields)

    for tyDef in extraFields:
      case tyDef.kind
        of nnkCall:
          # Already in the right format.
          tyDef[1].expectKind nnkStmtList
          tyDef[1].expectMinLen 1
          let
            valueType = tyDef[1][0]
            (_, identDef) = parsePublicPragma(tyDef[0], valueType)

          extraFieldDefs.add(identDef)
    
        of nnkAsgn:
          # Because it's invalid syntax to use `field: type = statement`
          # you can manually set the type using `field -> type = statement`
          # Otherwise, use `field: type` and set it up with `init:` in the system.
          var valueType: NimNode
          let value = tyDef[1]
          if tyDef[0].matchesTypeProvided:
            # Pull out user's type request.
            valueType = tyDef[0][2]
          else:
            # Try and work out what type we have.
            valueType = value.assignmentType
          let (ident, identDef) = parsePublicPragma(tyDef[0], valueType)

          # Add assignment to the init procedure.
          fieldSetup.add (ident, value)
          # Record the field def too.
          extraFieldDefs.add(identDef)
        else:
          error "Unhandled kind for extra field in system \"" & sysName &
            "\", expected `field: type` or `field = value`, got:\n" & tyDef.treeRepr

  # Generate the system type according to provided options.
  result.add makeSystemType(id, sysIndex, extraFieldDefs)
  result.add instantiateSystem(id, sysIndex, sysName, fieldSetup)

  # User access to system ownership.
  let sysType = ident systemTypeName(sysName)
  if ownedComponentIds.len > 0:
    var
      ownedComponents = nnkBracket.newTree()
    
    for c in ownedComponentIds:
      ownedComponents.add ident(id.typeName c)

    result.add(quote do:
      template isOwner*(sys: `sysType`): bool = true
      template ownedComponents*(sys: `sysType`): seq[ComponentTypeId] = `ownedComponents`
      )
  else:
    result.add(quote do:
      template isOwner*(sys: `sysType`): bool = false
      template ownedComponents*(sys: `sysType`): seq[ComponentTypeId] = []
      )

  id.add_ecsSysDefined sysIndex

  if id.private:
    result.deExport

  genLog "\n# System \"" & sysName & "\":\n" & result.repr


proc embedOwned(componentTypes, ownedComponents: NimNode): NimNode =
  result = componentTypes.copy
  for n in ownedComponents:
    result.add nnkCommand.newTree(ident "own", n)


# -----------------
# Public system API
# -----------------


macro defineSystemOwner*(id: static[EcsIdentity], name: static[string], componentTypes: untyped, ownedComponents: openarray[typedesc], options: static[ECSSysOptions], extraFields: untyped): untyped =
  ## Define a system using an ECS identity, declaring types that are owned by this system and providing extra fields.
  result = id.createSystem(name, componentTypes.embedOwned ownedComponents, extraFields, options)

macro defineSystemOwner*(id: static[EcsIdentity], name: static[string], componentTypes: untyped, ownedComponents: openarray[typedesc], options: static[ECSSysOptions]): untyped =
  ## Define a system using an ECS identity, declaring types that are owned by this system.
  result = id.createSystem(name, componentTypes.embedOwned ownedComponents, nil, options)

macro defineSystem*(id: static[EcsIdentity], name: static[string], componentTypes: untyped, options: static[ECSSysOptions], extraFields: untyped): untyped =
  ## Define a system and its types using an ECS identity, providing extra fields to incorporate into the resultant system instance.
  result = id.createSystem(name, componentTypes, extraFields, options)

template defineSystem*(id: static[EcsIdentity], name: static[string], componentTypes: untyped, options: static[ECSSysOptions]): untyped =
  ## Define a system and its types using an ECS identity with specific options.
  defineSystem(id, name, componentTypes, options, nil)

template defineSystem*(id: static[EcsIdentity], name: static[string], componentTypes: untyped): untyped =
  ## Define a system and its types using an ECS identity with default system options.
  defineSystem(id, name, componentTypes, defaultSystemOptions, nil)

template defineSystem*(id: static[EcsIdentity], name: static[string]): untyped =
  ## Define a system without components using an ECS identity with default system options.
  defineSystem(id, name, nil, defaultSystemOptions, nil)


#---------------------------------------------------
# Convenience templates for using a default identity
#---------------------------------------------------


template defineSystem*(name: static[string], componentTypes: untyped, options: static[ECSSysOptions], extraFields: untyped): untyped =
  ## Define a system and its types using the default ECS identity, providing extra fields to incorporate into the resultant system instance.
  defaultIdentity.defineSystem(name, componentTypes, options, extraFields)

template defineSystem*(name: static[string], componentTypes: untyped, options: static[ECSSysOptions]): untyped =
  ## Define a system and its types using the default ECS identity with specific options.
  defaultIdentity.defineSystem(name, componentTypes, options)

template defineSystem*(name: static[string], componentTypes: untyped): untyped =
  ## Define a system and its types using the default ECS identity with default system options.
  defaultIdentity.defineSystem(name, componentTypes)

template defineSystem*(name: static[string]): untyped =
  ## Define a system and its types using the default ECS identity with default system options.
  defaultIdentity.defineSystem(name, nil)

template defineSystemOwner*(name: static[string], componentTypes: untyped, ownedComponents: untyped, options: static[ECSSysOptions], extraFields: untyped): untyped =
  ## Define a system using the default ECS identity, declaring types that are owned by this system and providing extra fields.
  defaultIdentity.defineSystemOwner(name, componentTypes, ownedComponents, options, extraFields)

template defineSystemOwner*(name: static[string], componentTypes: untyped, ownedComponents: untyped, options: static[ECSSysOptions]): untyped =
  ## Define a system using the default ECS identity, declaring types that are owned by this system and providing extra fields.
  defaultIdentity.defineSystemOwner(name, componentTypes, ownedComponents, options)

template defineSystem*(name: static[string]): untyped =
  ## Define a system without components using the default ECS identity with default system options.
  defaultIdentity.defineSystem(name, nil, defaultSystemOptions, nil)


# ----------------
# Grouping systems
# ----------------


macro defineGroup*(id: static[EcsIdentity], group: static[string], systems: openarray[string]): untyped =
  ## Assign specific systems to a group using an ECS identity.
  ## 
  ## These systems will not be output as part of `commitSystems` and must be output with `commitGroup`.
  ## 
  ## Systems may be part of multiple groups.
  let
    lcGroup = group.toLowerAscii

  for systemName in systems:
    let
      nameStr = systemName.strVal
      lookupSys = findSystemIndex(id, nameStr)

    if lookupSys.found:
      let
        sys = lookupSys.index

      # Add to list of systems for this group.
      if sys notin id.groupSystems(lcGroup):
        id.add_groupSystems(lcGroup, sys)

      # Add the group to this system.
      if lcGroup notin id.systemGroups(sys):
        id.add_systemGroups(sys, lcGroup)

    else:
      error "Cannot find system \"" & nameStr & "\""

template defineGroup*(group: static[string], systems: openarray[string]): untyped =
  ## Assign specific systems to a group using the default ECS identity.
  ## 
  ## These systems will not be output as part of `commitSystems` and must be output with `commitGroup`.
  ## 
  ## Systems may be part of multiple groups.
  defaultIdentity.defineGroup(group, systems)

macro defineGroup*(id: static[EcsIdentity], group: static[string]): untyped =
  ## Assign previously defined and ungrouped systems to a group using an ECS identity.
  ## 
  ## These systems will not be output as part of `commitSystems` and must be output with `commitGroup`.
  ## 
  ## Systems may be part of multiple groups.
  var
    order = id.systemOrder()
  let
    lcGroup = group.toLowerAscii

  for sys in order:
    # Ignore systems that already belong to groups.
    if id.systemGroups(sys).len == 0:

      # Add to list of systems for this group.
      if sys notin id.groupSystems(lcGroup):
        id.add_groupSystems(lcGroup, sys)

      # Add the group to this system.
      if lcGroup notin id.systemGroups(sys):
        id.add_systemGroups(sys, lcGroup)

template defineGroup*(group: static[string]): untyped =
  ## Assign previously defined and ungrouped systems to a group using the default ECS identity.
  ## 
  ## These systems will not be output as part of `commitSystems` and must be output with `commitGroup`.
  ## 
  ## Systems may be part of multiple groups.
  defaultIdentity.defineGroup(group)

macro commitGroup*(id: static[EcsIdentity], group, runProc: static[string]): untyped =
  ## Output uncommitted system definitions for a group using an ECS identity and wrap in an execution procedure.
  ## 
  ## The order of execution matches the order these systems have been defined.
  ## 
  ## It is a compile time error to commit groups with no systems or that contain systems with no body.
  result = newStmtList()

  let
    systems = id.groupSystems(group.toLowerAscii)

  if systems.len == 0:
    error "No system bodies defined for group \"" & group & "\""
  else:
    result.add id.commitSystemList(systems, runProc)
  
  if id.private:
    result.deExport

template commitGroup*(group, runProc: static[string]): untyped =
  ## Output uncommitted system definitions for a group using the default ECS identity and wrap in an execution procedure.
  ## 
  ## The order of execution matches the order these systems have been defined.
  ## 
  ## It is a compile time error to commit groups with no systems or that contain systems with no body.
  defaultIdentity.commitGroup(group, runProc)


#----------------------
# User system utilities
#----------------------


template updateTimings*(sys: untyped): untyped =
  # per item
  # max
  if sys.timePerGroupItem > sys.maxTimePerGroupItem:
    sys.maxTimePerGroupItem = sys.timePerGroupItem
  # min
  if sys.minTimePerGroupItem <= 0.0: 
    sys.minTimePerGroupItem = sys.timePerGroupItem
  else:
    if sys.timePerGroupItem < sys.minTimePerGroupItem:
      sys.minTimePerGroupItem = sys.timePerGroupItem
  # per run
  # max
  if sys.timePerGroupRun > sys.maxTimePerGroupRun:
    sys.maxTimePerGroupRun = sys.timePerGroupRun
  # min
  if sys.minTimePerGroupRun <= 0.0: 
    sys.minTimePerGroupRun = sys.timePerGroupRun
  else:
    if sys.timePerGroupRun < sys.minTimePerGroupRun:
      sys.minTimePerGroupRun = sys.timePerGroupRun

macro removeComponents*(sys: object, types: varargs[typed]) =
  ## Remove the components in `types` from all entities in this system.
  
  # This macro builds a `removeComponents` with `types` and executes it
  # for each entity in the system, from the last entity backwards to the
  # first.
  # Note that removing a required component implicitly adjust the system
  # length so we don't need to manually set the 'groups' field length.

  let entity = ident "entity"
  var `removeInner` = nnkCall.newTree(ident "remove", entity)
  
  for ty in types:
    
    case ty.kind

      of nnkSym:
        `removeInner`.add ty
      
      of nnkHiddenStdConv:
        ty.expectMinLen 2
        ty[1].expectKind nnkBracket
        
        for compTy in ty[1]:
          `removeInner`.add compTy
      
      else:
        `removeInner`.add ty

  quote do:
    for i in countDown(`sys`.count - 1, 0):
      let `entity` = `sys`.groups[i].entity
      `removeInner`

template remove*(sys: object, types: varargs[typed]) =
  ## Remove the components in `types` from all entities in this system.
  removeComponents(sys, types)

template clear*(sys: object) =
  ## Remove all entities in this system.
  if `sys`.count > 0:
    for i in countDown(`sys`.count - 1, 0):
      `sys`.groups[i].entity.delete
    # The length of `sys`.groups is set by delete.


# -------------------------
# Wrapping iteration blocks
# -------------------------


proc initTiming(sys: NimNode, options: EcsSysOptions, core: NimNode): NimNode =
  ## Wraps `core` with timing code if `timings` is true, otherwise passes through `core` unchanged.
  case options.timings
    
    of stNone, stRunEvery:
      `core`
    
    of stProfiling:
      quote do:
        let startTime = cpuTime()
        `core`
        let endTime = cpuTime()
        `sys`.timePerGroupRun = endTime - startTime
        if `sys`.count > 0:
          `sys`.timePerGroupItem = `sys`.timePerGroupRun / `sys`.count.float
        else:
          `sys`.timePerGroupItem = 0.0

        # Note that the min/max timers are user handled with `system.resetMinMax`.
        `sys`.updateTimings()


proc wrapAllBlock(id: EcsIdentity, name: string, sysIndex: SystemIndex, options: EcsSysOptions, code: NimNode): NimNode =
  let
    # `sys` is the system variable parameter passed to the doProc.
    sys = ident "sys"
    cacheId = quote do: EcsIdentity(`id`)
    groupIndex = ident "groupIndex"
    idx = genSym(nskVar, "i")
    sysLen = ident "sysLen"

    # if `entity` != `item.entity` then this row has been removed.
    rowEnt = ident "entity"
    entAccess = userEntAccess(quote do: `sys`.groups[`idx`].entity)

    sysItem = id.systemItem(sysIndex, rowEnt, sys, groupIndex)

  result = initTiming(sys, options, quote do:
    block:
      static:
        if `cacheId`.inSystemAll:
          error "Cannot embed 'all' blocks within themselves"
        `cacheId`.set_inSystemAll true
        `cacheId`.set_ecsSysIterating true

      var
        `sysLen` = `sys`.count()

      if `sysLen` > 0:
        var
          `idx`: int

        while `idx` < `sysLen`:

          `entAccess`

          let
            ## Read-only index into `groups`.
            `groupIndex` {.used, inject.} = `idx`

          # System `item` template.
          `sysItem`

          # Inject the user's statements from `all:`
          `code`

          when `cacheId`.systemCalledDelete or
            `cacheId`.sysRemoveAffectedThisSystem:
              `sysLen` = `sys`.count()
              if `sysLen` > 0 and (`idx` < `sysLen` and `sys`.groups[`idx`].entity == `rowEnt`):
                # This row wasn't deleted so move forward.
                `idx` = `idx` + 1
          else:
            `idx` = `idx` + 1
      static:
        `cacheId`.set_inSystemAll false
        `cacheId`.set_ecsSysIterating false
  )


type
  Command = enum
    cmdNone,
    cmdMultiPass = "multipass",
    cmdStochastic = "stochastic"


proc getCommand(node: NimNode): Command =
  if node.kind == nnkIdent:
    case node.strVal.toLowerAscii
      of $cmdMultiPass:
        result = cmdMultiPass
      of $cmdStochastic:
        result = cmdStochastic


proc parseStreamCommands(code: NimNode): tuple[amount: NimNode, command: Command, body: NimNode] =
  # Stream commands:
  #   stream multipass <optional count>: <code block>
  #     - forces a minimum of `count` rows to be processed even if repeated.
  #     - omitting count uses system.streamRate.
  #   stream stochastic <optional count>: <code block>
  #     - selects rows to process at random.
  #     - omitting count uses system.streamRate.


  let formatError =
      "Expected one of:\n" &
      "  'stream:'\n" &
      "  'stream <command|parameter>:'\n" &
      "  'stream <parameter|parameter> <command|parameter>:'\n" &
      "Passed:\n" & code.repr & "\n"

  if code.len notin [2, 3]:
    error formatError

  case code.kind
    of nnkCommand:
      result.body = code[2]

      case code[1].kind
        of nnkIntLit:
          # `stream N:`
          result.amount = code[1]
        
        of nnkIdent:
          # `stream x:`
          result.command = code[1].getCommand

          if result.command == cmdNone:
            # Pass through user's identifier.
            result.amount = code[1]
        
        of nnkCommand:
          # `stream x y:`

          result.command = code[1][0].getCommand

          if result.command != cmdNone:
            # `stream command x:`
            result.amount = code[1][1]

          else:
            # Check for `stream x command:`
            result.command = code[1][1].getCommand

            if result.command == cmdNone:
              # No commands found.
              error formatError
            else:
              result.amount = code[1][0]

        else:
          error formatError

    of nnkCall:
      # `stream:`
      if code[1].kind != nnkStmtList:
        error formatError
      else:
        result.body = code[1]
    else:
      error formatError


proc wrapStreamBlock(id: EcsIdentity, name: string, sysIndex: SystemIndex, options: EcsSysOptions, code: NimNode): NimNode =
  let
    # `sys` is the system variable parameter passed to the doProc.
    sys = ident "sys"
    cacheId = quote do: EcsIdentity(`id`)
    groupIndex = ident "groupIndex"
    sysLen = ident "sysLen"

    # if `entity` != `item.entity` then this row has been removed.
    rowEnt = ident "entity"
    entAccess = userEntAccess(quote do: `sys`.groups[`groupIndex`].entity)

    sysItem = id.systemItem(sysIndex, rowEnt, sys, groupIndex)

    streamDetails = parseStreamCommands(code)
    streamBody = streamDetails.body

    streamAmount =
      if streamDetails.amount == nil:
        # Use default stream rate if not provided.
        quote do:
          `sys`.streamRate
      else:
        streamDetails.amount

  if streamDetails.body.len == 0:
    error "Stream cannot be empty"

  let
    processed = ident "sysProcessed"
    finished = genSym(nskVar, "finished")
    randomValue = bindSym "rand"

    processNext =
      case streamDetails.command
        of cmdNone:
          quote do:
            `sys`.lastIndex = `sys`.lastIndex + 1
            `finished` = (`processed` >= `streamAmount`) or (`sys`.lastIndex >= `sysLen`)
        of cmdMultiPass:
          quote do:
            `sys`.lastIndex = (`sys`.lastIndex + 1) mod `sysLen`
            `finished` = `processed` >= `streamAmount`
        of cmdStochastic:
          quote do:
            `sys`.lastIndex = `randomValue`(`sys`.high)
            `finished` = `processed` >= `streamAmount`

    initFirstRun =
      case streamDetails.command
        of cmdNone, cmdMultiPass:
          quote do:
            if `sys`.count > 0:
              `sys`.lastIndex = `sys`.lastIndex mod `sysLen`
        of cmdStochastic:
          quote do:
            if not `finished`:
              `sys`.lastIndex = `randomValue`(`sys`.high)

  result = initTiming(sys, options, quote do:
    static:
      if `cacheId`.inSystemStream:
        error "Cannot embed 'stream' blocks within themselves"
      `cacheId`.set_inSystemStream  true
      `cacheId`.set_ecsSysIterating true
    block:
      # loop per entity in system

      # Note that streaming bodies always check the length each iteration so
      # there's no need to modify generation when a delete is called.

      var
        `sysLen` = `sys`.count()
        `processed`: int
        `finished` = `sysLen` == 0
      `initFirstRun`
      while not `finished`:

        let
          ## Current index into `groups`.
          `groupIndex` {.used, inject.} = `sys`.lastIndex

        `entAccess`
        
        # System `item` template.
        `sysItem`
        
        # Inject stream statements.
        `streamBody`
        
        `processed` = `processed` + 1
        `sysLen` = `sys`.count()

        # processing based on commands.
        `processNext`
      
      static:
        `cacheId`.set_inSystemStream false
        `cacheId`.set_ecsSysIterating false
  )


#---------------------------
# Generating the system proc
#---------------------------


proc isBlockNode(node: NimNode): bool =
  node.len > 0 and
    (node.kind in [nnkCall, nnkCommand]) and
    (node[0].kind in [nnkIdent, nnkSym, nnkOpenSymChoice])


iterator blocks(body: NimNode): int =
  ## Return the index of top level nodes that could be blocks.
  
  var
    bodyIdx: int
  
  while bodyIdx < body.len:
    if body[bodyIdx].isBlockNode:  
        yield bodyIdx

    bodyIdx.inc


proc generateSystem(id: EcsIdentity, name: string, componentTypes: NimNode, options: ECSSysOptions, systemBody: NimNode): NimNode =
  ## Create the system proc to 'tick' the system.

  if systemBody == nil:
    error "makeSystem needs a `body`"

  systemBody.expectKind nnkStmtList

  type
    SystemBlock = enum
      sbFields = "fields"
      sbInit = "init",
      sbStart = "start",
      sbAll = "all",
      sbStream = "stream"
      sbFinish = "finish"
      sbAdded = "added"
      sbRemoved = "removed"
      sbAddedCallback = "addedcallback"
      sbRemovedCallback = "removedcallback"

  let
    sysId = ident(systemVarName(name))
    sys = ident "sys"
    sysType = ident systemTypeName(name)

  var
    sysIdxSearch = id.findSystemIndex(name)
    sysIndex = sysIdxSearch[1]

  var
    extraFields: NimNode
    hasFieldsBlock: bool

  # Extract definitions `fields:` blocks for system variable creation.
  # If the system is previously defined, fields are checked to match.
  for item in systemBody:
    if item.kind == nnkCall and
        item[0].kind in [nnkIdent, nnkOpenSymChoice] and
        ($item[0]).toLowerAscii == $sbFields:

      if not hasFieldsBlock:
        hasFieldsBlock = true
        extraFields = newStmtList()

      for fieldDef in item[1]:
        extraFields.add fieldDef

  result = newStmtList()

  if sysIdxSearch.found:
    # This system has already been defined.
    # Check the state passed here matches the previous definition.

    let
      existingSysIdx = sysIdxSearch.index
      existingExtraFields = id.extraFields(existingSysIdx)
      (uArgs, componentTypesStr) = id.unpackArgs componentTypes
      origDefLocStr = "\nOriginal system definition at: " &
        id.ecsSystemSourceLoc(sysIdxSearch.index) & "\n"
    
    if hasFieldsBlock and not(existingExtraFields == extraFields):
      var
        fStr1 = existingExtraFields.repr
        fStr2 = extraFields.repr
      if fStr1 == "nil": fStr1 = "<None>"
      if fStr2 == "nil": fStr2 = "<None>"

      error "Fields block doesn't match the original system definition:\n" &
        "Original fields:\n" & fStr1 &
        "\n\nPassed fields:" & fStr2 &
        origDefLocStr

    if id.bodyDefined(existingSysIdx):
      error "System \"" & name & "\" already has a body defined at: " &
        id.ecsSystemBodySourceLoc(sysIdxSearch.index) & "\n"
  
    let
      expectedTypes = id.ecsSysRequirements existingSysIdx
      existingOpts = id.getOptions existingSysIdx
      negations = id.ecsSysNegations existingSysIdx
      owned = id.ecsOwnedComponents existingSysIdx

    if componentTypes.len > 0:
      # Check the components given to makeSystem match defineSystem.
      
      template errMsg = error "Components passed to makeSystem \"" & name &
        "\" [" & componentTypesStr &
        "] in conflict with previous definition in defineSystem: [" &
        id.commaSeparate(expectedTypes) & "]" &
        (if negations.len > 0: " and not [" & id.commaSeparate(negations) & "]"
          else: "") &
        (if owned.len > 0: " and owning [" & id.commaSeparate(owned) & "]"
          else: "") &
        origDefLocStr
      
      # Check given types match the original definition.
      # Currently this doesn't enforce unspecified modifiers.

      for uArg in uArgs:
        case uArg.prefix.kind
          of upNone:
            if uArg.typeId notin expectedTypes:
              errMsg()
          of upNot:
            if uArg.typeId notin negations:
              errMsg()
          of upOwn:
            if uArg.typeId notin owned:
              errMsg()
          of upCustom:
            error "Cannot process a type modifier of '" & uArg.prefix.custom.repr & "'"

    # Options must match with the original definition.
    if existingOpts != options:
      error "Options don't match with previous definition for system \"" &
        name & "\":\nOriginal options:\n" & $existingOpts &
        "\nPassed options:\n" & $options

    when defined(ecsLog) or defined(ecsLogDetails):
      echo "Adding body to pre-defined system \"", name, "\" with types [",
        id.commaSeparate(expectedTypes), "]"
  
  else:
    # This is an inline makeSystem.
    
    result.add createSystem(id, name, componentTypes, extraFields, options)

    sysIdxSearch = id.findSystemIndex(name)
    assert sysIdxSearch.found, "Internal error: cannot find system \"" & name & "\" after adding it"
    
    # Use the new SystemIndex.
    sysIndex = sysIdxSearch.index

  # Parse the system system blocks.
  
  var
    initBodies = newStmtList()
    startBodies = newStmtList()   
    finishBodies = newStmtList()
    onAdded = newStmtList()
    onRemoved = newStmtList()
    onAddedCallback = newStmtList()
    onRemovedCallback = newStmtList()

    activeBlocks: set[SystemBlockKind]
    blockChoices: array[SystemBlock, string]
  
  for b in SystemBlock.low .. SystemBlock.high:
    blockChoices[b] = $b

  const needComponentsMsg = "Cannot use this block as this system has no components: '"
  let hasComponents = id.ecsSysRequirements(sysIdxSearch.index).len > 0
  var blockRemoves: seq[int]

  for blockIndex in systemBody.blocks:
    
    template item: NimNode =
      systemBody[blockIndex]

    let
      blockTitle = ($item[0]).toLowerAscii

    if blockTitle notin blockChoices:
      # Not a known block descriptor.
      continue

    # User code is in 'item[1]'.

    case blockTitle

      of $sbFields:
        # This block's fields have already been used to create the system
        # variable, and can be removed from the body.
        activeBlocks.incl sbkFields
        blockRemoves.add blockIndex

      of $sbInit:
        activeBlocks.incl sbkInit
        initBodies.add(item[1])
        blockRemoves.add blockIndex

      of $sbStart:
        activeBlocks.incl sbkStart
        startBodies.add(item[1])
        blockRemoves.add blockIndex

      of $sbFinish:
        activeBlocks.incl sbkFinish
        finishBodies.add(item[1])
        blockRemoves.add blockIndex

      of $sbAdded:
        if not hasComponents:
          error needComponentsMsg & $sbAdded & "'"
        activeBlocks.incl sbkAdded
        onAdded.add item[1]
        blockRemoves.add blockIndex
      
      of $sbRemoved:
        if not hasComponents:
          error needComponentsMsg & $sbRemoved & "'"
        activeBlocks.incl sbkRemoved
        onRemoved.add item[1]
        blockRemoves.add blockIndex

      of $sbAddedCallback:
        if not hasComponents:
          error needComponentsMsg & $sbAddedCallback & "'"
        activeBlocks.incl sbkAddedCallback
        onAddedCallback.add item[1]
        blockRemoves.add blockIndex

      of $sbRemovedCallback:
        if not hasComponents:
          error needComponentsMsg & $sbRemovedCallback & "'"
        activeBlocks.incl sbkRemovedCallback
        onRemovedCallback = item[1]
        blockRemoves.add blockIndex

  # Search and wrap 'all' and 'stream' blocks within the body.

  proc applyIterationBlocks(parent: NimNode) =
    # Recursive search and wrap for 'all' and 'stream' blocks.
    for blockIndex in 0 ..< parent.len:
      
      template curNode: NimNode =
        parent[blockIndex]

      if curNode.isBlockNode:

        let
          blockTitle = ($curNode[0]).toLowerAscii

        case blockTitle

          of $sbAll:
            if not hasComponents:
              error needComponentsMsg & $sbAll & "'"
            activeBlocks.incl sbkAll
            parent[blockIndex] = id.wrapAllBlock(name, sysIndex, options, parent[blockIndex][1])

          of $sbStream:
            if not hasComponents:
              error needComponentsMsg & $sbAdded & "'"
            activeBlocks.incl sbkStream
            # Note: passes `curNode` rather than the code in [1], as
            # stream has to further parse the node for commands.
            parent[blockIndex] = wrapStreamBlock(id, name, sysIndex, options, curNode())
          
          else:
            discard
      else:
        # We have to go deeper.
        curNode.applyIterationBlocks

  systemBody.applyIterationBlocks

  # Add event blocks to the macrocache.

  const
    msgSealed = "This ECS has been sealed with makeEcs() and system '$1' events cannot be changed"
    msgSealedAdded = msgSealed % "added"
    msgSealedRemoved = msgSealed % "removed"

  if onAdded.len > 0:
    if id.sealed sysIndex:
      error msgSealedAdded
    id.add_onAdded(sysIndex, onAdded)
  
  if onRemoved.len > 0:
    if id.sealed sysIndex:
      error msgSealedRemoved
    id.add_onRemoved(sysIndex, onRemoved)
  
  if onAddedCallback.len > 0:
    if id.sealed sysIndex:
      error msgSealedAdded
    id.add_onAddedCallback(sysIndex, onAddedCallback)
  
  if onRemovedCallback.len > 0:
    if id.sealed sysIndex:
      error msgSealedRemoved
    id.add_onRemovedCallback(sysIndex, onRemovedCallback)

  # Remove event blocks from the output body.
  
  for i in countDown(blockRemoves.high, 0):
    systemBody.del blockRemoves[i]

  # Set up debug echo statements.
  
  var echoRun, echoInit, echoAll, echoFinish, echoCompleted = newEmptyNode()
  case options.echoRunning:
    of seNone: discard
    of seEchoUsed, seEchoUsedAndRunning, seEchoUsedAndRunningAndFinished:
      if options.echoRunning in [seEchoUsedAndRunning, seEchoUsedAndRunningAndFinished]:
        echoRun = quote do:
          echo `name` & " running..."
      if sbkInit in activeBlocks:
        echoInit = quote do:
          echo `name` & " initialising"
      if sbkAll in activeBlocks:
        echoAll = quote do:
          echo `name` & " run all"
      if sbkFinish in activeBlocks:
        echoFinish = quote do:
          echo `name` & " run finish"
      if options.echoRunning == seEchoUsedAndRunningAndFinished:
        echoCompleted = quote do:
          echo `name` & " completed"
    of seEchoAll:
      echoRun = quote do:
        echo `name` & " running..."
      echoInit = quote do:
        echo `name` & " initialising"
      echoAll = quote do:
        echo `name` & " run all"
      echoFinish = quote do:
        echo `name` & " run finish"
      echoCompleted = quote do:
        echo `name` & " completed"

  # Manage the static environment.

  let
    cacheId = quote do: EcsIdentity(`id`)

    staticInit = quote do:
      
      # Record entry into system iteration in the static environment.

      `cacheId`.set_inSystem true
      `cacheId`.set_inSystemIndex `sysIndex`.SystemIndex
      `cacheId`.set_sysRemoveAffectedThisSystem false
      `cacheId`.set_systemCalledDelete false
      const
        errPrelude = "Internal error: "
        internalError = " macrocache storage is unexpectedly populated for system \"" & `name` & "\""
      assert `cacheId`.readsFrom(`sysIndex`.SystemIndex).len == 0, errPrelude & "readsFrom" & internalError
      assert `cacheId`.writesTo(`sysIndex`.SystemIndex).len == 0, errPrelude & "writesTo" & internalError

    reportPerformance =
      when defined(ecsPerformanceHints):
        quote do:
          # Reports system component access and performance hints.
          # Each component access is displayed in order of access
          # within the system.
          const prefix {.used.} = "System \"" & `name` & "\""
          when `cacheId`.len_readsFrom(`sysIndex`.SystemIndex) > 0:
            debugPerformance `cacheId`, prefix & ": Reads from: " &
              `cacheId`.commaSeparate(`cacheId`.readsFrom(`sysIndex`.SystemIndex))
          when `cacheId`.len_writesTo(`sysIndex`.SystemIndex) > 0:
            debugPerformance `cacheId`, prefix & ": Writes to: " &
              `cacheId`.commaSeparate(`cacheId`.writesTo(`sysIndex`.SystemIndex))
          when `cacheId`.systemCalledDelete:
            debugPerformance `cacheId`, prefix & " uses an arbitrary delete, length must be checked each iteration"
          elif `cacheId`.sysRemoveAffectedThisSystem:
            debugPerformance `cacheId`, prefix & " can remove items from this system, length must be checked each iteration"
      else:
        newStmtList()

    staticTearDown = quote do:

      `reportPerformance`

      # Record exit of system iteration in the static environment.

      `cacheId`.set_inSystem false
      `cacheId`.set_inSystemIndex InvalidSystemIndex

      `cacheId`.set_sysRemoveAffectedThisSystem false
      `cacheId`.set_systemCalledDelete false

  var
    sysTypeNames: string
  
  for typeName in id.systemTypesStr(sysIndex):
    if sysTypeNames != "": sysTypeNames &= ", "
    sysTypeNames &= typeName

  let
    systemComment = newCommentStmtNode("System \"" & name & "\", using components: " & sysTypeNames)
  
  # Assemble the final system procedure.

  let
    doSystem = ident doProcName(name)
  var
    initWrapper =
      if initBodies.len > 0:
        quote do:
          if unlikely(not `sys`.initialised):
            `echoInit`
            `initBodies`
            `sys`.initialised = true
      else:
        newStmtList()
  
    runCheck, initRunEvery: NimNode
  
  case options.timings
    of stNone:
      runCheck = quote: not `sys`.disabled
      initRunEvery = newStmtList()
    of stRunEvery, stProfiling:
      runCheck = quote do:
        (not `sys`.disabled) and ((`sys`.runEvery == 0.0) or (cpuTime() - `sys`.lastRun >= `sys`.runEvery))
      initRunEvery = quote do:
        # Update last tick time
        `sys`.lastRun = cpuTime()

  let
    sysBody =
      if systemBody.len == 0 and echoAll.len == 0:
        nnkDiscardStmt.newTree(newEmptyNode())
      else:
        systemBody

    # This procedure is executes the system.

    systemProc = quote do:
      proc `doSystem`*(`sys`: var `sysType`) =
        `systemComment`

        `echoRun`
        if `runCheck`:
          `initRunEvery`
          `initWrapper`
          `startBodies`
          static:
            `staticInit`

          if not `sys`.paused:
            `echoAll`
            `sysBody`

          static:
            `staticTearDown`

          `echoFinish`
          `finishBodies`

          for i in 0 ..< `sys`.deleteList.len:
            `sys`.deleteList[i].delete
          `sys`.deleteList.setLen 0
        `echoCompleted`
        
      
      template `doSystem`*: untyped =
        `doSystem`(`sysId`)

  # Store the body of the do proc.
  # The procs themselves are only accessible after commitSystem is called.
  id.set_definition(sysIndex, systemProc)

  # Add to the list of systems with a defined body.
  # This allows detection of trying to set a body multiple times.
  id.set_bodyDefined(sysIndex, true)
  id.set_ecsSystemBodySourceLoc(sysIndex, componentTypes.lineInfo)

  # Add to the current list of systems with uncommitted bodies.
  id.addUncommitted sysIndex


# ------------------
# Options specified
# ------------------


macro makeSystemOpts*(id: static[EcsIdentity], name: static[string], componentTypes: openarray[untyped], options: static[ECSSysOptions], systemBody: untyped): untyped =
  ## Define a system and/or add a system code body using an ECS identity with specific options.
  generateSystem(id, name, componentTypes, options, systemBody)


macro makeSystemOpts*(name: static[string], componentTypes: untyped, options: static[ECSSysOptions], systemBody: untyped): untyped =
  ## Define a system and/or add a system code body using the default ECS identity with specific options.
  generateSystem(defaultIdentity, name, componentTypes, options, systemBody)


# --------------------
# No options specified
# --------------------


proc sysOptionsOrDefault(id: EcsIdentity, name: string): tuple[found: bool, options: EcsSysOptions] {.compileTime.} =
  let
    sysIdxSearch = id.findSystemIndex(name)

  if sysIdxSearch.found:
    (true, id.getOptions sysIdxSearch.index)
  else:
    (false, defaultSysOpts)


macro makeSystem*(id: static[EcsIdentity], name: static[string], componentTypes: untyped, systemBody: untyped): untyped =
  ## Define a system and/or add a system code body using an ECS identity.
  ## 
  ## Previously defined systems carry their options over, otherwise `defaultSystemOptions` is used.
  let (_, options) = id.sysOptionsOrDefault name
  generateSystem(id, name, componentTypes, options, systemBody)


template makeSystem*(name: static[string], componentTypes: untyped, systemBody: untyped): untyped =
  ## Define a system and/or add a system code body using the default ECS identity.
  ## 
  ## Previously defined systems carry their options over, otherwise `defaultSystemOptions` is used.
  defaultIdentity.makeSystem(name, componentTypes, systemBody)


template makeSystem*(name: static[string], systemBody: untyped): untyped =
  ## Define a system and/or add a system code body using the default ECS identity.
  ## 
  ## Previously defined systems carry their options over, otherwise `defaultSystemOptions` is used.
  defaultIdentity.makeSystem(name, nil, systemBody)


macro makeSystemBody*(id: static[EcsIdentity], name: static[string], systemBody: untyped): untyped =
  ## Define the code body for a previously defined system using an ECS identity.
  let opts = id.sysOptionsOrDefault name

  if not opts.found:
    error "`makeSystemBody` requires a 'defineSystem' for \"" & name & "\""

  generateSystem(id, name, newEmptyNode(), opts.options, systemBody)


template makeSystemBody*(name: static[string], systemBody: untyped): untyped =
  ## Define the code body for a previously defined system using the default ECS identity.
  defaultIdentity.makeSystemBody(name, systemBody)


macro forSystemsUsing*(id: static[EcsIdentity], typeIds: static[openarray[ComponentTypeId]], actions: untyped): untyped =
  ## Statically perform `actions` only for systems defined for these types.
  ## Note that typeIds must be known at compile time.
  var processed: seq[SystemIndex]
  result = newStmtList()
  for compId in typeIds:
    for sys in id.systems(compId):
      if sys notin processed:
        processed.add sys
        let
          sysName = id.getSystemName sys
          curSysVar = id.instantiation sys
          curTupType = ident sysName.itemTypeName
        result.add(quote do:
          block:
            template sys: untyped = `curSysVar`
            template sysType: untyped = `curTupType`
            actions
        )
  genLog "# forSystemsUsing:\n", result.repr


macro forSystemsUsing*(id: static[EcsIdentity], types: openarray[typedesc], actions: untyped): untyped =
  ## Statically perform `actions` only for systems defined for these types.
  ## Systems may have other types defined but must include all of `types`.
  ## Note that types must be known at compile time.
  var typeIds = newSeq[ComponentTypeId]()
  for paramType in types:
    let paramTypeId = typeStringToId(id, $paramType)
    typeIds.add paramTypeId
  #
  result = quote do:
    forSystemsUsing(`typeIds`, `actions`)


template forSystemsUsing*(types: openarray[typedesc], actions: untyped): untyped =
  ## Statically perform `actions` only for systems defined for these types.
  ## Systems may have other types defined but must include all of `types`.
  ## Note that types must be known at compile time.
  forSystemsUsing(defaultIdentity, types, actions)
