# This is the PJS code generator.

import
  ast, strutils, trees, magicsys, options,
  nversion, msgs, idents, types, tables,
  ropes, math, passes, ccgutils, wordrecg, renderer,
  intsets, cgmeth, lowerings, sighashes, modulegraphs, lineinfos, rodutils,
  transf, injectdestructors


from modulegraphs import ModuleGraph, PPassContext

type
  TypeCache = Table[SigHash, Rope]
  BModule = ref TPjsGen
  TPjsGen = object of PPassContext
    module: PSym
    graph: ModuleGraph
    g: PGlobals
    config: ConfigRef
    typeCache: TypeCache # cache for generated types
  BProc = ref TProc
  TProc = object
    m: BModule
    prc: PSym # The Nim proc that this proc belongs to, can be NIL for module!
    body: Rope
  PGlobals = ref object of RootObj
    typeInfo: Rope
    constants: Rope
    code: Rope
  TResKind = enum
    resNone # not set
    resExpr # is some complex expression
    resVal # is a temporary / value / l-value
  TPjsTypeKind = enum
    etyVoid # void
    etyBool # bool
    etyInt8 # i8
    etyInt16 # i16
    etyInt32 # i32
    etyFloat32 # f32
    etyFloat64 # f64
    etyUint8 # u8
    etyUint16 # u16
    etyUint32 # u32
    etyArray # array[N, T]
    etyRef # ref[T]
    etyStruct # struct Foo {...}
    etyProc # fn (...)
  TCompRes = object
    kind: TResKind
    typ: TPjsTypeKind
    res: Rope # result part

proc newGlobals(): PGlobals =
  new(result)

proc newModule(graph: ModuleGraph; module: PSym): BModule =
  new(result)
  result.module = module
  result.graph = graph
  result.config = graph.config
  if graph.backend == nil:
    let g = newGlobals()
    result.g = g
    graph.backend = g
  else:
    result.g = PGlobals(graph.backend)

proc newProc(m: BModule; prc: PSym): BProc =
  new(result)
  result.m = m
  result.prc = prc

template config*(p: BProc): ConfigRef =
  p.m.config

# {{{ name mangling

proc mangleName(m: BModule, s: PSym): Rope =
  proc validJsName(name: string): bool =
    result = true
    const reservedWords = ["abstract", "await", "boolean", "break", "byte",
      "case", "catch", "char", "class", "const", "continue", "debugger",
      "default", "delete", "do", "double", "else", "enum", "export", "extends",
      "false", "final", "finally", "float", "for", "function", "goto", "if",
      "implements", "import", "in", "instanceof", "int", "interface", "let",
      "long", "native", "new", "null", "package", "private", "protected",
      "public", "return", "short", "static", "super", "switch", "synchronized",
      "this", "throw", "throws", "transient", "true", "try", "typeof", "var",
      "void", "volatile", "while", "with", "yield"]
    case name
    of reservedWords:
      return false
    else:
      discard
    if name[0] in {'0'..'9'}: return false
    for chr in name:
      if chr notin {'A'..'Z','a'..'z','_','$','0'..'9'}:
        return false
  result = s.loc.r
  if result == nil:
    if s.kind == skField and s.name.s.validJsName:
      result = rope(s.name.s)
    elif s.kind == skTemp:
      result = rope(mangle(s.name.s))
    else:
      var x = newStringOfCap(s.name.s.len)
      var i = 0
      while i < s.name.s.len:
        let c = s.name.s[i]
        case c
        of 'A'..'Z':
          if i > 0 and s.name.s[i-1] in {'a'..'z'}:
            x.add '_'
          x.add(chr(c.ord - 'A'.ord + 'a'.ord))
        of 'a'..'z', '_', '0'..'9':
          x.add c
        else:
          x.add("HEX" & toHex(ord(c), 2))
        inc i
      result = rope(x)
    # From ES5 on reserved words can be used as object field names
    if s.kind != skField:
      if m.config.hcrOn:
        # When hot reloading is enabled, we must ensure that the names
        # of functions and types will be preserved across rebuilds:
        add(result, idOrSig(s, m.module.name.s, m.sigConflicts))
      else:
        add(result, "_")
        add(result, rope(s.id))
    s.loc.r = result

# }}}
# {{{ JS escape string literal

proc escapeJSString(s: string): string =
  result = newStringOfCap(s.len + s.len shr 2)
  result.add("\"")
  for c in items(s):
    case c
    of '\l': result.add("\\n")
    of '\r': result.add("\\r")
    of '\t': result.add("\\t")
    of '\b': result.add("\\b")
    of '\a': result.add("\\a")
    of '\e': result.add("\\e")
    of '\v': result.add("\\v")
    of '\\': result.add("\\\\")
    of '\"': result.add("\\\"")
    else: add(result, c)
  result.add("\"")

proc makeJSString(s: string, escapeNonAscii = true): Rope =
  if escapeNonAscii:
    result = strutils.escape(s).rope
  else:
    result = escapeJSString(s).rope

# }}}
# {{{ types

# Types that are irrelevant to this backend, and thus can be safely ignored.
const IrrelevantTypes = {tyGenericBody, tyGenericInst, tyGenericInvocation,
                          tyDistinct, tyRange, tyStatic, tyAlias, tySink,
                          tyInferred, tyOwned}

const PjsRefTypes = {tyRef, tySequence, tyString, tyProc, tyArray}

proc mapType(typ: PType): TPjsTypeKind

proc mapSetType(conf: ConfigRef; typ: PType): TPjsTypeKind =
  case int(getSize(conf, typ))
  of 1: result = etyInt8
  of 2: result = etyInt16
  of 4: result = etyInt32
  else: result = etyTypedArray

proc mapType(typ: PType): TPjsTypeKind =
  ## Maps a Nim type to a PJS type
  let t = skipTypes(typ, abstractInst)
  case t.kind
  of tyNone, tyTyped: result = etyVoid
  of tyBool: result = etyBool
  of tyChar: result = etyUint8
  of tySet: result = mapSetType(conf, typ)
  of tyOpenArray, tyArray, tyVarargs, tyUncheckedArray:
    result = etyTypedArray
    if not isPjsPod(lastSon(typ)):
      result = etyJsArray
  of tyObject, tyTuple:
    result = etyStruct
  of tyUserTypeClasses:
    doAssert typ.isResolvedUserTypeClass
    result = mapType(conf, typ.lastSon)
  of tyGenericBody, tyGenericInst, tyGenericParam, tyDistinct, tyOrdinal,
     tyTypeDesc, tyAlias, tySink, tyInferred, tyOwned:
    result = mapType(conf, lastSon(typ))
  of tyEnum:
    if firstOrd(conf, typ) < 0:
      result = etyInt32
    else:
      case int(getSize(conf, typ)):
      of 1: result = etyUint8
      of 2: result = etyUint16
      of 4: result = etyInt32
      of 8: result = etyInt64
      else: result = etyInt32
  of tyRange:
    result = mapType(conf, typ.sons[0])
  of tyPtr, tyVar, tyLent, tyRef:
    var base = skipTypes(typ.lastSon, typedescInst)
    case base.kind
    of tyOpenArray, tyArray, tyVarargs, tyUncheckedArray:
      result = etyTypedArray
      if not isPjsPod(lastSon(typ)):



proc cacheGetType(tab: TypeCache; sig: SigHash): Rope =
  # returns nil if we need to declare this type.
  # since types are now unique via the ``getUniqueType`` mechanism,
  # this slow linear search is not necessary anymore:
  result = tab.getOrDefault(sig)

proc cacheAddType(tab: TypeCache; sig: SigHash; t: Rope): void =
  tab[sig] = t

proc typeNameOrLiteral(m: BModule; t: PType, literal: string): Rope =
  if t.sym != nil and sfImportc in t.sym.flags and t.sym.magic == mNone:
    result = t.sym.loc.r
  else:
    result = rope(literal)

proc getSimpleTypeDesc(m: BModule; typ: PType): Rope =
  const NumericalTypeToStr: array[tyInt..tyUInt64, string] = [
    "i32", "i8", "i16", "i32", "i64", "f64", "f32", "f64", "f128",
    "u32", "u8", "u16", "u32", "u64"]
  case typ.kind
  of tyString:
    result = typeNameOrLiteral(m, typ, "jarray[u8]")
  of tyCString:
    result = typeNameOrLiteral(m, typ, "string")
  of tyBool:
    result = typeNameOrLiteral(m, typ, "bool")
  of tyChar:
    result = typeNameOrLiteral(m, typ, "u8")
  of tyInt..tyUInt64:
    result = typeNameOrLiteral(m, typ, NumericalTypeToStr[typ.kind])
  of tyDistinct, tyRange, tyOrdinal:
    result = getSimpleTypeDesc(m, typ.sons[0])
  of tyStatic:
    if typ.n != nil:
      result = getSimpleTypeDesc(m, lastSon(typ))
    else:
      internalError(m.config, "tyStatic for getSimpleTypeDesc")
  of tyGenericInst, tyAlias, tySink, tyOwned:
    result = getSimpleTypeDesc(m, lastSon(typ))
  else:
    result = nil
  if result != nil and typ.isImportedType():
    let sig = hashType(typ)
    if cacheGetType(m.typeCache, sig) == nil:
      cacheAddType(m.typeCache, sig, result)

proc getTypePre(m: BModule, typ: PType; sig: SigHash): Rope =
  if typ == nil:
    result = rope("void")
  else:
    result = getSimpleTypeDesc(m, typ)
    if result == nil:
      result = cacheGetType(m.typeCache, sig)

proc getTypeDescAux(m: BModule, origTyp: PType, check: var IntSet): Rope =
  # returns only the type's name
  var t = origTyp.skipTypes(IrrelevantTypes)
  if containsOrIncl(check, t.id):
    if not (isImportedCppType(origTyp) or isImportedCppType(t)):
      internalError(m.config, "cannot generate C type for: " & typeToString(origTyp))
    # XXX: this BUG is hard to fix -> we need to introduce helper structs,
    # but determining when this needs to be done is hard. We should split
    # C type generation into an analysis and a code generation phase somehow.
  let sig = hashType(origTyp)
  result = getTypePre(m, t, sig)
  if result != nil:
    excl(check, t.id)
    return
  case t.kind
  of tyRef:
    var et = origTyp.skipTypes(abstractInst).lastSon
    var etB = et.skipTypes(abstractInst)
    if mapType(m.config, t) == ctPtrToArray:

proc getTypeDesc(m: BModule, typ: PType): Rope =
  var check = initIntSet()
  result = getTypeDescAux(m, typ, check)

# }}}
# {{{ gen

proc genStmt(p: BProc, n: PNode): void
proc gen(p: BProc, n: PNode, r: var TCompRes): void

proc genLineDir(p: BProc, n: PNode): void =
  # TODO: Support linedir?
  discard

proc genVarInit(p: BProc, v: PSym, n: PNode) =
  var a: TCompRes
  var s: Rope
  var varCode: string
  var varName = mangleName(

proc genVarStmt(p: BProc, n: PNode) =
  for i in 0 ..< len(n):
    var a = n.sons[i]
    if a.kind != nkCommentStmt:
      if a.kind == nkVarTuple:
        let unpacked = lowerTupleUnpacking(p.m.graph, a, p.prc)
        genStmt(p, unpacked)
      else:
        assert(a.kind == nkIdentDefs)
        assert(a.sons[0].kind == nkSym)
        var v = a.sons[0].sym
        if lfNoDecl notin v.loc.flags and sfImportc notin v.flags:
          genLineDir(p, a)
          if sfCompileTime notin v.flags:
            genVarInit(p, v, a.sons[2])
          else:
            # lazy emit, done when it's actually used.
            if v.ast == nil: v.ast = a[2]

proc gen(p: BProc, n: PNode, r: var TCompRes): void =
  r.typ = etyNone
  r.kind = resNone
  case n.kind
  of nkCharLit..nkUInt64Lit:
    if n.typ.kind == tyBool:
      r.res = if n.intVal == 0: rope"false" else: rope"true"
    else:
      r.res = rope(n.intVal)
    r.kind = resExpr
  of nkStmtList, nkStmtListExpr:
    # this shows the distinction is nice for backends and should be kept
    # in the frontend
    let isExpr = not isEmptyType(n.typ)
    for i in 0 ..< len(n) - isExpr.ord:
      genStmt(p, n.sons[i])
    if isExpr:
      gen(p, lastSon(n), r)
  of nkVarSection, nkLetSection:
    genVarStmt(p, n)
  of nkConstSection:
    discard
  of nkTypeSection, nkCommentStmt, nkIteratorDef, nkIncludeStmt,
     nkImportStmt, nkImportExceptStmt, nkExportStmt, nkExportExceptStmt,
     nkFromStmt, nkTemplateDef, nkMacroDef, nkStaticStmt:
    discard
  else:
    internalError(p.config, n.info, "gen: unknown node type: " & $n.kind)

proc genStmt(p: BProc, n: PNode): void =
  var r: TCompRes
  gen(p, n, r)
  if r.res != nil:
    p.body.add(r.res)
    p.body.add(rope";")

proc genModule(p: BProc, n: PNode): void =
  var transformedN = transformStmt(p.m.graph, p.m.module, n)
  genStmt(p, transformedN)

# }}}
# {{{

proc wholeCode(m: BModule): Rope =
  let globals = PGlobals(m.graph.backend)
  result = globals.code

proc myOpen(graph: ModuleGraph; module: PSym): PPassContext =
  result = newModule(graph, module)

proc myProcess(b: PPassContext, n: PNode): PNode =
  result = n
  if b == nil: return
  let m = BModule(b)
  if passes.skipCodegen(m.config, n):
    return
  let p = newProc(m, nil)
  genModule(p, n)

proc myClose(graph: ModuleGraph; b: PPassContext; n: PNode): PNode =
  result = myProcess(b, n)
  let m = BModule(b)
  if sfMainModule in m.module.flags:
    let code = wholeCode(m)
    let outFile = m.config.prepareToWriteOutput()
    discard writeRopeIfNotEqual(code, outFile)

const PjsGenPass* = makePass(myOpen, myProcess, myClose)

# }}}
# vim: set foldmethod=marker:
