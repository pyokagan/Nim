# This is the PJS code generator.

import
  ast, strutils, trees, magicsys, options,
  nversion, msgs, idents, types, tables,
  ropes, math, passes, ccgutils, wordrecg, renderer,
  intsets, cgmeth, lowerings, sighashes, modulegraphs, lineinfos, rodutils,
  transf, injectdestructors


from modulegraphs import ModuleGraph, PPassContext

type
  BModule = ref TPjsGen
  TPjsGen = object of PPassContext
    module: PSym
    graph: ModuleGraph
    g: PGlobals
    config: ConfigRef
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
    etyNone # no type
    etyProc # proc type
    etyBool
    etyInt8
    etyInt16
    etyInt32
    etyUint8
    etyUint16
    etyUint32
    etyFloat32
    etyFloat64
    etyString
    etyRef
    etyArray
    etyNimSeq
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

# {{{ gen

proc gen(p: BProc, n: PNode, r: var TCompRes): void

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
