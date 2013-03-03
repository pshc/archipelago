from atom import *
from base import *
from globs import *
import compiler
from compiler import ast
import re

ScopeContext = DT('ScopeContext', ('indent', int),
                                  ('syms', {(str, bool): object}),
                                  ('blockMatch', bool),
                                  ('prevContext', None))
SCOPE = new_env('SCOPE', ScopeContext)

OmniContext = DT('OmniContext', ('decls', ModuleDecls),
                                ('funcDefns', [TopFunc]),
                                ('imports', [object]),
                                ('exports', [object]),
                                ('missingRefs', {(str, str): [object]}),
                                ('loadedDeps', set([Module])),
                                ('directlyImportedModuleNames', set([str])))
OMNI = new_env('OMNI', OmniContext)

AstType = new_extrinsic('AstType', (str, FuncMeta))
AstHint = new_extrinsic('AstHint', {str: str})

def ast_envs():
    decls = blank_module_decls()
    omni = OmniContext(decls, [], {}, {}, {}, set(), set())
    scope = ScopeContext(0, {}, False, None)
    return omni, scope

def is_top_level():
    return env(SCOPE).indent == 0

loaded_module_export_names = {}

valueNamespace = 'value'
typeNamespace = 'type'
symbolNamespace = 'symbol'

def sym_call(path, args):
    mod, sym = path.split('.')
    assert mod in WRITTEN_MODULES, "%s not written yet!" % (mod,)
    syms = loaded_module_export_names[WRITTEN_MODULES[mod]]
    sym = (sym, valueNamespace)
    assert sym in syms, "%s not found in %s" % (sym, syms.keys())
    return S.VoidStmt(VoidCall(E.Bind(syms[sym]), args))

def builtin_ref(name):
    return E.Bind(BUILTINS[name])

def builtin_call(name, args):
    return E.Call(builtin_ref(name), args)


def identifier(obj, name=None, namespace=valueNamespace,
               permissible_nms=frozenset(), export=False):
    scope = env(SCOPE)
    already_Named = name is None
    if already_Named:
        name = extrinsic(Name, obj)
    key = (name, namespace)
    assert name in permissible_nms or key not in scope.syms, (
            "Symbol '%s' already in %s env\n%s" % (
            name, namespace,
            '\n'.join('\t'+str(s) for s, ns in scope.syms if ns == namespace)))
    assert check_bind_kind(obj), "Can't bind %s %r to %r" % (namespace, obj,
            name)
    scope.syms[key] = obj
    if not already_Named:
        add_extrinsic(Name, obj, name)

    omni = env(OMNI)
    missing_binds = omni.missingRefs.get(key)
    if missing_binds is not None:
        for bind in missing_binds:
            bind.target = obj
        del omni.missingRefs[key]
    if export:
        omni.exports[key] = obj

def ident_exists(nm, namespace=valueNamespace):
    scope = env(SCOPE)
    key = (nm, namespace)
    while scope is not None:
        o = scope.syms.get(key)
        if o is not None:
            return Just(o)
        scope = scope.prevContext

    ext = env(OMNI).imports.get(key)
    if ext is not None:
        return Just(ext)

    return Nothing()

def refs_existing(nm, namespace=valueNamespace):
    ref = ident_exists(nm, namespace)
    if isJust(ref):
        return E.Bind(fromJust(ref))
    key = (nm, namespace)
    fwd_ref = E.Bind(key)
    omni = env(OMNI)
    omni.missingRefs.setdefault(key, []).append(fwd_ref)
    return fwd_ref

def check_bind_kind(v):
    if isinstance(v, (GlobalVar, Var, Builtin, Ctor)):
        return True
    elif isinstance(v, (DataType, Env, Extrinsic)):
        return True
    else:
        return False

def type_ref(nm):
    if nm in types_by_name:
        return types_by_name[nm]()
    ref = ident_exists(nm, typeNamespace)
    return maybe_(TForward(nm, []), ref)

def destroy_forward_ref(ref):
    if not isinstance(ref.refAtom, basestring):
        return
    omni = env(OMNI)
    for t in (True, False):
        key = (ref.refAtom, t)
        refs = omni.missingRefs.get(key, [])
        if ref in refs:
            refs.remove(ref)
            if not refs:
                del omni.missingRefs[key]
            return
    assert False, "Couldn't find forward ref for destruction"

def inside_scope(f):
    def new_scope(*args, **kwargs):
        prev = env(SCOPE)
        new = ScopeContext(prev.indent + 1, {}, False, prev)
        return in_env(SCOPE, new, lambda: f(*args, **kwargs))
    new_scope.__name__ = f.__name__
    return new_scope

def make_grammar_decorator(index_only=False):
    dispatch_index = {}
    def decorator(key, meta=None):
        def inserter(f):
            dispatch_index[key] = f
            f.meta = meta
            return f
        return inserter
    def dispatch(nd, *args):
        f = dispatch_index.get(nd.__class__)
        if f is None:
            return False
        return f(nd, *args)
    return (decorator, dispatch_index if index_only else dispatch)

top_level, conv_top_level = make_grammar_decorator()
stmt, conv_stmt = make_grammar_decorator()
expr, conv_expr = make_grammar_decorator()
special_assignment, SPECIAL_ASSIGNMENTS = make_grammar_decorator(True)
special_call, SPECIAL_CALLS = make_grammar_decorator(True)

def conv_exprs(elist):
    return map(conv_expr, elist)

def conv_type(t, tvars, dt=None):
    m = match(t)
    if m("DataType(_, _, _)"):
        return vanilla_tdata(t)
    elif m("Builtin(_) or TPrim(_)"):
        return t
    elif m("Lit(StrLit(s))"):
        return parse_new_type(m.s, tvars)
    elif m("ListLit([t])"):
        return TArray(conv_type(m.t, tvars, dt))
    else:
        assert isinstance(getattr(t, 'refAtom', None), basestring
                ), 'Unknown type: %s %r' % (type(t), t)
        type_nm = t.refAtom
        destroy_forward_ref(t)
        return type_ref(type_nm)

# EXPRESSIONS

for (cls, op) in {ast.Add: '+', ast.Sub: '-',
                  ast.Mul: '*', ast.FloorDiv: '//', ast.Mod: '%',
                  ast.Div: 'fdiv',
                  ast.Bitand: '&', ast.Bitor: '|', ast.Bitxor: '^',
                  ast.LeftShift: '<<', ast.RightShift: '>>'}.iteritems():
    @expr(cls)
    def binop(e, o=op):
        cs = e.getChildren()
        assert len(cs) == 2
        return builtin_call(o, [conv_expr(cs[0]), conv_expr(cs[1])])

for (cls, sym) in {ast.UnaryAdd: 'positive',
                   ast.UnarySub: 'negate',
                   ast.Not: 'not',
                   ast.Invert: 'invert'}.iteritems():
    @expr(cls)
    def unaop(e, s=sym):
        return builtin_call(s, [conv_expr(e.expr)])
del cls, sym

@expr(ast.And)
def conv_and(e):
    assert len(e.nodes) == 2
    return And(*map(conv_expr, e.nodes))

def unwrap_ast(node):
    if isinstance(node, ast.Const):
        return node.value
    elif isinstance(node, ast.Name):
        return node.name
    elif isinstance(node, ast.Tuple):
        return tuple(map(unwrap_ast, node.nodes))
    elif isinstance(node, ast.List):
        return map(unwrap_ast, node.nodes)
    else:
        assert False, "%s isn't a field spec" % (node,)

def _make_dt(dt_nm, *args, **opts):
    dt_nm = unwrap_ast(dt_nm)
    if dt_nm not in DATATYPES:
        args = map(unwrap_ast, args)
        opts['maker'](dt_nm, *args)
    dt = extrinsic(FormSpec, DATATYPES[dt_nm])
    identifier(dt, namespace=typeNamespace)
    for ctor in dt.ctors:
        identifier(ctor, export=True)
    env(OMNI).decls.dts.append(dt)

@special_assignment('cdecl')
def make_cdecl(nm, t):
    var = GlobalVar()
    identifier(var, nm.value, export=True, namespace=valueNamespace)
    tvars = {}
    t = conv_type(conv_special(t), tvars)
    t.meta.envParam = False
    add_extrinsic(TypeOf, var, t)
    env(OMNI).decls.cdecls.append(var)

@special_assignment('cimport')
def make_cimport(nm, t):
    var = GlobalVar()
    identifier(var, nm.value, export=False, namespace=valueNamespace)
    tvars = {}
    t = conv_type(conv_special(t), tvars)
    t.meta.envParam = False
    add_extrinsic(TypeOf, var, t)
    env(OMNI).decls.cdecls.append(var)

@special_assignment('ADT')
def make_adt(*args):
    _make_dt(*args, **(dict(maker=ADT)))

@special_assignment('DT')
def make_dt(*args):
    _make_dt(*args, **(dict(maker=DT)))

@special_assignment('new_env')
def make_env(nm, t):
    tvars = {}
    e = Env(conv_type(conv_special(t), tvars))
    identifier(e, nm.value, namespace=symbolNamespace, export=True)
    env(OMNI).decls.envs.append(e)

@special_assignment('new_extrinsic')
def make_extrinsic(nm, t):
    tvars = {}
    extr = Extrinsic(conv_type(conv_special(t), tvars))
    identifier(extr, nm.value, namespace=symbolNamespace, export=True)
    env(OMNI).decls.extrinsics.append(extr)

def refs_symbol(e):
    return refs_existing(e.name, namespace=symbolNamespace).target

@special_call('env')
def conv_get_env(environ):
    return GetEnv(refs_symbol(environ))

@special_call('have_env')
def conv_get_env(environ):
    return HaveEnv(refs_symbol(environ))

@special_call('in_env')
def conv_in_env(environ, val, f):
    environ = refs_symbol(environ)
    val = conv_expr(val)
    f = conv_byneed(f)
    return InEnv(environ, val, f)

# TEMP
@special_call('create_ctx')
def conv_create_ctx(environ, val):
    environ = refs_symbol(environ)
    val = conv_expr(val)
    return CreateCtx(environ, val)

@special_call('destroy_ctx')
def conv_free_ctx(environ, ctx):
    environ = refs_symbol(environ)
    ctx = conv_expr(ctx)
    return DestroyCtx(environ, ctx)

@special_call('extrinsic')
def conv_get_extrinsic(ext, e):
    return GetExtrinsic(refs_symbol(ext), conv_expr(e))

@special_call('has_extrinsic')
def conv_has_extrinsic(ext, e):
    return HasExtrinsic(refs_symbol(ext), conv_expr(e))

@special_call('add_extrinsic')
def conv_add_extrinsic(ext, e, val):
    return WriteExtrinsic(refs_symbol(ext), conv_expr(e), conv_expr(val), True)

@special_call('update_extrinsic')
def conv_update_extrinsic(ext, e, val):
    return WriteExtrinsic(refs_symbol(ext), conv_expr(e), conv_expr(val),False)

@special_call('scope_extrinsic')
def conv_scope_extrinsic(ext, f):
    return ScopeExtrinsic(refs_symbol(ext), conv_byneed(f))

@special_call('hint', 'kwargs')
def conv_hint(e, **kwargs):
    e = conv_expr(e)
    insts = {}
    for k, s in kwargs.iteritems():
        insts[k] = s.literal.val
    add_extrinsic(AstHint, e, insts)
    return e

@special_call('anno')
def conv_anno(t, e):
    e = conv_expr(e)
    add_extrinsic(AstType, e.func, t.value)
    return e

def conv_special(e):
    """
    For DT and env argument conversion into types
    """
    c = e.__class__
    if c is ast.Name:
        return type_ref(e.name)
    elif c is ast.Const:
        assert isinstance(e.value, basestring), 'Bad type repr: %s' % e.value
        return E.Lit(StrLit(e.value))
    elif c is ast.Tuple:
        assert len(e.nodes) == 2
        assert isinstance(e.nodes[0], ast.Const)
        nm = e.nodes[0].value
        assert isinstance(nm, basestring), 'Expected field name: %s' % nm
        return E.TupleLit([E.Lit(StrLit(nm)), conv_special(e.nodes[1])])
    else:
        assert False, 'Unexpected %s' % c

def replace_refs(mapping, e):
    # TODO: Need an expression walker
    if isinstance(e, E.Bind):
        if e.target in mapping:
            e.target = mapping[e.target]
    elif isinstance(e, Structured):
        for field in extrinsic(FormSpec, type(e)).fields:
            if not isinstance(field.type, TWeak):
                replace_refs(mapping, getattr(e, extrinsic(Name, field)))
    elif isinstance(e, list):
        # XXX: List of weak refs?
        for i in e:
            replace_refs(mapping, i)
    return e

def extract_ret(b):
    # dumb
    return match(b, "Body([Return(e)])")

SPECIAL_CASES = {
    'identity': lambda r: r(0),
    'tuple2': lambda r: E.TupleLit([r(0), r(1)]),
    'tuple3': lambda r: E.TupleLit([r(0), r(1), r(2)]),
    'tuple4': lambda r: E.TupleLit([r(0), r(1), r(2), r(3)]),
    'tuple5': lambda r: E.TupleLit([r(0), r(1), r(2), r(3), r(4)]),
}

def conv_byneed(f):
    return conv_byneed_rebound(conv_expr(f), [])

def conv_byneed_rebound(f, bs):
    bname = match(f, ('Bind(v)', lambda v: extrinsic(Name, v)),
                     ('_', lambda: None))
    special = bname and SPECIAL_CASES.get(bname)
    if special:
        e = special(lambda i: E.Bind(bs[i]))
    else:
        def rebind_func(params, b):
            return replace_refs(dict(ezip(params, bs)), extract_ret(b))
        e = match(f, ('FuncExpr(Func(params, b))', rebind_func),
                     ('_', lambda: E.Call(f, map(E.Bind, bs))))
    return e

BlockMatchBindings = DT('BlockMatchBindings', ('bindings', {str: Var}))

@inside_scope
def conv_match_case(code, f):
    bs = []
    c = conv_match_try(compiler.parse(code, mode='eval').node, bs, True)
    e = conv_byneed_rebound(f, bs)
    return MatchCase(c, e)

@inside_scope
def conv_block_match_case(m, test, body):
    assert isinstance(test, ast.CallFunc) and isinstance(test.node,
            ast.Name) and test.node.name == m, \
            "Bad m(...) block pat: %s" % (test,)
    args = test.args
    assert len(args) == 1 and isinstance(args[0], ast.Const), "Need m(<str>)"
    pat = args[0].value

    bs = []
    c = conv_match_try(compiler.parse(pat, mode='eval').node, bs, False)
    db = dict(bs)
    assert len(db) == len(bs), "Duplicate names?"
    env(SCOPE).syms[(m, valueNamespace)] = BlockMatchBindings(db)
    return MatchCase(c, Body(conv_stmts_noscope(body)))

@special_call('match')
def conv_match(*args):
    expra = conv_expr(args[0])
    if len(args) == 1:
        return BlockMatch(expra, None) # stupid overload
    argsa = conv_exprs(args[1:])
    casesa = [match(a, ('TupleLit([Lit(StrLit(c)), f])', conv_match_case))
              for a in argsa]
    return Match(expra, casesa)

def conv_match_try(node, bs, asLocalVars):
    recurse = lambda n: conv_match_try(n, bs, asLocalVars)
    if isinstance(node, ast.CallFunc) and isinstance(node.node, ast.Name):
        nm = node.node.name
        args = map(recurse, node.args)
        b = refs_existing(nm)
        assert isinstance(b.target, Ctor), "Can't bind to %s" % (b,)
        return PatCtor(b.target, args)
    elif isinstance(node, ast.Name):
        if node.name == '_':
            return PatWild()
        i = Var()
        if asLocalVars:
            identifier(i, node.name)
            bs.append(i)
        else:
            add_extrinsic(Name, i, node.name)
            bs.append((node.name, i))
        return PatVar(i)
    elif isinstance(node, ast.Const):
        val = node.value
        if isinstance(val, int):
            return PatInt(val)
        elif isinstance(val, str):
            return PatStr(val)
        assert False
    elif isinstance(node, ast.Tuple):
        return PatTuple(map(recurse, node.nodes))
    elif isinstance(node, ast.Or):
        assert False, "yagni?"
        return PatOr(map(recurse, node.nodes))
    elif isinstance(node, ast.And):
        assert False, "yagni?"
        return PatAnd(map(recurse, node.nodes))
    elif isinstance(node, ast.Compare) and node.ops[0][0] == '==':
        assert isinstance(node.expr, ast.Name) and node.expr.name != '_'
        i = Var()
        if asLocalVars:
            identifier(i, node.expr.name)
            bs.append(i)
        else:
            add_extrinsic(Name, i, node.expr.name)
            bs.append((node.expr.name, i))
        return PatCapture(i, recurse(node.ops[0][1]))
    assert False, "Unknown match case: %s" % node

def setup_block_match(m, blockMatch):
    env(SCOPE).blockMatch = (m, blockMatch)
    return []

def cleanup_block_match():
    env(SCOPE).blockMatch = False

SpecialAssignment = DT('SpecialAssignment', ('func', None), ('args', ['a']))

@expr(ast.CallFunc)
def conv_callfunc(e):
    assert not e.star_args and not e.dstar_args
    # omit kw args
    normal_args = filter(lambda a: not isinstance(a, ast.Keyword), e.args)
    if isinstance(e.node, ast.Name):
        kind = e.node.name
        spec = SPECIAL_ASSIGNMENTS.get(kind)
        if spec is not None:
            return SpecialAssignment(spec, e.args)
        spec = SPECIAL_CALLS.get(kind)
        if spec is not None:
            if spec.meta == 'kwargs':
                info = {}
                for arg in e.args:
                    if isinstance(arg, ast.Keyword):
                        info[arg.name] = conv_expr(arg.expr)
                return spec(*normal_args, **info)
            s = spec(*normal_args)
            # hack for match() overload
            if isinstance(s, BlockMatch):
                return SpecialAssignment(setup_block_match, [s])
            return s
    return E.Call(conv_expr(e.node), map(conv_expr, normal_args))

@expr(ast.Compare)
def conv_compare(e):
    assert len(e.ops) == 1
    la = conv_expr(e.expr)
    ra = conv_expr(e.ops[0][1])
    op = e.ops[0][0]
    return builtin_call(op, [la, ra])

@expr(ast.Const)
def conv_const(e):
    v = e.value
    if isinstance(v, int):
        return E.Lit(IntLit(v))
    elif isinstance(v, float):
        return E.Lit(FloatLit(v))
    elif isinstance(v, str):
        return E.Lit(StrLit(v))
    assert False, 'Unknown literal %s' % (e,)

@expr(ast.Dict)
def conv_dict(e):
    return DictLit([E.TupleLit([conv_expr(a), conv_expr(b)])
                    for (a, b) in e.items])

@expr(ast.GenExpr)
def conv_genexpr(e):
    return conv_expr(e.code)

@expr(ast.GenExprInner)
def conv_genexprinner(e):
    assert len(e.quals) == 1
    ea = conv_expr(e.expr)
    comp = e.quals[0]
    assa = fromJust(conv_ass(comp.assign))
    lista = conv_expr(comp.iter if hasattr(comp, 'iter') else comp.list)
    preds = [conv_expr(if_.test) for if_ in comp.ifs]
    return GenExpr(ea, assa, lista, preds)

@expr(ast.Getattr)
def conv_getattr(e):
    expr = conv_expr(e.expr)
    m = match(expr)
    if m('Bind(obj)'):
        # Look for block match's m.<pat var>
        if isinstance(m.obj, BlockMatchBindings):
            nm = e.attrname
            binds = m.obj.bindings
            assert nm in binds, "%s not in %s" % (nm, binds)
            return E.Bind(binds[nm])

    # Resolve field name later
    return E.Attr(expr, e.attrname)

@expr(ast.IfExp)
def conv_ifexp(e):
    return Ternary(conv_expr(e.test), conv_expr(e.then), conv_expr(e.else_))

def extract_arglist(s):
    names = s.argnames[:]
    assert not s.kwargs and not s.varargs and not s.defaults
    args = []
    for nm in names:
        arg = Var()
        identifier(arg, nm)
        args.append(arg)
    return args

@expr(ast.Lambda)
@inside_scope
def conv_lambda(e):
    params = extract_arglist(e)
    body = Body([S.Return(conv_expr(e.code))])
    return FuncExpr(Func(params, body))

@expr(ast.List)
def conv_list(e):
    return ListLit(conv_exprs(e.nodes))

@expr(ast.ListComp)
def conv_listcomp(e):
    return conv_genexprinner(e)

@expr(ast.Name)
def conv_name(e):
    return refs_existing(e.name)

@expr(ast.Or)
def conv_or(e):
    assert len(e.nodes) == 2
    return Or(*conv_exprs(e.nodes))

@expr(ast.Slice)
def conv_slice(e):
    (ea, et) = conv_expr(e.expr)
    sym = 'arraycopy'
    args = [ea]
    lt = ut = ''
    if e.lower:
        (la, lt) = conv_expr(e.lower)
        sym = 'lslice'
        args.append(la)
    if e.upper:
        (ua, ut) = conv_expr(e.upper)
        sym = 'slice' if e.lower else 'uslice'
        args.append(ua)
    return (builtin_call(sym, args), '%s[%s:%s]' % (et, lt, ut))

@expr(ast.Subscript)
def conv_subscript(e):
    assert len(e.subs) == 1
    ea = conv_expr(e.expr)
    sa = conv_expr(e.subs[0])
    return builtin_call('subscript', [ea, sa])

@expr(ast.Tuple)
def conv_tuple(e):
    itemsa = conv_exprs(e.nodes)
    return E.TupleLit(conv_exprs(e.nodes))

# STATEMENTS

@stmt(ast.Assert)
def conv_assert(s):
    fail = conv_expr(s.fail) if s.fail else E.Lit(StrLit('(no desc)'))
    return [Assert(conv_expr(s.test), fail)]

@stmt(ast.Assign)
def conv_assign(s):
    assert len(s.nodes) == 1
    left = s.nodes[0]
    expra = conv_expr(s.expr)
    if isinstance(expra, SpecialAssignment):
        return expra.func(left.name, *expra.args)
    reass = conv_try_reass(left)
    if isJust(reass):
        return [S.Assign(fromJust(reass), expra)]
    else:
        return [S.Defn(conv_ass(left), expra)]

@top_level(ast.Assign)
def conv_top_assign(s):
    assert len(s.nodes) == 1
    left = s.nodes[0]
    expra = conv_expr(s.expr)
    if isinstance(expra, SpecialAssignment):
        if isinstance(left, ast.AssTuple):
            left = left.nodes[0]
        right = expra.args[0]
        if isinstance(right, ast.Const):
            right = right.value
        name = left.name
        assert name == right, "Name mismatch %s, %s" % (name, right)
        expra.func(*expra.args)
    else:
        reass = conv_try_reass(left)
        assert not isJust(reass), "Can't reassign in global scope"
        assert isinstance(left, ast.AssName) and left.name != '_'
        var = GlobalVar()
        identifier(var, left.name, export=True)
        val = match(expra, "Lit(lit)")
        env(OMNI).decls.lits.append(LitDecl(var, val))

@stmt(ast.AssList)
def conv_asslist(s):
    assert False, 'TODO: Unpack list'
    # map(conv_ass, s.nodes)

@stmt(ast.AssTuple)
def conv_asstuple(s):
    for node in s.nodes:
        if getattr(node, 'flags', '') == 'OP_DELETE':
            assert False, 'Del not supported'
        else:
            # TODO
            assert False, 'Unknown AssTuple node: ' + repr(node)
    return []

def op_to_aug(op):
    return {'+=': AugAdd, '-=': AugSubtract, '*=': AugMultiply,
            '//=': AugDivide, '%=': AugModulo}[op]()

@stmt(ast.AugAssign)
def conv_augassign(s):
    lhs = fromJust(conv_try_reass(s.node))
    return [S.AugAssign(op_to_aug(s.op), lhs, conv_expr(s.expr))]

@stmt(ast.Break)
def conv_break(s):
    return [S.Break()]

@stmt(ast.Continue)
def conv_continue(s):
    return [S.Continue()]

def convert_to_voidexpr(e):
    if isinstance(e, InEnv):
        return VoidInEnv(e.env, e.init, convert_to_voidexpr(e.expr))
    return VoidCall(e.func, e.args)

@stmt(ast.Discard)
def conv_discard(s):
    if isinstance(s.expr, ast.Const) and s.expr.value is None:
        return []
    e = conv_callfunc(s.expr)

    # Dumb special case
    if isinstance(e, Stmt):
        assert isinstance(e, WriteExtrinsic)
        return [e]

    return [S.VoidStmt(convert_to_voidexpr(e))]

def conv_ass(s):
    if isinstance(s, ast.AssName):
        if s.name == '_':
            return PatWild()
        assert not isJust(ident_exists(s.name)), \
                "Unexpected reassignment of %s" % (s.name,)
        var = Var()
        identifier(var, s.name, export=is_top_level())
        return PatVar(var)
    elif isinstance(s, ast.AssTuple):
        return PatTuple(map(conv_ass, s.nodes))
    else:
        assert False, "Can't convert %s" % (s,)

def conv_try_reass(s):
    if isinstance(s, (ast.AssName, ast.Name)):
        ref = ident_exists(s.name)
        if isNothing(ref):
            return Nothing()
        return Just(LhsVar(fromJust(ref)))
    elif isinstance(s, (ast.AssAttr, ast.Getattr)):
        expra = conv_expr(s.expr)
        return Just(LhsAttr(expra, s.attrname))
    else:
        return Nothing()

@stmt(ast.For)
@inside_scope
def conv_for(s):
    if s.else_:
        assert False
    return [For(conv_ass(s.assign), conv_expr(s.list),
            conv_stmts_noscope(s.body))]

load_module = None

@top_level(ast.From)
def conv_from(s):
    names = ', '.join(import_names(s.names))
    modname = s.modname
    if modname != 'base':
        assert len(s.names) == 1 and s.names[0][0] == '*', \
                'Only wildcard imports are supported.'
        omni = env(OMNI)
        if modname not in omni.directlyImportedModuleNames:
            omni.directlyImportedModuleNames.add(modname)
            filename = modname.replace('.', '/') + '.py'
            import_module(load_module(filename, omni.loadedDeps))

def import_module(bundle_mod):
    global loaded_module_export_names
    for mod in bundle_mod.root.decls:
        symbols = loaded_module_export_names[mod]
        imports = env(OMNI).imports
        for k in symbols:
            assert k not in imports, "Import clash: %s" % (k,)
            imports[k] = symbols[k]

@stmt(ast.Function)
@top_level(ast.Function)
def conv_function(s):
    astannot = None

    if s.name == 'main':
        astannot = 'void -> int noenv'

    if s.decorators:
        for dec in s.decorators.nodes:
            if isinstance(dec, ast.CallFunc):
                if dec.node.name == 'annot':
                    assert len(dec.args) == 1, "Bad annot: %s" % (dec,)
                    assert isinstance(dec.args[0], ast.Const)
                    astannot = dec.args[0].value
                else:
                    assert False, "Unexpected " + dec.node
    glob = is_top_level()
    var = GlobalVar() if glob else Var()
    assert astannot, "Function %s has no type annot" % s.name
    identifier(var, s.name, export=glob)
    @inside_scope
    def build():
        func = Func([], Body([]))
        add_extrinsic(AstType, func, astannot)
        func.params = extract_arglist(s)
        func.body.stmts = conv_stmts_noscope(s.code)
        return func
    if glob:
        env(OMNI).decls.funcDecls.append(var)
        env(OMNI).funcDefns.append(TopFunc(var, build()))
    else:
        return [S.Defn(PatVar(var), FuncExpr(build()))]

@stmt(ast.If)
def conv_if(s):
    if env(SCOPE).blockMatch:
        m, bm = env(SCOPE).blockMatch
        assert not bm.cases
        bm.cases = [conv_block_match_case(m, t, b) for t, b in s.tests]
        cleanup_block_match()
        return [bm]

    conds = []
    for (test, body) in s.tests:
        conds.append(CondCase(conv_expr(test), Body(conv_stmts(body))))
    if s.else_:
        conds.append(CondCase(builtin_ref('True'), Body(conv_stmts(s.else_))))
    return [S.Cond(conds)]

def import_names(nms):
    return ['%s%s' % (m, (' as ' + n) if n else '') for (m, n) in nms]

@stmt(ast.Import)
def conv_import(s):
    assert False, "This style of import is not supported"

@stmt(ast.Pass)
def conv_pass(s):
    return []

@stmt(ast.Printnl)
def conv_printnl(s):
    assert s.dest is None
    assert len(s.nodes) == 1
    node = s.nodes[0]
    if isinstance(node, ast.Mod):
        assert isinstance(node.right, ast.Tuple)
        args = map(conv_expr, node.right.nodes)
        ops = []
        for bit in re.split(r'(%.)', node.left.value):
            if bit.startswith('%'):
                if bit == '%s':
                    f = 'runtime._print_str'
                elif bit == '%d':
                    f = 'runtime._print_int'
                else:
                    assert False, "Unknown format " + bit
                ops.append(sym_call(f, [args.pop(0)]))
            else:
                lit = E.Lit(StrLit(bit))
                ops.append(sym_call('runtime._print_str', [lit]))
        assert not args, "Format arguments remain: " + args
        ops.append(sym_call('runtime._newline', []))
        return ops
    else:
        return [sym_call('runtime.puts', [conv_expr(node)])]

@top_level(ast.Printnl)
def ignore_debug_print(s):
    pass

@stmt(ast.Return)
def conv_return(s):
    if isinstance(s.value, ast.Const) and s.value.value is None:
        return [S.ReturnNothing()]
    return [S.Return(conv_expr(s.value))]

@inside_scope
def conv_stmts(stmts):
    stmts = concat([conv_stmt(stmt) for stmt in stmts])
    assert not env(SCOPE).blockMatch, "Dangling block match?"
    return stmts

def conv_stmts_noscope(stmts):
    return concat([conv_stmt(stmt) for stmt in stmts])

@stmt(ast.While)
def conv_while(s):
    return [S.While(conv_expr(s.test), Body(conv_stmts(s.body)))]

def setup_builtin_module():
    for name, t in builtins_types.iteritems():
        tvars = {}
        t = parse_new_type(t, tvars)
        if isinstance(t, TFunc):
            t.meta.envParam = False
        builtin = Builtin()
        add_extrinsic(Name, builtin, name)
        add_extrinsic(TypeOf, builtin, t)
        # TODO: Put the TypeVars somewhere too
        BUILTINS[name] = builtin

def convert_file(filename, name, deps):
    assert filename.endswith('.py')
    tops = compiler.parseFile(filename).node.nodes
    decl_mod = Module(t_DT(ModuleDecls), None)
    add_extrinsic(Name, decl_mod, name)
    deps.add(decl_mod)
    omni, scope = ast_envs()
    omni.loadedModules = deps
    def go():
        for name, b in BUILTINS.iteritems():
            scope.syms[(name, valueNamespace)] = b
        map_(conv_top_level, tops)
    in_env(OMNI, omni, lambda: in_env(SCOPE, scope, go))
    decl_mod.root = omni.decls

    bundle = Bundle([decl_mod], [], [])
    bundle_mod = Module(t_DT(Bundle), bundle)
    add_extrinsic(Name, bundle_mod, name + '_bundle')

    if omni.funcDefns:
        unit = CompilationUnit(omni.funcDefns)
        defn_mod = Module(t_DT(CompilationUnit), unit)
        add_extrinsic(Name, defn_mod, name + '_impl')
        bundle.units.append(defn_mod)

    # Resolve imports for missing symbols
    missing = omni.missingRefs
    for key, binds in missing.items():
        if key in omni.imports:
            obj, b = omni.imports[key]
            for bind in binds:
                bind.target = obj
            del missing[key]
    assert not missing, "Symbols not found: " + ', '.join(
                '%s %s' % (t, s) for s, t in missing)

    global loaded_module_export_names
    loaded_module_export_names[decl_mod] = omni.exports
    if filename in RUNTIME_MODULE_OBJS:
        for sym, var in omni.exports.iteritems():
            name, space = sym
            assert space == valueNamespace
            RUNTIME[name] = var

    return bundle_mod

def escape(text):
    return text.replace('\\', '\\\\').replace('"', '\\"')

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
