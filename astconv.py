from atom import *
from base import *
import compiler
from compiler import ast

ScopeContext = DT('ScopeContext', ('indent', int),
                                  ('syms', {(str, bool): object}),
                                  ('prevContext', None))
SCOPE = new_env('SCOPE', ScopeContext)

OmniContext = DT('OmniContext', ('imports', [object]),
                                ('exports', [object]),
                                ('missingRefs', {(str, str): [object]}),
                                ('loadedDeps', set([Module])),
                                ('directlyImportedModuleNames', set([str])))
OMNI = new_env('OMNI', OmniContext)

AstType = new_extrinsic('AstType', Type)
AstHint = new_extrinsic('AstHint', {str: str})

def ast_envs():
    omni = OmniContext({}, {}, {}, set(), set())
    scope = ScopeContext(0, {}, None)
    return omni, scope

def is_top_level():
    return env(SCOPE).indent == 0

loaded_module_export_names = {}

valueNamespace = 'value'
typeNamespace = 'type'
symbolNamespace = 'symbol'
cNamespace = 'C'

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
    if isinstance(v, (Var, Builtin, Ctor)):
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
        new = ScopeContext(prev.indent + 1, {}, prev)
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
    def unknown():
        assert isinstance(getattr(t, 'refAtom', None), basestring
                ), 'Unknown type: %r' % (t,)
        type_nm = t.refAtom
        destroy_forward_ref(t)
        return type_ref(type_nm)
    return match(t,
        ("Builtin(_)", lambda: t),
        ("TPrim(_)", lambda: t),
        ("StrLit(s)", lambda s: parse_new_type(s, tvars)),
        ("ListLit([t])",
            lambda t: TArray(conv_type(t, tvars, dt))),
        ("_", unknown))

# EXPRESSIONS

for (cls, op) in {ast.Add: '+', ast.Sub: '-',
                  ast.Mul: '*', ast.FloorDiv: '//', ast.Mod: '%',
                  ast.Bitand: '&', ast.Bitor: '|', ast.Bitxor: '^',
                  ast.LeftShift: '<<', ast.RightShift: '>>'}.iteritems():
    @expr(cls)
    def binop(e, o=op):
        cs = e.getChildren()
        assert len(cs) == 2
        return symcall(o, [conv_expr(cs[0]), conv_expr(cs[1])])

for (cls, sym) in {ast.UnaryAdd: 'positive',
                   ast.UnarySub: 'negate',
                   ast.Not: 'not',
                   ast.Invert: 'invert'}.iteritems():
    @expr(cls)
    def unaop(e, s=sym):
        return symcall(s, [conv_expr(e.expr)])
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
    return [TopDT(dt)]

@special_assignment('cdecl')
def make_cdecl(nm, t):
    var = Var()
    identifier(var, nm.value, export=True, namespace=cNamespace)
    tvars = {}
    t = conv_type(conv_special(t), tvars)
    add_extrinsic(TypeOf, var, t)
    return [TopCDecl(var)]

@special_assignment('cimport')
def make_cimport(nm, t):
    var = Var()
    identifier(var, nm.value, export=False, namespace=valueNamespace)
    tvars = {}
    t = conv_type(conv_special(t), tvars)
    add_extrinsic(TypeOf, var, t)
    return [TopCDecl(var)]

@special_assignment('ADT')
def make_adt(*args):
    return _make_dt(*args, **(dict(maker=ADT)))

@special_assignment('DT')
def make_dt(*args):
    return _make_dt(*args, **(dict(maker=DT)))

@special_assignment('new_env')
def make_env(nm, t):
    tvars = {}
    e = Env(conv_type(conv_special(t), tvars))
    identifier(e, nm.value, namespace=symbolNamespace, export=True)
    return [TopEnv(e)]

@special_assignment('new_extrinsic')
def make_extrinsic(nm, t):
    tvars = {}
    extr = Extrinsic(conv_type(conv_special(t), tvars))
    identifier(extr, nm.value, namespace=symbolNamespace, export=True)
    return [TopExtrinsic(extr)]

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
        insts[k] = s.val
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
        return E.StrLit(e.value)
    elif c is ast.Tuple:
        assert len(e.nodes) == 2
        assert isinstance(e.nodes[0], ast.Const)
        nm = e.nodes[0].value
        assert isinstance(nm, basestring), 'Expected field name: %s' % nm
        return E.TupleLit([E.StrLit(nm), conv_special(e.nodes[1])])
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

@inside_scope
def conv_match_case(code, f):
    bs = []
    c = conv_match_try(compiler.parse(code, mode='eval').node, bs)
    e = conv_byneed_rebound(f, bs)
    return MatchCase(c, e)

@special_call('match')
def conv_match(*args):
    expra = conv_expr(args[0])
    argsa = conv_exprs(args[1:])
    casesa = [match(a, ('TupleLit([StrLit(c), f])', conv_match_case))
              for a in argsa]
    return Match(expra, casesa)

named_match_cases = {'key': [1], 'named': [1], 'sym': [2, 3],
                     'contains': [1], 'cons': [2], 'all': [2], 'every': [2]}
assert set(named_match_cases) == set(named_match_dispatch)

def conv_match_try(node, bs):
    if isinstance(node, ast.CallFunc) and isinstance(node.node, ast.Name):
        nm = node.node.name
        named_matcher = named_match_cases.get(nm)
        if nm in ('all', 'every'):
            assert len(node.args) == 2 and isinstance(node.args[0], ast.Name)
            i = conv_match_try(node.args[0], bs)
            dummy = []
            assert False, "yagni"
            return symref(nm + '2', [i, conv_match_try(node.args[1], dummy)])
        args = [conv_match_try(n, bs) for n in node.args]
        if named_matcher is not None:
            assert len(args) in named_matcher, (
                   "Bad number of args (%d) to %s matcher" % (len(args), nm))
            assert False, "yagni"
            return symref("%s%d" % (nm, len(args)), args)
        else:
            b = refs_existing(nm)
            assert isinstance(b.target, Ctor), "Can't bind to %s" % (b,)
            return PatCtor(b.target, args)
    elif isinstance(node, ast.Name):
        if node.name == '_':
            return PatWild()
        i = Var()
        identifier(i, node.name)
        bs.append(i)
        return PatVar(i)
    elif isinstance(node, ast.Const):
        val = node.value
        if isinstance(val, int):
            return PatInt(val)
        elif isinstance(val, str):
            return PatStr(val)
        assert False
    elif isinstance(node, ast.Tuple):
        return PatTuple([conv_match_try(n,bs) for n in node.nodes])
    elif isinstance(node, ast.Or):
        assert False, "yagni?"
        return PatOr([conv_match_try(n, bs) for n in node.nodes])
    elif isinstance(node, ast.And):
        assert False, "yagni?"
        return PatAnd([conv_match_try(n, bs) for n in node.nodes])
    elif isinstance(node, ast.Compare) and node.ops[0][0] == '==':
        assert isinstance(node.expr, ast.Name) and node.expr.name != '_'
        i = Var()
        identifier(i, node.expr.name)
        bs.append(i)
        return PatCapture(i, conv_match_try(node.ops[0][1], bs))
    assert False, "Unknown match case: %s" % node


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
            return spec(*normal_args)
    return E.Call(conv_expr(e.node), map(conv_expr, normal_args))

@expr(ast.Compare)
def conv_compare(e):
    assert len(e.ops) == 1
    la = conv_expr(e.expr)
    ra = conv_expr(e.ops[0][1])
    op = e.ops[0][0]
    return symcall(op, [la, ra])

@expr(ast.Const)
def conv_const(e):
    v = e.value
    if isinstance(v, int):
        return E.IntLit(v)
    elif isinstance(v, float):
        return E.FloatLit(v)
    elif isinstance(v, str):
        return E.StrLit(v)
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
    # Resolve field name later
    return E.Attr(conv_expr(e.expr), e.attrname)

@expr(ast.IfExp)
def conv_ifexp(e):
    return E.Ternary(conv_expr(e.test), conv_expr(e.then), conv_expr(e.else_))

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
    return (symcall(sym, args), '%s[%s:%s]' % (et, lt, ut))

@expr(ast.Subscript)
def conv_subscript(e):
    assert len(e.subs) == 1
    ea = conv_expr(e.expr)
    sa = conv_expr(e.subs[0])
    return symcall('subscript', [ea, sa])

@expr(ast.Tuple)
def conv_tuple(e):
    itemsa = conv_exprs(e.nodes)
    return E.TupleLit(conv_exprs(e.nodes))

# STATEMENTS

@stmt(ast.Assert)
def conv_assert(s):
    fail = conv_expr(s.fail) if s.fail else E.StrLit('')
    return [Assert(conv_expr(s.test), fail)]

@stmt(ast.Assign)
@top_level(ast.Assign)
def conv_assign(s):
    assert len(s.nodes) == 1
    left = s.nodes[0]
    expra = conv_expr(s.expr)
    if isinstance(expra, SpecialAssignment):
        if isinstance(left, ast.AssTuple):
            left = left.nodes[0]
        right = expra.args[0]
        if isinstance(right, ast.Const):
            right = right.value
        assert left.name == right, "Name mismatch %s, %s" % (left.name, right)
        return expra.func(*expra.args)

    global_scope = is_top_level()
    reass = conv_try_reass(left)
    if isJust(reass):
        assert not global_scope, "Can't reassign in global scope"
        return [S.Assign(fromJust(reass), expra)]
    else:
        pat = conv_ass(left)
        ass = TopDefn(pat, expra) if global_scope else S.Defn(pat, expra)
        return [ass]

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

@stmt(ast.Discard)
def conv_discard(s):
    if isinstance(s.expr, ast.Const) and s.expr.value is None:
        return []
    e = conv_expr(s.expr)

    # Dumb special case
    if isinstance(e, Stmt):
        assert isinstance(e, WriteExtrinsic)
        return [e]

    return [S.ExprStmt(e)]

def conv_ass(s):
    if isinstance(s, ast.AssName):
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
        global loaded_module_export_names
        omni = env(OMNI)
        if modname not in omni.directlyImportedModuleNames:
            omni.directlyImportedModuleNames.add(modname)
            filename = modname.replace('.', '/') + '.py'
            mod = load_module(filename, omni.loadedDeps)
            symbols = loaded_module_export_names[mod]
            for k in symbols:
                assert k not in omni.imports, "Import clash: %s" % (k,)
                omni.imports[k] = symbols[k]
    return []

@stmt(ast.Function)
@top_level(ast.Function)
def conv_function(s):
    astannot = None
    if s.decorators:
        for dec in s.decorators.nodes:
            if isinstance(dec, ast.CallFunc):
                if dec.node.name == 'annot':
                    assert astannot is None
                    assert isinstance(dec.args[0], ast.Const)
                    astannot = dec.args[0].value
    func = Func([], Body([]))
    var = Var()
    assert astannot, "Function %s has no type annot" % s.name
    add_extrinsic(AstType, func, astannot)
    glob = is_top_level()
    identifier(var, s.name, export=glob)
    @inside_scope
    def rest():
        func.params = extract_arglist(s)
        func.body.stmts = conv_stmts_noscope(s.code)
        return func
    f = (TopDefn if glob else S.Defn)(PatVar(var), FuncExpr(rest()))
    return [f]

@stmt(ast.If)
def conv_if(s):
    conds = []
    for (test, body) in s.tests:
        conds.append(CondCase(conv_expr(test), Body(conv_stmts(body))))
    else_ = Just(Body(conv_stmts(s.else_))) if s.else_ else Nothing()
    return [S.Cond(conds, else_)]

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
    node = s.nodes[0]
    if isinstance(node, ast.Const):
        exprsa = [E.StrLit(node.value+'\n'), E.TupleLit([])]
    elif isinstance(node, ast.Mod):
        format = s.nodes[0].left.value
        exprsa = [E.StrLit(format+'\n'), conv_expr(s.nodes[0].right)]
    else:
        assert False, "Unexpected print form: %s" % s
    return [S.ExprStmt(symcall('printf', exprsa))]

@top_level(ast.Printnl)
def ignore_debug_print(s):
    return []

@stmt(ast.Return)
def conv_return(s):
    if isinstance(s.value, ast.Const) and s.value.value is None:
        return [S.ReturnNothing()]
    return [S.Return(conv_expr(s.value))]

@inside_scope
def conv_stmts(stmts):
    return concat([conv_stmt(stmt) for stmt in stmts])

def conv_stmts_noscope(stmts):
    return concat([conv_stmt(stmt) for stmt in stmts])

@stmt(ast.While)
def conv_while(s):
    return [S.While(conv_expr(s.test), Body(conv_stmts(s.body)))]

def setup_builtin_module():
    for name, t in builtins_types.iteritems():
        t, tvars = make_builtin_scheme(name, t)
        builtin = Builtin()
        add_extrinsic(Name, builtin, name)
        add_extrinsic(TypeOf, builtin, t)
        # TODO: Put the TypeVars somewhere too
        BUILTINS[name] = builtin

def convert_file(filename, name, deps):
    assert filename.endswith('.py')
    tops = compiler.parseFile(filename).node.nodes
    mod = Module(t_DT(CompilationUnit), None)
    add_extrinsic(Name, mod, name)
    deps.add(mod)
    omni, scope = ast_envs()
    omni.loadedModules = deps
    def go():
        for name, b in BUILTINS.iteritems():
            scope.syms[(name, valueNamespace)] = b
        root = []
        for top in tops:
            root += conv_top_level(top)
        return CompilationUnit(root)
    mod.root = in_env(OMNI, omni, lambda: in_env(SCOPE, scope, go))
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
    loaded_module_export_names[mod] = omni.exports
    return mod

def escape(text):
    return text.replace('\\', '\\\\').replace('"', '\\"')

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
