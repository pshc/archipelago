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
                                ('missingRefs', {(str, bool): [object]}),
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
    try:
        b = bind_kind(obj)
    except ValueError:
        assert False, "Can't bind %s %r to %r" % (namespace, obj, name)
    scope.syms[key] = (obj, b)
    if not already_Named:
        add_extrinsic(Name, obj, name)

    omni = env(OMNI)
    missing_binds = omni.missingRefs.get(key)
    if missing_binds is not None:
        for bind in missing_binds:
            bind.binding = b(obj)
        del omni.missingRefs[key]
    if export:
        omni.exports[key] = (obj, b)

def ident_exists(nm, namespace=valueNamespace):
    scope = env(SCOPE)
    key = (nm, namespace)
    while scope is not None:
        o = scope.syms.get(key)
        if o is not None:
            var, b = o
            return Just(b(var))
        scope = scope.prevContext

    ext = env(OMNI).imports.get(key)
    if ext is not None:
        var, b = ext
        return Just(b(var))

    return Nothing()

def refs_existing(nm, namespace=valueNamespace):
    ref = ident_exists(nm, namespace)
    if isJust(ref):
        return Bind(fromJust(ref))
    if namespace == typeNamespace:
        if nm == 'int':
            return TInt()
        if nm == 'str':
            return TStr()
        # Bind() is wrong for types... or is it?
    key = (nm, namespace)
    fwd_ref = Bind(key)
    omni = env(OMNI)
    omni.missingRefs.setdefault(key, []).append(fwd_ref)
    return fwd_ref

def bind_kind(v):
    if isinstance(v, Var):
        return BindVar
    elif isinstance(v, Builtin):
        return BindBuiltin
    elif isinstance(v, Ctor):
        return BindCtor
    elif isinstance(v, (DataType, Ctxt, Extrinsic)):
        return identity
    else:
        raise ValueError("Can't bind to %r" % (v,))

def type_ref(nm):
    return refs_existing(nm, namespace=typeNamespace)

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

def unknown_stmt(node):
    print '??%s %s??' % (node.__class__,
          ', '.join(filter(lambda x: not x.startswith('_'), dir(node))))
    exit(-1)

def unknown_expr(node):
    print '%s?(%s)' % (str(node.__class__),
          ', '.join(filter(lambda x: not x.startswith('_'), dir(node))))

def make_grammar_decorator(default_dispatch):
    dispatch_index = {}
    def decorator(key):
        def inserter(f):
            dispatch_index[key] = f
            return f
        return inserter
    def dispatch(nd, *args):
        return dispatch_index.get(nd.__class__, default_dispatch)(nd, *args)
    return (decorator, dispatch)

def conv_type(t, tvars, dt=None):
    def unknown():
        assert isinstance(getattr(t, 'refAtom', None), basestring
                ), 'Unknown type: %r' % (t,)
        type_nm = t.refAtom
        destroy_forward_ref(t)
        return type_ref(type_nm)
    def type_str(s):
        return in_env(NEWTYPEVARS, None, lambda:
                in_env(TVARS, tvars, lambda: parse_type(s)))
    return match(t,
        ("BindBuiltin(_)", lambda: t),
        ("TPrim(_)", lambda: t),
        ("StrLit(s)", type_str),
        ("ListLit([t])",
            lambda t: TArray(conv_type(t, tvars, dt))),
        ("_", unknown))

(top_level, conv_top_level) = make_grammar_decorator(unknown_stmt)
(stmt, conv_stmt) = make_grammar_decorator(unknown_stmt)
(expr, conv_expr) = make_grammar_decorator(unknown_expr)

def conv_exprs(elist):
    return map(conv_expr, elist)

# EXPRESSIONS

for (cls, op) in {ast.Add: '+', ast.Sub: '-',
                  ast.Mul: '*', ast.Mod: '%',
                  ast.Div: '/', ast.FloorDiv: '//',
                  ast.Bitand: '&', ast.Bitor: '|', ast.Bitxor: '^',
                  ast.LeftShift: '<<', ast.RightShift: '>>'}.iteritems():
    @expr(cls)
    def binop(e, o=op):
        return symcall(o, [conv_expr(e.left), conv_expr(e.right)])

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
    elif isinstance(node, ast.Tuple):
        return tuple(map(unwrap_ast, node.nodes))
    else:
        assert False

def _make_dt(dt_nm, *args, **opts):
    dt_nm = unwrap_ast(dt_nm)
    if dt_nm not in DATATYPES:
        args = map(unwrap_ast, args)
        opts['maker'](dt_nm, *args)
    dt = DATATYPES[dt_nm].__form__
    identifier(dt, namespace=typeNamespace)
    for ctor in dt.ctors:
        identifier(ctor, export=True)
    return [TopDT(dt)]

def make_adt(*args):
    return _make_dt(*args, **(dict(maker=ADT)))
def make_dt(*args):
    return _make_dt(*args, **(dict(maker=DT)))

def make_env(nm, t):
    tvars = {}
    ctxt = Ctxt(conv_type(t, tvars))
    identifier(ctxt, nm, namespace=symbolNamespace, export=True)
    return [TopCtxt(ctxt)]

def make_extrinsic(nm, t):
    tvars = {}
    extr = Extrinsic(conv_type(t, tvars))
    identifier(extr, nm, namespace=symbolNamespace, export=True)
    return [TopExtrinsic(extr)]

def conv_get_env(args):
    assert len(args) == 1
    # XXX Need to deref
    return GetCtxt(args[0])

def conv_in_env(args):
    assert len(args) == 3
    # XXX Need to deref the first arg...
    return InCtxt(*args)

def conv_get_extrinsic(args):
    assert len(args) == 2
    # XXX
    return GetExtrinsic(*args)

def conv_hint(args, kwargs):
    assert len(args) == 1
    e = args[0]
    insts = {}
    for k, s in kwargs.iteritems():
        insts[k] = s.val
    add_extrinsic(AstHint, e, insts)
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
        return StrLit(e.value)
    elif c is ast.Tuple:
        assert len(e.nodes) == 2
        assert isinstance(e.nodes[0], ast.Const)
        nm = e.nodes[0].value
        assert isinstance(nm, basestring), 'Expected field name: %s' % nm
        return TupleLit([StrLit(nm), conv_special(e.nodes[1])])
    else:
        assert False, 'Unexpected %s' % c

def replace_refs(mapping, e):
    # TODO: Need an expression walker
    if isinstance(e, BindVar):
        if e.var in mapping:
            e.var = mapping[e.var]
    elif isinstance(e, Structured):
        for field in e.__form__.fields:
            if not isinstance(field.type, TWeak):
                replace_refs(mapping, getattr(e, extrinsic(Name, field)))
    elif isinstance(e, list):
        # XXX: List of weak refs?
        for i in e:
            replace_refs(mapping, i)
    return e

def extract_ret(b):
    # dumb
    return match(b, ("Body([Return(e)])", identity))

SPECIAL_CASES = {
    'identity': lambda r: r(0),
    'tuple2': lambda r: TupleLit([r(0), r(1)]),
    'tuple3': lambda r: TupleLit([r(0), r(1), r(2)]),
    'tuple4': lambda r: TupleLit([r(0), r(1), r(2), r(3)]),
    'tuple5': lambda r: TupleLit([r(0),r(1),r(2),r(3),r(4)]),
}

@inside_scope
def conv_match_case(code, f):
    bs = []
    c = conv_match_try(compiler.parse(code, mode='eval').node, bs)
    special = SPECIAL_CASES.get(match(f, ('BindBuiltin(nm)', identity),
                                         ('_', lambda: None)))
    if special:
        e = special(lambda i: bs[i])
    else:
        e = match(f, ('FuncExpr(Func(params, b))', lambda params, b:
                         replace_refs(dict(zip(params, bs)), extract_ret(b))),
                     ('_', lambda: Call(f, [Bind(BindVar(b)) for b in bs])))
    return MatchCase(c, e)

def conv_match(args):
    expra = args.pop(0)
    casesa = [match(a, ('TupleLit([StrLit(c), f])', conv_match_case))
              for a in args]
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
            assert isinstance(b.binding, BindCtor), "Can't bind to %s" % (b,)
            return PatCtor(b.binding.ctor, args)
    elif isinstance(node, ast.Name):
        if node.name == '_':
            return PatWild()
        i = Var()
        identifier(i, node.name)
        bs.append(i)
        return PatVar(i)
    elif isinstance(node, ast.Const):
        va, vt = conv_const(node)
        return va
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


SpecialCallForm = DT('SpecialCall', ('name', str), ('args', [object]))
special_call_forms = {
        'ADT': make_adt, 'DT': make_dt,
        'new_env': make_env,
        'new_extrinsic': make_extrinsic,
}
extra_call_forms = {
        'match': conv_match,
        'env': conv_get_env, 'in_env': conv_in_env,
        'extrinsic': conv_get_extrinsic,
        'hint': conv_hint,
}

@expr(ast.CallFunc)
def conv_callfunc(e):
    assert not e.star_args and not e.dstar_args
    if isinstance(e.node, ast.Name):
        kind = e.node.name
        if kind in ('DT', 'ADT'):
            return SpecialCallForm(kind, e.args)
        elif kind in ('new_env', 'new_extrinsic'):
            if e.args and isinstance(e.args[0], ast.Const):
                name = e.args[0].value
                if isinstance(name, basestring):
                    assert len(e.args) == 2
                    t = conv_special(e.args[1])
                    return SpecialCallForm(kind, [name, t])
    # omit kw args
    argsa = map(conv_expr,
            filter(lambda a: not isinstance(a, ast.Keyword), e.args))
    if isinstance(e.node, ast.Name):
        f = extra_call_forms.get(e.node.name)
        if f:
            if e.node.name == 'hint':
                # collect kw args for this special form
                info = {}
                for arg in e.args:
                    if isinstance(arg, ast.Keyword):
                        info[arg.name] = conv_expr(arg.expr)
                return f(argsa, info)
            return f(argsa)
        elif e.node.name == 'char':
            c = match(argsa[0], ('StrLit(s)', identity))
            assert len(c) == 1
            return CharLit(c)
    fa = conv_expr(e.node)
    return Call(conv_expr(e.node), argsa)

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
        return IntLit(v)
    elif isinstance(v, str):
        return StrLit(v)
    assert False, 'Unknown literal %s' % (e,)

@expr(ast.Dict)
def conv_dict(e):
    return DictLit([TupleLit([conv_expr(a), conv_expr(b)])
                    for (a, b) in e.items])

@expr(ast.GenExpr)
def conv_genexpr(e):
    return conv_expr(e.code)

@expr(ast.GenExprInner)
def conv_genexprinner(e):
    assert len(e.quals) == 1
    ea = conv_expr(e.expr)
    comp = e.quals[0]
    # TODO: Ought to be a pattern. Unify?
    assa = fromJust(conv_ass(comp.assign))
    lista = conv_expr(comp.iter if hasattr(comp, 'iter') else comp.list)
    preds = [conv_expr(if_.test) for if_ in comp.ifs]
    return GenExpr(ea, assa, lista, preds)

@expr(ast.Getattr)
def conv_getattr(e):
    return Attr(conv_expr(e.expr), refs_existing(e.attrname))

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
    body = Body([Return(conv_expr(e.code))])
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
    return Or(conv_exprs(e.nodes))

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
    return TupleLit(conv_exprs(e.nodes))

# STATEMENTS

@stmt(ast.Assert)
def conv_assert(s):
    fail = conv_expr(s.fail) if s.fail else StrLit('')
    return [Assert(conv_expr(s.test), fail)]

@stmt(ast.Assign)
@top_level(ast.Assign)
def conv_assign(s):
    assert len(s.nodes) == 1
    left = s.nodes[0]
    expra = conv_expr(s.expr)
    if isinstance(expra, SpecialCallForm):
        # s.nodes[0] is usually the same as args[0], skipped for now
        return special_call_forms[expra.name](*expra.args)
    # XXX Distinguish between defn and binding earlier
    m = match(conv_ass(left))
    global_scope = is_top_level()
    if m('Just(lefta)'):
        assert not global_scope
        lefta = m.arg
        m.ret(Assign(lefta, expra))
    else:
        assert isinstance(left, ast.AssName), "Simple assignment only"
        var = Var()
        identifier(var, left.name, export=global_scope)
        m.ret(TopDefn(var, expra) if global_scope else Defn(var, expra))
    ass = m.result()
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
            '/=': AugDivide, '%=': AugModulo}[op]()

@stmt(ast.AugAssign)
def conv_augassign(s):
    lhs = fromJust(conv_ass(s.node))
    return [AugAssign(op_to_aug(s.op), lhs, conv_expr(s.expr))]

@stmt(ast.Break)
def conv_break(s):
    return [Break()]

@stmt(ast.Continue)
def conv_continue(s):
    return [Continue()]

@stmt(ast.Discard)
def conv_discard(s):
    if isinstance(s.expr, ast.Const) and s.expr.value is None:
        return []
    return [ExprStmt(conv_expr(s.expr))]

# ast lhs -> Maybe Lhs
def conv_ass(s):
    if isinstance(s, (ast.AssName, ast.Name)):
        ref = ident_exists(s.name)
        if isJust(ref):
            assert isinstance(ref.just, BindVar)
            ref = Just(LhsVar(ref.just.var))
        return ref
    elif isinstance(s, ast.AssTuple):
        return Just(LhsTuple([conv_ass(n) for n in s.nodes]))
    elif isinstance(s, ast.AssAttr):
        expra = conv_expr(s.expr)
        attra = ident_ref(s.attrname, True, export=False)
        return Just(LhsAttr([expra, attra]))
    else:
        assert False, "Can't convert %s" % (s,)

@stmt(ast.For)
@inside_scope
def conv_for(s):
    if s.else_:
        assert False
    return [For(conv_ass(s.assign), conv_expr(s.list),
            conv_stmts_noscope(s.body))]

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
            mod = load_module_dep(modname.replace('.', '/') + '.py',
                    omni.loadedDeps)
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
    @inside_scope
    def rest():
        func.params = extract_arglist(s)
        func.body.stmts = conv_stmts_noscope(s.code)
        return func
    var = Var()
    glob = is_top_level()
    identifier(var, s.name, export=glob)
    f = (TopDefn if glob else Defn)(var, FuncExpr(rest()))
    assert astannot, "Function %r has no type annot" % f
    add_extrinsic(AstType, func, astannot)
    return [f]

@stmt(ast.If)
def conv_if(s):
    conds = []
    for (test, body) in s.tests:
        conds.append(Case(conv_expr(test), conv_stmts(body)))
    else_ = Just(Body(conv_stmts(s.else_))) if s.else_ else Nothing()
    return [Cond(conds, else_)]

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
        exprsa = [StrLit(node.value+'\n'), TupleLit([])]
    elif isinstance(node, ast.Mod):
        format = s.nodes[0].left.value
        exprsa = [StrLit(format+'\n'), conv_expr(s.nodes[0].right)]
    else:
        assert False, "Unexpected print form: %s" % s
    return [ExprStmt(symcall('printf', exprsa))]

@stmt(ast.Return)
def conv_return(s):
    if isinstance(s.value, ast.Const) and s.value.value is None:
        return [ReturnNothing()]
    return [Return(conv_expr(s.value))]

@inside_scope
def conv_stmts(stmts):
    return concat([conv_stmt(stmt) for stmt in stmts])

def conv_stmts_noscope(stmts):
    return concat([conv_stmt(stmt) for stmt in stmts])

@stmt(ast.While)
def conv_while(s):
    return [While(conv_expr(s.test), Body(conv_stmts(s.body)))]

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
            scope.syms[(name, valueNamespace)] = (b, BindBuiltin)
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
                bind.binding = b(obj)
            del missing[key]
    assert not missing, "Symbols not found: " + ', '.join(
                ('type %s' if t else '%s') % s for s, t in missing)
    global loaded_module_export_names
    loaded_module_export_names[mod] = omni.exports
    return mod

def escape(text):
    return text.replace('\\', '\\\\').replace('"', '\\"')

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
