from atom import *
from base import *
import compiler
from compiler import ast

ScopeContext = DT('ScopeContext', ('indent', int),
                                  ('syms', {(str, bool): object}),
                                  ('prevContext', None))
SCOPE = new_context('SCOPE', ScopeContext)

OmniContext = DT('OmniContext', ('imports', [object]),
                                ('exports', [object]),
                                ('missingRefs', {(str, bool): [object]}),
                                ('loadedDeps', set([Module])))
OMNI = new_context('OMNI', OmniContext)

def ast_contexts():
    omni = OmniContext({}, {}, {}, set())
    scope = ScopeContext(-1, {}, None)
    return omni, scope

loaded_module_export_names = {}

def identifier(obj, name, is_type=False,
               permissible_nms=frozenset(), export=False):
    scope = context(SCOPE)
    key = (name, is_type)
    kind = 'type' if is_type else 'term'
    assert name in permissible_nms or key not in scope.syms, (
            "Symbol '%s' already in %s context\n%s" % (
            name, kind,
            '\n'.join('\t'+str(s) for s, t in scope.syms if t == is_type)))
    try:
        b = bind_kind(obj)
    except ValueError:
        assert False, "Can't bind %s %r to %r" % (kind, obj, name)
    scope.syms[key] = (obj, b)
    add_extrinsic(Name, obj, name)

    omni = context(OMNI)
    missing_binds = omni.missingRefs.get(key)
    if missing_binds is not None:
        for bind in missing_binds:
            bind.binding = b(obj)
        del omni.missingRefs[key]
    if export:
        omni.exports[key] = obj

def ident_exists(nm, is_type=False):
    scope = context(SCOPE)
    key = (nm, is_type)
    while scope is not None:
        o = scope.syms.get(key)
        if o is not None:
            var, b = o
            return Just(b(var))
        scope = scope.prevContext
    return Nothing()

def refs_existing(nm, is_type=False):
    ref = ident_exists(nm, is_type=is_type)
    if isJust(ref):
        return fromJust(ref)
    if is_type:
        if nm == 'int':
            return TInt()
        if nm == 'str':
            return TStr()
        # Bind() is wrong for types... or is it?
    key = (nm, is_type)
    fwd_ref = Bind(key)
    omni = context(OMNI)
    omni.missingRefs.setdefault(key, []).append(fwd_ref)
    return fwd_ref

def bind_kind(v):
    if isinstance(v, Var):
        return BindVar
    elif isinstance(v, Builtin):
        return BindBuiltin
    elif isinstance(v, Func):
        return BindFunc
    elif isinstance(v, Field):
        return BindField
    elif isinstance(v, Ctor):
        return BindCtor
    elif isinstance(v, DTStmt):
        return BindDT
    else:
        raise ValueError("Can't bind to %r" % (v,))

def type_ref(nm):
    return refs_existing(nm, is_type=True)

def destroy_forward_ref(ref):
    if not isinstance(ref.refAtom, basestring):
        return
    omni = context(OMNI)
    for t in (True, False):
        key = (ref.refAtom, t)
        refs = omni.missingRefs.get(key, [])
        if ref in refs:
            refs.remove(ref)
            if not refs:
                del omni.missingRefs[key]
            return
    assert False, "Couldn't find forward ref for destruction"

def symcall(name, subs):
    assert name in boot_sym_names, '%s not a boot symbol' % (name,)
    return Call(Bind(BindBuiltin(symref(name))), subs)

def inside_scope(f):
    def new_scope(*args, **kwargs):
        prev = context(SCOPE)
        new = ScopeContext(prev.indent + 1, {}, prev)
        return in_context(SCOPE, new, lambda: f(*args, **kwargs))
    new_scope.__name__ = f.__name__
    return new_scope

def unknown_stmt(node):
    print '??%s %s??' % (node.__class__,
          ', '.join(filter(lambda x: not x.startswith('_'), dir(node))))

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
        if len(s) == 1:
            tvar = tvars.get(s)
            if not s:
                tvar = TypeVar()
                add_extrinsic(Name, tvar, s)
                tvars[s] = tvar
            return TVar(tvar)
        if '(' in s and s[-1] == ')':
            ctor, p, args = s[:-1].partition('(')
            return TApply(type_str(ctor), map(type_str, args.split(',')))
        return type_ref(s)
    return match(t,
        ("BindBuiltin(_)", lambda: t),
        ("BindDT(_)", lambda: t),
        ("TStr() or TInt()", lambda: t),
        ("StrLit(s)", type_str),
        ("ListLit([t])",
            lambda t: TApply(type_ref('List'), [conv_type(t, tvars, dt)])),
        ("_", unknown))

(stmt, conv_stmt) = make_grammar_decorator(unknown_stmt)
(expr, conv_expr) = make_grammar_decorator(unknown_expr)

def conv_exprs(elist):
    return map(conv_expr, elist)

# EXPRESSIONS

add_sym('binaryop')
add_sym('unaryop')

for (cls, op) in {ast.Add: '+', ast.Sub: '-',
                  ast.Mul: '*', ast.Mod: '%',
                  ast.Div: '/', ast.FloorDiv: '//',
                  ast.Bitand: '&', ast.Bitor: '|', ast.Bitxor: '^',
                  ast.LeftShift: '<<', ast.RightShift: '>>'}.iteritems():
    add_sym(op)
    @expr(cls)
    def binop(e, o=op):
        return symcall(o, [conv_expr(e.left), conv_expr(e.right)])

for (cls, (op, sym)) in {ast.UnaryAdd: ('+', 'positive'),
                         ast.UnarySub: ('-', 'negate'),
                         ast.Not: ('not ', 'not'),
                         ast.Invert: ('~', 'invert')}.iteritems():
    add_sym(sym)
    @expr(cls)
    def unaop(e, o=op, s=sym):
        return symcall(s, [conv_expr(e.expr)])
del cls, op

@expr(ast.And)
def conv_and(e):
    assert len(e.nodes) == 2
    return And(*map(conv_expr, e.nodes))

def make_adt(left, args):
    adt_nm = match(args.pop(0), ('StrLit(nm)', identity))
    ctors = []
    adt = DTStmt(ctors, [])
    identifier(adt, adt_nm, is_type=True, export=True)
    tvars = {}
    field_nms = set()
    while args:
        ctor_nm = match(args.pop(0), ('StrLit(s)', identity))
        members = []
        while args:
            nm, t = match(args[0], ('StrLit(_)', lambda: (None, None)),
                                   ('TupleLit([StrLit(nm), t])', tuple2))
            if nm is None:
                break
            field = Field(conv_type(t, tvars, dt=adt))
            identifier(field, nm, permissible_nms=field_nms)
            field_nms.add(nm)
            members.append(field)
            args.pop(0)
        ctor = Ctor(members)
        identifier(ctor, ctor_nm, export=True)
        ctors.append(ctor)
    adt.tvars = tvars.values()
    return [adt]


add_sym('DT')
add_sym('ctor')
add_sym('field')
def make_dt(left, args):
    (nm, fs) = match(args, ('cons(StrLit(dt_nm), all(nms, TupleLit('
                            '[StrLit(nm), t])))', tuple2))
    fields = []
    ctor = Ctor(fields)
    identifier(ctor, nm, export=True)
    dt = DTStmt([ctor], [])
    identifier(dt, nm, is_type=True, export=True)
    tvars = {}
    for fnm, t in fs:
        field = Field(conv_type(t, tvars, dt=dt))
        identifier(field, fnm)
        fields.append(field)
    dt.tvars = tvars.values()
    return [dt]

def make_context(left, args):
    nm, t = match(args, ('cons(nm==StrLit(_), cons(t, _))', tuple2))
    tvars = {}
    ctxt = Ctxt(conv_type(t, tvars))
    #identifier(ctxt, nm, export=True)
    return [CtxtStmt(ctxt)]

def conv_get_context(args):
    assert len(args) == 1
    # XXX Need to deref
    return GetCtxt(args[0])

def conv_in_context(args):
    assert len(args) == 3
    # XXX Need to deref the first arg...
    return InCtxt(*args)

def make_extrinsic(left, args):
    nm, t = match(args, ('[nm==StrLit(_), t]', tuple2))
    tvars = {}
    extrinsic = Extrinsic(conv_type(t, tvars))
    return [ExtrinsicStmt(extrinsic)]

def conv_special(e):
    """
    For DT and context argument conversion into types
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
    # XXX: Need to walk expression, replacing bindings.
    print 'WARNING: replace_refs not implemented'
    return e

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
        e = match(f, ('Lambda(params, e)', lambda params, e:
                         replace_refs(dict(zip(params, bs)), e)),
                     ('_', lambda: Call(f, [BindVar(b) for b in bs])))
    return MatchCase(c, e)

add_sym('match')
add_sym('case')
def conv_match(args):
    expra = args.pop(0)
    casesa = [match(a, ('TupleLit([StrLit(c), f])', conv_match_case))
              for a in args]
    return Match(expra, casesa)

named_match_cases = {'sized': [1, 2], 'key': [1, 2], 'named': [1, 2],
                     'subs': [1], 'sym': [2, 3],
                     'contains': [1], 'cons': [2], 'all': [2], 'every': [2]}
assert set(named_match_cases) == set(named_match_dispatch)

for nm, ns in named_match_cases.iteritems():
    for n in ns:
        add_sym('%s%d' % (nm, n))
def conv_match_try(node, bs):
    if isinstance(node, ast.CallFunc) and isinstance(node.node, ast.Name):
        nm = node.node.name
        named_matcher = named_match_cases.get(nm)
        if nm in ('all', 'every'):
            assert len(node.args) == 2 and isinstance(node.args[0], ast.Name)
            i = conv_match_try(node.args[0], bs)
            dummy = []
            return symref(nm + '2', [i, conv_match_try(node.args[1], dummy)])
        args = [conv_match_try(n, bs) for n in node.args]
        if named_matcher is not None:
            assert len(args) in named_matcher, (
                   "Bad number of args (%d) to %s matcher" % (len(args), nm))
            return symref("%s%d" % (nm, len(args)), args)
        else:
            return PatCtor(refs_existing(nm), [args])
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
        return symref('or', [int_len(node.nodes)]
                            + [conv_match_try(n, bs) for n in node.nodes])
    elif isinstance(node, ast.And):
        return symref('and', [int_len(node.nodes)]
                             + [conv_match_try(n, bs) for n in node.nodes])
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
        'new_context': make_context,
        'new_extrinsic': make_extrinsic,
}
extra_call_forms = {
        'match': conv_match,
        'context': conv_get_context, 'in_context': conv_in_context,
}

@expr(ast.CallFunc)
def conv_callfunc(e):
    assert not e.star_args and not e.dstar_args
    if isinstance(e.node, ast.Name) and e.node.name in special_call_forms:
        return SpecialCallForm(e.node.name, map(conv_special, e.args))
    argsa = map(conv_expr, e.args)
    if isinstance(e.node, ast.Name):
        f = extra_call_forms.get(e.node.name)
        if f:
            return f(argsa)
        elif e.node.name == 'char':
            c = match(argsa[0], ('StrLit(s)', identity))
            assert len(c) == 1
            return CharLit(c)
    fa = conv_expr(e.node)
    return Call(conv_expr(e.node), argsa)

map(lambda s: add_sym(s), ['<', '>', '==', '!=', '<=', '>='])
map(add_sym, ['is', 'is not', 'in', 'not in'])
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

add_sym('genexpr')
@expr(ast.GenExprInner)
def conv_genexprinner(e):
    assert len(e.quals) == 1
    ea = conv_expr(e.expr)
    comp = e.quals[0]
    # TODO: Ought to be a pattern. Unify?
    assa = conv_ass(comp.assign)
    lista = conv_expr(comp.iter if hasattr(comp, 'iter') else comp.list)
    preds = [conv_expr(if_.test) for if_ in comp.ifs]
    return GenExpr(ea, assa, lista, preds)

add_sym('attr')
@expr(ast.Getattr)
def conv_getattr(e):
    (ea, et) = conv_expr(e.expr)
    nm = e.attrname
    return (symref('attr', [ea, refs_existing(nm)]), '%s.%s' % (et, nm))

add_sym('?:')
@expr(ast.IfExp)
def conv_ifexp(e):
    (ca, ct) = conv_expr(e.test)
    (ta, tt) = conv_expr(e.then)
    (fa, ft) = conv_expr(e.else_)
    return (symref('?:', [ca, ta, fa]), '%s if %s else %s' % (tt, ct, ft))

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
    return Lambda(extract_arglist(e), conv_expr(e.code))

@expr(ast.List)
def conv_list(e):
    return ListLit(conv_exprs(e.nodes))

@expr(ast.ListComp)
def conv_listcomp(e):
    return conv_genexprinner(e)

@expr(ast.Name)
def conv_name(e):
    return refs_existing(e.name)

add_sym('or')
@expr(ast.Or)
def conv_or(e):
    assert len(e.nodes) == 2
    return Or(conv_exprs(e.nodes))

map(add_sym, ['arraycopy', 'slice', 'lslice', 'uslice'])
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

add_sym('subscript')
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

map(add_sym, ['defn', '='])
@stmt(ast.Assign)
def conv_assign(s):
    assert len(s.nodes) == 1
    expra = conv_expr(s.expr)
    if isinstance(expra, SpecialCallForm):
        return special_call_forms[expra.name](s.nodes[0], expra.args)
    lefta = conv_ass(s.nodes[0])
    # XXX Distinguish between defn and binding earlier
    if isJust(lefta):
        ass = Assign(fromJust(lefta), expra)
    else:
        global_scope = context(SCOPE).indent == 0
        var = identifier(Var(), nm, export=global_scope)
        ass = Defn(var, expra)
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
    return [AugAssign(op_to_aug(s.op), conv_lhs(s.node), conv_expr(s.expr))]

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

def conv_ass(s):
    if isinstance(s, ast.AssName):
        # LhsVar
        return ident_exists(s.name)
    elif isinstance(s, ast.AssTuple):
        return Just(LhsTuple([conv_ass(n) for n in s.nodes]))
    elif isinstance(s, ast.AssAttr):
        expra = conv_expr(s.expr)
        attra = ident_ref(s.attrname, True, export=False)
        return Just(LhsAttr([expra, attra]))
    else:
        # ???
        return Just(conv_expr(s))

@stmt(ast.For)
@inside_scope
def conv_for(s):
    if s.else_:
        assert False
    return [For(conv_ass(s.assign), conv_expr(s.list),
            conv_stmts_noscope(s.body))]

@stmt(ast.From)
def conv_from(s):
    names = ', '.join(import_names(s.names))
    if s.modname != 'base':
        assert len(s.names) == 1 and s.names[0][0] == '*', \
                'Only wildcard imports are supported.'
        global loaded_module_export_names
        omni = context(OMNI)
        mod = load_module_dep(s.modname.replace('.', '/') + '.py',
                omni.loadedDeps)
        symbols = loaded_module_export_names[mod]
        omni.imports.update(symbols)
    return []

add_sym('local')
@stmt(ast.Function)
def conv_function(s):
    export = True
    for dec in s.decorators or []:
        e = conv_expr(dec)
        if match(e, ("somekindofreference(nm)", lambda nm: nm == 'local'),
                    ("_", lambda: False)):
            export = False
    func = Func([], [])
    identifier(func, s.name, export=export)
    @inside_scope
    def rest():
        func.params = extract_arglist(s)
        func.body = conv_stmts_noscope(s.code)
        return func
    return [rest()]

@stmt(ast.If)
def conv_if(s):
    conds = []
    for (test, body) in s.tests:
        conds.append(Case(conv_expr(test), conv_stmts(body)))
    else_ = Just(conv_stmts(s.else_)) if s.else_ else Nothing()
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
    return [While(conv_expr(s.test), conv_stmts(s.body))]

# Shouldn't this be a context or something?
BUILTINS = {}

def setup_builtin_module():
    omni, scope = ast_contexts()
    def go():
        is_type = False
        for name in builtins_types:
            builtin = Builtin()
            BUILTINS[(name, is_type)] = (builtin, BindBuiltin)
    roots = in_context(OMNI, omni, lambda: in_context(SCOPE, scope, go))

def convert_file(filename, name, deps):
    assert filename.endswith('.py')
    if not BUILTINS:
        setup_builtin_module()
    stmts = compiler.parseFile(filename).node.nodes
    mod = Module(name, None, [])
    deps.add(mod)
    omni, scope = ast_contexts()
    omni.loadedModules = deps
    def go():
        scope.syms.update(BUILTINS)
        conv_stmts(stmts)
    mod.roots = in_context(OMNI, omni, lambda: in_context(SCOPE, scope, go))
    # Resolve imports for missing symbols
    missing = omni.missingRefs
    for key, binds in missing.items():
        if key in omni.imports:
            obj = omni.imports[key]
            b = bind_kind(obj)
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
