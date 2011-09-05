from atom import *
from base import *
import compiler
from compiler import ast

ScopeContext = DT('ScopeContext', ('indent', int),
                                  ('syms', {(str, bool): Atom}),
                                  ('prevContext', None))
SCOPE = new_context('SCOPE', ScopeContext)

OmniContext = DT('OmniContext', ('imports', [Atom]),
                                ('exports', [Atom]),
                                ('missingRefs', {(str, bool): [Atom]}),
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

def ident_ref(nm, create, is_type=False, export=False):
    scope = context(SCOPE)
    key = (nm, is_type)
    while scope is not None:
        o = scope.syms.get(key)
        if o is not None:
            var, b = o
            return Just(b(var))
        scope = scope.prevContext
    return False
    if create:
        return Nothing()
    fwd_ref = Bind(None)
    omni = context(OMNI)
    omni.missingRefs.setDefault(key, []).append(fwd_ref)
    return Just(fwd_ref)

def bind_kind(v):
    if isinstance(v, Var):
        return BindVar
    elif isinstance(v, Builtin):
        return BindBuiltin
    elif isinstance(v, Func):
        return BindFunc
    elif isinstance(v, Ctor):
        return BindCtor
    else:
        raise ValueError("Can't bind to %r" % (v,))

def refs_existing(nm):
    return ident_ref(nm, False)

def type_ref(nm):
    return ident_ref(nm, False, is_type=True)

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

add_sym('typeapply')
def type_apply(tref, args):
    return symref('typeapply', [tref, int_len(args)] + args)

def conv_type(t, tvars, dt=None):
    def unknown():
        assert isinstance(getattr(t, 'refAtom', None), basestring
                ), 'Unknown type: %r' % (t,)
        type_nm = t.refAtom
        destroy_forward_ref(t)
        return type_ref(type_nm)
    def type_str(s):
        if len(s) == 1:
            if s not in tvars:
                tvars[s] = symref('typevar', [symname(s)])
            return ref_(tvars[s])
        if '(' in s and s[-1] == ')':
            ctor, p, args = s[:-1].partition('(')
            return type_apply(type_str(ctor), map(type_str, args.split(',')))
        return type_ref(s)
    return match(t,
        ("key('str' or 'int')", lambda: t),
        ("BindBuiltin(_)", lambda: t),
        ("BindDT(_)", lambda: t),
        ("StrLit(s)", type_str),
        ("key('listlit', sized(cons(lt, _)))",
            lambda t: type_apply(type_ref('List'), [conv_type(t, tvars, dt)])),
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
    add_sym(op, extra_prop='binaryop', extra_str=op.replace('//','/'))
    @expr(cls)
    def binop(e, o=op):
        return symcall(o, [conv_expr(e.left), conv_expr(e.right)])

for (cls, (op, sym)) in {ast.UnaryAdd: ('+', 'positive'),
                         ast.UnarySub: ('-', 'negate'),
                         ast.Not: ('not ', 'not'),
                         ast.Invert: ('~', 'invert')}.iteritems():
    add_sym(sym, extra_prop='unaryop', extra_str=op.replace('not ', '!'))
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
    (nm, fs) = match(args, ('cons(Str(dt_nm, _), all(nms, key("tuplelit", \
                             sized(cons(Str(nm, _), cons(t, _))))))', tuple2))
    fields = []
    dtsubs = [identifier('ctor', nm, fields, export=True)]
    fa = identifier('DT', nm, dtsubs, is_type=True, export=True)
    tvars = {}
    fields += [identifier('field', fnm,
                          [symref('type', [conv_type(t, tvars, dt=fa)])])
               for (fnm, t) in fs]
    dtsubs += tvars.values()
    return ([fa], '%s = DT(%s)' % (nm, ', '.join(f for f, s in fs)))

def make_context(left, args):
    nm, t = match(args, ('cons(nm==StrLit(_), cons(t, _))', tuple2))
    tvars = {}
    #ctxt = identifier('CTXT', nm, [ta], export=True)
    return [CtxtStmt(Ctxt(conv_type(t, tvars)))]

def conv_get_context(args):
    assert len(args) == 1
    # XXX Need to deref
    return GetCtxt(args[0])

def conv_in_context(args):
    assert len(args) == 3
    # XXX Need to deref the first arg...
    return InCtxt(*args)

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
    ra = getattr(e, 'refAtom', None)
    if ra in mapping:
        e.refAtom = mapping[ra]
    for sub in e.subs:
        replace_refs(mapping, sub)
    return e

SPECIAL_CASES = {
    'identity': lambda r: r(0),
    'tuple2': lambda r: symref('tuplelit', [int_(2), r(0), r(1)]),
    'tuple3': lambda r: symref('tuplelit', [int_(3), r(0), r(1), r(2)]),
    'tuple4': lambda r: symref('tuplelit', [int_(4), r(0), r(1), r(2), r(3)]),
    'tuple5': lambda r: symref('tuplelit', [int_(5),r(0),r(1),r(2),r(3),r(4)]),
}

@inside_scope
def conv_match_case(code, f):
    bs = []
    c = conv_match_try(compiler.parse(code, mode='eval').node, bs)
    ref = lambda s: ref_(s)
    special = SPECIAL_CASES.get(getattr(f, 'refAtom', None))
    if special:
        e = special(lambda i: ref(bs[i]))
    else:
        e = match(f, ('key("lambda", sized(every(args, arg==key("var")), \
                                           cons(e, _)))',
                      lambda args, e: replace_refs(dict(zip(args, bs)), e)),
                     ('_', lambda: symref('call', [f, int_len(bs)]
                                          + [ref(b) for b in bs])))
    return symref('case', [c, e])

add_sym('match')
add_sym('case')
def conv_match(args):
    expra = args.pop(0)
    casesa = [match(a, ('key("tuplelit", sized(cons(Str(c, _), cons(f, _))))',
                        conv_match_case)) for a in args]
    return symref('match', [expra] + casesa)

named_match_cases = {'sized': [1, 2], 'key': [1, 2], 'named': [1, 2],
                     'subs': [1], 'sym': [2, 3],
                     'contains': [1], 'cons': [2], 'all': [2], 'every': [2]}
assert set(named_match_cases) == set(named_match_dispatch)

for nm, ns in named_match_cases.iteritems():
    for n in ns:
        add_sym('%s%d' % (nm, n))
add_sym('capture')
add_sym('wildcard')
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
            return symref('ctor', [refs_existing(nm), int_len(args)] + args)
    elif isinstance(node, ast.Name):
        if node.name == '_':
            return symref('wildcard', [])
        i = identifier('var', node.name)
        bs.append(i)
        return i
    elif isinstance(node, ast.Const):
        va, vt = conv_const(node)
        return va
    elif isinstance(node, ast.Tuple):
        return symref('tuplelit', [int_len(node.nodes)]
                                  + [conv_match_try(n,bs) for n in node.nodes])
    elif isinstance(node, ast.Or):
        return symref('or', [int_len(node.nodes)]
                            + [conv_match_try(n, bs) for n in node.nodes])
    elif isinstance(node, ast.And):
        return symref('and', [int_len(node.nodes)]
                             + [conv_match_try(n, bs) for n in node.nodes])
    elif isinstance(node, ast.Compare) and node.ops[0][0] == '==':
        assert isinstance(node.expr, ast.Name) and node.expr.name != '_'
        i = identifier('var', node.expr.name)
        bs.append(i)
        return symref('capture', [i, conv_match_try(node.ops[0][1], bs)])
    assert False, "Unknown match case: %s" % node


SpecialCallForm = DT('SpecialCall', ('name', str), ('args', [Atom]))
special_call_forms = {
        'ADT': make_adt, 'DT': make_dt,
        'new_context': make_context,
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

map(lambda s: add_sym(s, extra_prop='binaryop', extra_str=s),
    ['<', '>', '==', '!=', '<=', '>='])
map(add_sym, ['is', 'is not', 'in', 'not in'])
@expr(ast.Compare)
def conv_compare(e):
    assert len(e.ops) == 1
    (la, lt) = conv_expr(e.expr)
    (ra, rt) = conv_expr(e.ops[0][1])
    op = e.ops[0][0]
    return (symcall(op, [la, ra]), '%s %s %s' % (lt, op, rt))

@expr(ast.Const)
def conv_const(e):
    v = e.value
    if isinstance(v, int):
        return IntLit(v)
    elif isinstance(v, str):
        return StrLit(v)
    assert False, 'Unknown literal %s' % (e,)

add_sym('dictlit')
add_sym('pair')
@expr(ast.Dict)
def conv_dict(e):
    # This is pretty gross
    keys = map(conv_expr, map(fst, e.items))
    vals = map(conv_expr, map(snd, e.items))
    pairs = [([ka, va], (kt, vt)) for ((ka, kt), (va, vt)) in zip(keys, vals)]
    apairs = [symref('pair', [k, v]) for (k, v) in map(fst, pairs)]
    return (symref('dictlit', apairs),
            '{%s}' % ', '.join('%s: %s' % kv for kv in map(snd, pairs)))

@expr(ast.GenExpr)
def conv_genexpr(e):
    return conv_expr(e.code)

add_sym('genexpr')
@expr(ast.GenExprInner)
def conv_genexprinner(e):
    assert len(e.quals) == 1
    (ea, et) = conv_expr(e.expr)
    comp = e.quals[0]
    (assa, asst) = conv_ass(comp.assign)
    (lista, listt) = conv_expr(comp.iter if hasattr(comp, 'iter')
                               else comp.list)
    preds = []
    iftext = ''
    for if_ in comp.ifs:
        (ifa, ift) = conv_expr(if_.test)
        preds.append(ifa)
        iftext += ' if %s' % (ift,)
    return (symref('genexpr', [ea, assa, lista, int_len(preds)] + preds),
            '%s for %s in %s%s' % (et, asst, listt, iftext))

add_sym('attr')
@expr(ast.Getattr)
def conv_getattr(e):
    (ea, et) = conv_expr(e.expr)
    nm = e.attrname
    return (symref('attr', [ea, refs_existing(nm)]), '%s.%s' % (et, nm))

add_sym('keyword')
@expr(ast.Keyword)
def conv_keyword(e):
    (ea, et) = conv_expr(e.expr)
    return (symref('keyword', [Str(e.name, []), ea]), '%s=%s' % (e.name, et))

add_sym('?:')
@expr(ast.IfExp)
def conv_ifexp(e):
    (ca, ct) = conv_expr(e.test)
    (ta, tt) = conv_expr(e.then)
    (fa, ft) = conv_expr(e.else_)
    return (symref('?:', [ca, ta, fa]), '%s if %s else %s' % (tt, ct, ft))

def arg_pair(name):
    assert isinstance(name, str)
    return (symname(name), name)

def extract_arglist(s):
    names = s.argnames[:]
    assert not s.kwargs and not s.varargs and not s.defaults
    return ([identifier(Var(), nm) for nm in names], names)

add_sym('lambda')
@expr(ast.Lambda)
@inside_scope
def conv_lambda(e):
    (argsa, argst) = extract_arglist(e)
    (codea, codet) = conv_expr(e.code)
    return (symref('lambda', [int_len(argsa)] + argsa + [codea]),
            'lambda %s: %s' % (', '.join(argst), codet))

add_sym('listlit')
@expr(ast.List)
def conv_list(e):
    (itemsa, itemst) = conv_exprs(e.nodes)
    return (symref('listlit', [int_len(itemsa)] + itemsa),
            '[%s]' % ', '.join(itemst))

@expr(ast.ListComp)
def conv_listcomp(e):
    (compa, compt) = conv_genexprinner(e)
    return (compa, '[%s]' % compt)

@expr(ast.Name)
def conv_name(e):
    return (refs_existing(e.name), e.name)

add_sym('or', extra_prop='binaryop', extra_str='||')
@expr(ast.Or)
def conv_or(e):
    assert len(e.nodes) == 2
    (exprsa, exprst) = conv_exprs(e.nodes)
    return (symref('or', exprsa), ' or '.join(exprst))

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
    (ea, et) = conv_expr(e.expr)
    (sa, st) = conv_expr(e.subs[0])
    return (symref('subscript', [ea, sa]), '%s[%s]' % (et, st))

add_sym('tuplelit')
@expr(ast.Tuple)
def conv_tuple(e):
    if len(e.nodes) == 1:
        (fa, ft) = conv_expr(e.nodes[0])
        return (symref('tuplelit', [Int(1, []), fa]), '(%s,)' % (ft,))
    (itemsa, itemst) = conv_exprs(e.nodes)
    return (symref('tuplelit', [int_len(itemsa)] + itemsa),
            '(%s)' % ', '.join(itemst))

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
    lefta = conv_ass(s.nodes[0], context(SCOPE).indent == 0)
    # XXX Distinguish between defn and binding earlier
    k = match(lefta, ("key('var')", lambda: 'defn'), ('_', lambda: '='))
    return [symref(k, [lefta, expra])]

@stmt(ast.AssList)
def conv_asslist(s):
    assert False, 'TODO: Unpack list'
    # map(conv_ass, s.nodes)

add_sym('del')
@stmt(ast.AssTuple)
def conv_asstuple(s):
    ata = []
    for node in s.nodes:
        if getattr(node, 'flags', '') == 'OP_DELETE':
            ata.append(symref('del', [refs_existing(node.name)]))
        else:
            assert False, 'Unknown AssTuple node: ' + repr(node)
    return ata

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

def conv_ass(s, global_scope=False):
    if isinstance(s, ast.AssName):
        # LhsVar
        return ident_ref(s.name, True, export=global_scope)
    elif isinstance(s, ast.AssTuple):
        return LhsTuple([conv_ass(n, global_scope) for n in s.nodes])
    elif isinstance(s, ast.AssAttr):
        expra = conv_expr(s.expr)
        attra = ident_ref(s.attrname, True, export=False)
        return LhsAttr([expra, attra])
    else:
        return conv_expr(s)

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
    #func = identifier('func', s.name, export=export)
    @inside_scope
    def rest():
        return Func(extract_arglist(s), conv_stmts_noscope(s.code))
    #func.subs += rest()
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

def make_builtin(name, is_type=False):
    builtin = Builtin(name)
    BUILTINS[(name, is_type)] = (builtin, BindBuiltin)
    return identifier(builtin, name, is_type=is_type)

def setup_builtin_module():
    omni, scope = ast_contexts()
    def go():
        make_builtin('int', is_type=True)
        make_builtin('str', is_type=True)
    roots = in_context(OMNI, omni, lambda: in_context(SCOPE, scope, go))

def convert_file(filename, name, deps):
    assert filename.endswith('.py')
    if not BUILTINS:
        setup_builtin_module()
    if not boot_mod.digest:
        serialize_module(boot_mod)
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
