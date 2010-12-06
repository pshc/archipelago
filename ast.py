from atom import *
from base import *
import compiler
from compiler.ast import *

# HACK: Need context, storing a global...
CUR_CONTEXT = None
OMNI_CONTEXT = None

loaded_module_export_names = {}

def identifier(bootkey, name, subs=None, is_type=False,
               permissible_nms=frozenset(), export=False):
    global CUR_CONTEXT
    context = CUR_CONTEXT
    key = (name, is_type)
    assert name in permissible_nms or key not in context.syms, (
            "Symbol '%s' already in %s context\n%s" % (
            name, 'type' if is_type else 'term',
            '\n'.join('\t'+str(s) for s, t in context.syms if t == is_type)))
    if subs is None:
        subs = []
    subs.insert(0, symname(name))
    s = symref(bootkey, subs)
    context.syms[key] = s
    global OMNI_CONTEXT
    missing_refs = OMNI_CONTEXT.missingRefs.get(key)
    if missing_refs is not None:
        for ref in missing_refs:
            ref.refAtom = s
        del OMNI_CONTEXT.missingRefs[key]
    if export:
        OMNI_CONTEXT.exports[key] = s
    return s

add_sym('var')
def ident_ref(nm, create, is_type=False, export=False):
    global CUR_CONTEXT
    context = CUR_CONTEXT
    key = (nm, is_type)
    while context is not None:
        if key in context.syms:
            return Ref(context.syms[key], [])
        context = context.prevContext
    if create:
        var = identifier('var', nm, is_type=is_type, export=export)
        return var
    fwd_ref = Ref(nm, [])
    context = OMNI_CONTEXT
    context.missingRefs[key] = context.missingRefs.get(key, []) + [fwd_ref]
    return fwd_ref

def refs_existing(nm):
    return ident_ref(nm, False)

def create_or_update_ident(nm):
    return ident_ref(nm, True, export=True)

def type_ref(nm):
    return ident_ref(nm, False, is_type=True)

def destroy_forward_ref(ref):
    if not isinstance(ref.refAtom, basestring):
        return
    global OMNI_CONTEXT
    for t in (True, False):
        key = (ref.refAtom, t)
        refs = OMNI_CONTEXT.missingRefs.get(key, [])
        if ref in refs:
            refs.remove(ref)
            if not refs:
                del OMNI_CONTEXT.missingRefs[key]
            return
    assert False, "Couldn't find forward ref for destruction"

def inside_scope(f):
    def new_scope(*args, **kwargs):
        global CUR_CONTEXT
        prev = CUR_CONTEXT
        context = ConvertContext(prev.indent + 1, {}, prev)
        CUR_CONTEXT = context
        r = f(context, *args, **kwargs)
        CUR_CONTEXT = prev
        return r
    return new_scope


def unknown_stmt(node, context):
    cout(context, '??%s %s??', node.__class__,
          ', '.join(filter(lambda x: not x.startswith('_'), dir(node))))

def unknown_expr(node):
    return '%s?(%s)' % (str(node.__class__),
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
            return Ref(tvars[s], [])
        if '(' in s and s[-1] == ')':
            ctor, p, args = s[:-1].partition('(')
            return type_apply(type_str(ctor), map(type_str, args.split(',')))
        return type_ref(s)
    return match(t,
        ("key('str' or 'int')", lambda: t),
        ("Ref(key('DT'), _)", lambda: t),
        ("Str(s, _)", type_str),
        ("key('listlit', sized(cons(lt, _)))",
            lambda t: type_apply(type_ref('List'), [conv_type(t, tvars, dt)])),
        ("_", unknown))

(stmt, conv_stmt) = make_grammar_decorator(unknown_stmt)
(expr, conv_expr) = make_grammar_decorator(unknown_expr)

def conv_exprs(elist):
    return unzip(map(conv_expr, elist))

# EXPRESSIONS

add_sym('binaryop')
add_sym('unaryop')

for (cls, op) in {Add: '+', Sub: '-', Mul: '*', Div: '/', FloorDiv: '//',
                  Mod: '%', Bitand: '&', Bitor: '|', Bitxor: '^',
                  LeftShift: '<<', RightShift: '>>'}.iteritems():
    add_sym(op, extra_prop='binaryop', extra_str=op.replace('//','/'))
    @expr(cls)
    def binop(e, o=op):
        (la, lt) = conv_expr(e.left)
        (ra, rt) = conv_expr(e.right)
        return (symcall(o, [la, ra]), '%s %s %s' % (lt, o, rt))

for (cls, (op, sym)) in {UnaryAdd: ('+', 'positive'),
                         UnarySub: ('-', 'negate'),
                         Not: ('not ', 'not'),
                         Invert: ('~', 'invert')}.iteritems():
    add_sym(sym, extra_prop='unaryop', extra_str=op.replace('not ', '!'))
    @expr(cls)
    def unaop(e, o=op, s=sym):
        (a, t) = conv_expr(e.expr)
        return (symcall(s, [a]), o + t)
del cls, op

add_sym('and', extra_prop='binaryop', extra_str='&&')
@expr(And)
def conv_and(e):
    assert len(e.nodes) == 2
    (exprsa, exprst) = conv_exprs(e.nodes)
    return (symref('and', exprsa), ' and '.join(exprst))

add_sym('DT')
add_sym('ctor')
def make_adt(left, args):
    adt_nm = match(args.pop(0), ('Str(nm, _)', identity))
    ctors = []
    adt = identifier('DT', adt_nm, ctors, is_type=True, export=True)
    ctor_nms = []
    tvars = {}
    field_nms = set()
    while args:
        ctor = match(args.pop(0), ('Str(s, _)', identity))
        members = []
        while args:
            nm, t = match(args[0], ('Str(_, _)', lambda: (None, None)),
                                   ('key("tuplelit", sized(cons(Str(nm, _), \
                                     cons(t, _))))', tuple2))
            if nm is None:
                break
            members.append(identifier('field', nm,
                    [symref('type', [conv_type(t, tvars, dt=adt)])],
                    is_type=False, permissible_nms=field_nms))
            field_nms.add(nm)
            args.pop(0)
        ctor_nms.append(ctor)
        ctors.append(identifier('ctor', ctor, members, export=True))
    adt.subs += tvars.values()
    return ([adt], '%s = ADT(%s)' % (adt_nm, ', '.join(ctor_nms)))


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
    return ([fa], '%s = DT(%s)' % (nm, ', '.join(map(fst, fs))))

def replace_refs(mapping, e):
    ra = getattr(e, 'refAtom', None)
    if ra in mapping:
        e.refAtom = mapping[ra]
    for sub in e.subs:
        replace_refs(mapping, sub)
    return e

@inside_scope
def conv_match_case(context, code, f):
    bs = []
    c = conv_match_try(compiler.parse(code, mode='eval').node, bs)
    ref = lambda s: Ref(s, [])
    # TODO: Fix these up, due to stdlib
    e = match(f, ('key("lambda", sized(every(args, arg==key("var")), \
                                       cons(e, _)))',
                  lambda args, e: replace_refs(dict(zip(args, bs)), e)),
                 ('key("identity")', lambda: ref(bs[0])),
                 ('key("tuple2")', lambda: symref('tuplelit', [Int(2, []),
                                                  ref(bs[0]), ref(bs[1])])),
                 ('key("tuple3")', lambda: symref('tuplelit', [Int(3, []),
                                         ref(bs[0]), ref(bs[1]), ref(bs[2])])),
                 ('key("tuple4")', lambda: symref('tuplelit', [Int(4, []),
                             ref(bs[0]), ref(bs[1]), ref(bs[2]), ref(bs[3])])),
                 ('key("tuple5")', lambda: symref('tuplelit', [Int(5, []),
                 ref(bs[0]), ref(bs[1]), ref(bs[2]), ref(bs[3]), ref(bs[4])])),
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
def conv_match_try(ast, bs):
    if isinstance(ast, CallFunc) and isinstance(ast.node, Name):
        nm = ast.node.name
        named_matcher = named_match_cases.get(nm)
        if nm in ('all', 'every'):
            assert len(ast.args) == 2 and isinstance(ast.args[0], Name)
            i = conv_match_try(ast.args[0], bs)
            dummy = []
            return symref(nm + '2', [i, conv_match_try(ast.args[1], dummy)])
        args = [conv_match_try(n, bs) for n in ast.args]
        if named_matcher is not None:
            assert len(args) in named_matcher, (
                   "Bad number of args (%d) to %s matcher" % (len(args), nm))
            return symref("%s%d" % (nm, len(args)), args)
        else:
            return symref('ctor', [refs_existing(nm), int_len(args)] + args)
    elif isinstance(ast, Name):
        if ast.name == '_':
            return symref('wildcard', [])
        i = identifier('var', ast.name)
        bs.append(i)
        return i
    elif isinstance(ast, Const):
        va, vt = conv_const(ast)
        return va
    elif isinstance(ast, Tuple):
        return symref('tuplelit', [int_len(ast.nodes)]
                                  + [conv_match_try(n, bs) for n in ast.nodes])
    elif isinstance(ast, Or):
        return symref('or', [int_len(ast.nodes)]
                            + [conv_match_try(n, bs) for n in ast.nodes])
    elif isinstance(ast, And):
        return symref('and', [int_len(ast.nodes)]
                             + [conv_match_try(n, bs) for n in ast.nodes])
    elif isinstance(ast, Compare) and ast.ops[0][0] == '==':
        assert isinstance(ast.expr, Name) and ast.expr.name != '_'
        i = identifier('var', ast.expr.name)
        bs.append(i)
        return symref('capture', [i, conv_match_try(ast.ops[0][1], bs)])
    assert False, "Unknown match case: %s" % ast


SpecialCallForm = DT('SpecialCall', ('name', str), ('args', [Atom]))
special_call_forms = {'ADT': make_adt, 'DT': make_dt}

add_sym('call')
add_sym('char')
@expr(CallFunc)
def conv_callfunc(e):
    assert not e.star_args and not e.dstar_args
    (argsa, argst) = unzip(map(conv_expr, e.args))
    argstt = '(%s)' % (', '.join(argst),)
    if isinstance(e.node, Name):
        argsttt = e.node.name + argstt
        if e.node.name in special_call_forms:
            return (SpecialCallForm(e.node.name, argsa), argsttt)
        elif e.node.name == 'match':
            return (conv_match(argsa), argsttt)
        elif e.node.name == 'char':
            assert len(argsa) == 1 and isinstance(argsa[0], Str) \
                   and len(argsa[0].strVal) == 1
            return (symref('char', [argsa[0]]), argsttt)
    (fa, ft) = conv_expr(e.node)
    return (symref('call', [fa, int_len(argsa)] + argsa), ft + argstt)

map(lambda s: add_sym(s, extra_prop='binaryop', extra_str=s),
    ['<', '>', '==', '!=', '<=', '>='])
map(add_sym, ['is', 'is not', 'in', 'not in'])
@expr(Compare)
def conv_compare(e):
    assert len(e.ops) == 1
    (la, lt) = conv_expr(e.expr)
    (ra, rt) = conv_expr(e.ops[0][1])
    op = e.ops[0][0]
    return (symcall(op, [la, ra]), '%s %s %s' % (lt, op, rt))

@expr(Const)
def conv_const(e):
    v = e.value
    if isinstance(v, int):
        return (Int(v, []), str(v))
    elif isinstance(v, str):
        return (Str(v, []), repr(v))
    assert False, 'Unknown literal %s' % (e,)

add_sym('dictlit')
add_sym('pair')
@expr(Dict)
def conv_dict(e):
    # This is pretty gross
    keys = map(conv_expr, map(fst, e.items))
    vals = map(conv_expr, map(snd, e.items))
    pairs = [([ka, va], (kt, vt)) for ((ka, kt), (va, vt)) in zip(keys, vals)]
    apairs = [symref('pair', [k, v]) for (k, v) in map(fst, pairs)]
    return (symref('dictlit', apairs),
            '{%s}' % ', '.join('%s: %s' % kv for kv in map(snd, pairs)))

@expr(GenExpr)
def conv_genexpr(e):
    return conv_expr(e.code)

add_sym('genexpr')
@expr(GenExprInner)
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
@expr(Getattr)
def conv_getattr(e):
    (ea, et) = conv_expr(e.expr)
    nm = e.attrname
    return (symref('attr', [ea, refs_existing(nm)]), '%s.%s' % (et, nm))

add_sym('keyword')
@expr(Keyword)
def conv_keyword(e):
    (ea, et) = conv_expr(e.expr)
    return (symref('keyword', [Str(e.name, []), ea]), '%s=%s' % (e.name, et))

add_sym('?:')
@expr(IfExp)
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
    return ([identifier('var', nm) for nm in names], names)

add_sym('lambda')
@expr(Lambda)
@inside_scope
def conv_lambda(context, e):
    (argsa, argst) = extract_arglist(e)
    (codea, codet) = conv_expr(e.code)
    return (symref('lambda', [int_len(argsa)] + argsa + [codea]),
            'lambda %s: %s' % (', '.join(argst), codet))

add_sym('listlit')
@expr(List)
def conv_list(e):
    (itemsa, itemst) = conv_exprs(e.nodes)
    return (symref('listlit', [int_len(itemsa)] + itemsa),
            '[%s]' % ', '.join(itemst))

@expr(ListComp)
def conv_listcomp(e):
    (compa, compt) = conv_genexprinner(e)
    return (compa, '[%s]' % compt)

@expr(Name)
def conv_name(e):
    return (refs_existing(e.name), e.name)

add_sym('or', extra_prop='binaryop', extra_str='||')
@expr(Or)
def conv_or(e):
    assert len(e.nodes) == 2
    (exprsa, exprst) = conv_exprs(e.nodes)
    return (symref('or', exprsa), ' or '.join(exprst))

map(add_sym, ['arraycopy', 'slice', 'lslice', 'uslice'])
@expr(Slice)
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
@expr(Subscript)
def conv_subscript(e):
    assert len(e.subs) == 1
    (ea, et) = conv_expr(e.expr)
    (sa, st) = conv_expr(e.subs[0])
    return (symref('subscript', [ea, sa]), '%s[%s]' % (et, st))

add_sym('tuplelit')
@expr(Tuple)
def conv_tuple(e):
    if len(e.nodes) == 1:
        (fa, ft) = conv_expr(e.nodes[0])
        return (symref('tuplelit', [Int(1, []), fa]), '(%s,)' % (ft,))
    (itemsa, itemst) = conv_exprs(e.nodes)
    return (symref('tuplelit', [int_len(itemsa)] + itemsa),
            '(%s)' % ', '.join(itemst))

# STATEMENTS

add_sym('assert')
@stmt(Assert)
def conv_assert(s, context):
    (testa, testt) = conv_expr(s.test)
    (faila, failt) = conv_expr(s.fail) if s.fail else (Str('', []), None)
    cout(context, 'assert %s%s', testt, ', ' + failt if failt else '')
    return [symref('assert', [testa, faila])]

add_sym('=')
@stmt(Assign)
def conv_assign(s, context):
    (expra, exprt) = conv_expr(s.expr)
    if isinstance(expra, SpecialCallForm):
        assert len(s.nodes) == 1
        (spa, spt) = special_call_forms[expra.name](s.nodes[0], expra.args)
        cout(context, spt)
        return spa
    (lefta, leftt) = unzip(map(conv_ass, s.nodes))
    assa = []
    for ass in lefta: # backwards
        assa.append(symref('=', [ass, expra]))
        expra = ass
    cout(context, '%s = %s', ' = '.join(leftt), exprt)
    return assa

@stmt(AssList)
def conv_asslist(s, context):
    assert False, 'TODO: Unpack list'
    # map(conv_ass, s.nodes)

add_sym('del')
@stmt(AssTuple)
def conv_asstuple(s, context):
    ata = []
    for node in s.nodes:
        if getattr(node, 'flags', '') == 'OP_DELETE':
            cout(context, 'del %s', node.name)
            ata.append(symref('del', [refs_existing(node.name)]))
        else:
            assert False, 'Unknown AssTuple node: ' + repr(node)
    return ata

map(add_sym, ['+=', '-=', '*=', '/=', '%='])
@stmt(AugAssign)
def conv_augassign(s, context):
    (assa, asst) = conv_expr(s.node)
    (ea, et) = conv_expr(s.expr)
    cout(context, '%s %s %s', asst, s.op, et)
    return [symref(s.op, [assa, ea])]

add_sym('break')
@stmt(Break)
def conv_break(s, context):
    cout(context, 'break')
    return [symref('break', [])]

add_sym('class')
@stmt(Class)
def conv_class(s, context):
    cout(context, 'class %s%s:', s.name,
            '(%s)' % ', '.join(s.bases) if s.bases else '')
    if s.doc:
        cout(context, '    ' + s.doc)
    conv_stmts(s.code, context)
    return [symref('class', [])] # XXX: Will likely not support classes

add_sym('continue')
@stmt(Continue)
def conv_continue(s, context):
    cout(context, 'continue')
    return [symref('continue', [])]

add_sym('exprstmt')
@stmt(Discard)
def conv_discard(s, context):
    if isinstance(s.expr, Const) and s.expr.value is None:
        return []
    (ea, et) = conv_expr(s.expr)
    cout(context, '%s', et)
    return [symref('exprstmt', [ea])]

add_sym('tuplelit')
add_sym('attr')
def conv_ass(s):
    if isinstance(s, AssName):
        return (create_or_update_ident(s.name), s.name)
    elif isinstance(s, AssTuple):
        (itemsa, itemst) = unzip(map(conv_ass, s.nodes))
        itemsa.insert(0, int_len(itemsa))
        return (symref('tuplelit', itemsa), '(%s)' % (', '.join(itemst),))
    elif isinstance(s, AssAttr):
        (expra, exprt) = conv_expr(s.expr)
        (attra, attrt) = (create_or_update_ident(s.attrname), s.attrname)
        return (symref('attr', [expra, attra]), '%s.%s' % (exprt, attrt))
    else:
        return conv_expr(s)

add_sym('for')
add_sym('body')
@stmt(For)
@inside_scope
def conv_for(context, s, prev):
    (assa, asst) = conv_ass(s.assign)
    (lista, listt) = conv_expr(s.list)
    cout(context, 'for %s in %s:', asst, listt, indent_offset=-1)
    stmts = conv_stmts_noscope(s.body, context)
    fora = [assa, lista, symref('body', [int_len(stmts)] + stmts)]
    if s.else_:
        assert False
    return [symref('for', fora)]

@stmt(From)
def conv_from(s, context):
    if s.modname != 'stdlib':
        names = ', '.join(import_names(s.names))
        cout(context, 'from %s import %s # ignored', s.modname, names)
    return []

add_sym('func')
add_sym('args')
add_sym('body')
add_sym('doc')
add_sym('decorators')
@stmt(Function)
def conv_function(s, context):
    decs = []
    for decorator in s.decorators or []:
        (deca, dect) = conv_expr(decorator)
        cout(context, '@%s', dect)
        decs.append(deca)
    func = identifier('func', s.name, export=True) # XXX: Maybe not?
    @inside_scope
    def rest(context):
        (argsa, argst) = extract_arglist(s)
        cout(context, 'def %s(%s):', s.name, ', '.join(argst),
                indent_offset=-1)
        if s.doc:
            cout(context, '%s', repr(s.doc))
        stmts = conv_stmts_noscope(s.code, context)
        funca = [symref('args', [int_len(argsa)] + argsa),
                 symref('body', [int_len(stmts)] + stmts)]
        if s.doc:
            funca.append(symref('doc', [Str(s.doc, [])]))
        if decs:
            funca.append(symref('decorators', [int_len(decs)] + decs))
        return funca
    func.subs += rest()
    return [func]

add_sym('cond')
add_sym('case')
add_sym('else')
@stmt(If)
def conv_if(s, context):
    conds = []
    keyword = 'if'
    for (test, body) in s.tests:
        (testa, testt) = conv_expr(test)
        cout(context, '%s %s:', keyword, testt)
        stmts = conv_stmts(body, context)
        conds.append(symref('case', [testa, int_len(stmts)] + stmts))
        keyword = 'elif'
    if s.else_:
        cout(context, 'else:')
        stmts = conv_stmts(s.else_, context)
        conds.append(symref('else', [int_len(stmts)] + stmts))
    return [symref('cond', conds)]

def import_names(nms):
    return ['%s%s' % (m, (' as ' + n) if n else '') for (m, n) in nms]

@stmt(Import)
def conv_import(s, context):
    cout(context, 'import %s', ', '.join(import_names(s.names)))
    global loaded_module_export_names
    for name, qual in s.names:
        assert not qual, "Qualified imports not supported"
        name = name + '.py'
        if name not in loaded_modules and name == 'stdlib.py':
            global stdlib_mod
            assert not stdlib_mod
            stdlib_mod = convert_file('stdlib.py')
            serialize_module(stdlib_mod)
            import hm
            types = hm.infer_types(stdlib_mod.roots)
            write_mod_repr('gutentag.c', stdlib_mod, [types])
            from mogrify import mogrify
            c = mogrify(stdlib_mod, types)
            write_mod_repr('gutentag.c', c, [])
            from c import write_c_file
            write_c_file('gutentag.c', c)
            serialize_module(c)
        assert name in loaded_modules, "Import %s not loaded" % name
        mod = loaded_modules[name]
        symbols = loaded_module_export_names[mod]
        global OMNI_CONTEXT
        OMNI_CONTEXT.imports.update(symbols)
    return []

@stmt(Pass)
def conv_pass(s, context):
    cout(context, 'pass')
    return []

add_sym('print')
@stmt(Printnl)
def conv_printnl(s, context):
    assert s.dest is None
    node = s.nodes[0]
    if isinstance(node, Const):
        exprsa = [Str(node.value+'\n', []),
                symref('tuplelit', [Int(0, [])])]
        exprst = repr(node.value)
    elif isinstance(node, Mod):
        format = s.nodes[0].left.value
        argsa, argst = conv_expr(s.nodes[0].right)
        exprsa = [Str(format+'\n', []), argsa]
        exprst = '%r %% %s' % (format, argst)
    else:
        assert False, "Unexpected print form: %s" % s
    cout(context, 'print %s', exprst)
    return [symref('exprstmt', [symcall('printf', exprsa)])]

add_sym('return')
add_sym('returnnothing')
@stmt(Return)
def conv_return(s, context):
    if isinstance(s.value, Const) and s.value.value is None:
        cout(context, 'return')
        return [symref('returnnothing', [])]
    (vala, valt) = conv_expr(s.value)
    cout(context, 'return %s', valt)
    return [symref('return', [vala])]

@inside_scope
def conv_stmts(context, stmts, prev_context):
    return concat([conv_stmt(stmt, context) for stmt in stmts])

def conv_stmts_noscope(stmts, context):
    return concat([conv_stmt(stmt, context) for stmt in stmts])

add_sym('while')
add_sym('body')
@stmt(While)
def conv_while(s, context):
    (testa, testt) = conv_expr(s.test)
    cout(context, 'while %s:', testt)
    stmts = conv_stmts(s.body, context)
    return [symref('while', [testa, symref('body', [int_len(stmts)] + stmts)])]

ConvertContext = DT('ConvertContext', ('indent', int),
                                      ('syms', {(str, bool): Atom}),
                                      ('prevContext', None))

OmniContext = DT('OmniContext', ('imports', [Atom]),
                                ('exports', [Atom]),
                                ('missingRefs', {(str, bool): [Atom]}))

def cout(context, format, *args, **kwargs):
    indent = context.indent + kwargs.get('indent_offset', 0)
    line = '    ' * indent + format % args
    print line

def convert_file(filename):
    global boot_mod, stdlib_mod
    if not boot_mod.digest:
        serialize_module(boot_mod)
    stmts = compiler.parseFile(filename).node.nodes
    from atom import Module as Module_
    mod = Module_(filename, None, [])
    context = ConvertContext(-1, {}, None)
    for k, v in boot_sym_names.iteritems():
        t = k in ('str', 'int')
        context.syms[(k, t)] = v
    global CUR_CONTEXT, OMNI_CONTEXT, loaded_module_export_names
    CUR_CONTEXT = context
    OMNI_CONTEXT = OmniContext({}, {}, {})
    mod.roots = conv_stmts(stmts, context)
    # Resolve imports for missing symbols
    missing = OMNI_CONTEXT.missingRefs
    for key, refs in missing.items():
        if key in OMNI_CONTEXT.imports:
            for ref in refs:
                ref.refAtom = OMNI_CONTEXT.imports[key]
            del missing[key]
    assert not missing, "Symbols not found: " + ', '.join(
                ('type %s' if t else '%s') % s for s, t in missing)
    loaded_module_export_names[mod] = OMNI_CONTEXT.exports
    return mod

def escape(text):
    return text.replace('\\', '\\\\').replace('"', '\\"')

# TEMP
def fst(t):
    (f, s) = t
    return f
def snd(t):
    (f, s) = t
    return s

add_sym('module')
def emit_graph(mod, filename):
    f = open(filename, 'w')
    def do_emit(node, ctr):
        label = match(node,
                ('Int(n, _)', str),
                ('Str(s, _)', repr),
                ('Ref(r, _)', lambda r: r.subs[0].subs[0].strVal
                                        if r in boot_sums else '<ref>'))
        f.write('n%d [label="%s"];\n' % (ctr, escape(label)))
        orig = ctr
        for sub in node.subs:
            f.write('n%d -> n%d;\n' % (orig, ctr + 1))
            ctr = do_emit(sub, ctr + 1)
        return ctr
    f.write('digraph G {\n')
    do_emit(symref('module', mod.roots), 0)
    f.write('}\n')

if __name__ == '__main__':
    emit_graph(convert_file('interpret.py'), 'graph.dot')

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
