from atom import *
from base import *
import compiler
from compiler.ast import *

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

(stmt, conv_stmt) = make_grammar_decorator(unknown_stmt)
(expr, conv_expr) = make_grammar_decorator(unknown_expr)

def conv_exprs(elist):
    return unzip(map(conv_expr, elist))

# EXPRESSIONS

for (cls, op) in {Add: '+', Sub: '-', Mul: '*', Div: '/', FloorDiv: '//',
                  Mod: '%', Power: '**', Bitand: '&', Bitor: '|', Bitxor: '^',
                  LeftShift: '<<', RightShift: '>>'}.iteritems():
    add_sym(op)
    @expr(cls)
    def binop(e, o=op):
        (la, lt) = conv_expr(e.left)
        (ra, rt) = conv_expr(e.right)
        return (symcall(o, [la, ra]), '%s %s %s' % (lt, o, rt))

for (cls, (op, sym)) in {UnaryAdd: ('+', 'positive'),
                         UnarySub: ('-', 'negate'),
                         Not: ('not ', 'not'),
                         Invert: ('~', 'invert')}.iteritems():
    add_sym(sym)
    @expr(cls)
    def unaop(e, o=op, s=sym):
        (a, t) = conv_expr(e.expr)
        return (symcall(s, [a]), o + t)
del cls, op

add_sym('and')
@expr(And)
def conv_and(e):
    (exprsa, exprst) = conv_exprs(e.nodes)
    return (symref('and', [int_len(exprsa)]) + exprsa,
            ' and '.join(exprst))

map(add_sym, ['call', 'args', 'starargs', 'dstarargs'])
@expr(CallFunc)
def conv_callfunc(e):
    (fa, ft) = conv_expr(e.node)
    (argsa, argst) = unzip(map(conv_expr, e.args))
    argsa = [fa, symref('args', [int_len(argsa)] + argsa)]
    if e.star_args:
        (saa, sat) = conv_expr(e.star_args)
        argsa.append(symref('starargs', [saa]))
        argst.append('*' + sat)
    if e.dstar_args:
        (dsa, dst) = conv_expr(e.dstar_args)
        argsa.append(symref('dstarargs', [dsa]))
        argst.append('**' + sat)
    return (symref('call', argsa), '%s(%s)' % (ft, ', '.join(argst)))

map(add_sym, ['<', '>', '==', '!=', '<=', '>=',
              'is', 'is not', 'in', 'not in'])
@expr(Compare)
def conv_compare(e):
    assert len(e.ops) == 1
    (la, lt) = conv_expr(e.expr)
    (ra, rt) = conv_expr(e.ops[0][1])
    op = e.ops[0][0]
    return (symcall(op, [la, ra]), '%s %s %s' % (lt, op, rt))

add_sym('null')
@expr(Const)
def conv_const(e):
    v = e.value
    if isinstance(v, int):
        return (Int(v, []), str(v))
    elif isinstance(v, str):
        return (Str(v, []), repr(v))
    elif v is None:
        return (symref('null', []), 'None')
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

add_sym('getattr')
@expr(Getattr)
def conv_getattr(e):
    (ea, et) = conv_expr(e.expr)
    nm = e.attrname
    return (symref('getattr', [ea, Str(nm, [])]), '%s.%s' % (et, nm))

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
    return (symref('name', [Str(name, [])]), name)

add_sym('vararg')
add_sym('kwarg')
add_sym('default')
def extract_arglist(s):
    names = s.argnames[:]
    endnames = []
    astargs = []
    if s.kwargs:
        (kwa, kwt) = arg_pair(names.pop())
        endnames = ['**' + kwt]
        kwa.subs.append(symref('kwarg', []))
        astargs = [kwa]
    if s.varargs:
        (vaa, vat) = arg_pair(names.pop())
        endnames.insert(0, '*' + vat)
        vaa.subs.append(symref('vararg', []))
        astargs.insert(0, vaa)
    if s.defaults:
        ndefs = len(s.defaults)
        defnames = []
        astdefs = []
        for (nm, e) in zip(names[-ndefs:], s.defaults):
            (aa, at) = arg_pair(nm)
            (da, dt) = conv_expr(e) # default value expr
            defnames.append('%s=%s' % (at, dt))
            aa.subs.append(symref('default', [da]))
            astdefs.append(aa)
        endnames = defnames + endnames
        astargs = astdefs + astargs
        names = names[:-ndefs]
    args = map(arg_pair, names)
    return (map(fst, args) + astargs, map(snd, args) + endnames)

add_sym('lambda')
@expr(Lambda)
def conv_lambda(e):
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

add_sym('ident')
@expr(Name)
def conv_name(e):
    return (symident(e.name, []), e.name)

add_sym('or')
@expr(Or)
def conv_or(e):
    (exprsa, exprst) = conv_exprs(e.nodes)
    return (symref('or', [int_len(exprsa)] + exprsa),
            ' or '.join(exprst))

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
    (faila, failt) = maybe((Str('', []), None), conv_expr, s.fail)
    cout(context, 'assert %s%s', testt, ', ' + failt if failt else '')
    return [symref('assert', [testa, faila])]

add_sym('=')
@stmt(Assign)
def conv_assign(s, context):
    (expra, exprt) = conv_expr(s.expr)
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
            ata.append(symref('del', [symident(node.name, [])]))
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

add_sym('class')
@stmt(Class)
def conv_class(s, context):
    cout(context, 'class %s%s:', s.name,
            '(%s)' % ', '.join(s.bases) if s.bases else '')
    if s.doc:
        cout(context, '    ' + s.doc)
    conv_stmts(s.code, context)
    return [symref('class', [])] # XXX: Will likely not support classes

add_sym('exprstmt')
@stmt(Discard)
def conv_discard(s, context):
    (ea, et) = conv_expr(s.expr)
    cout(context, '%s', et)
    return [symref('exprstmt', [ea])]

add_sym('unpacktuple')
add_sym('setattr')
def conv_ass(s):
    if isinstance(s, AssName):
        return (symident(s.name, []), s.name)
    elif isinstance(s, AssTuple):
        (itemsa, itemst) = unzip(map(conv_ass, s.nodes))
        itemsa.insert(0, int_len(itemsa))
        return (symref('unpacktuple', itemsa), '(%s)' % (', '.join(itemst),))
    elif isinstance(s, AssAttr):
        (expra, exprt) = conv_expr(s.expr)
        (attra, attrt) = (symident(s.attrname, []), s.attrname)
        return (symref('setattr', [expra, attra]), '%s.%s' % (exprt, attrt))
    else:
        return conv_expr(s)

add_sym('for')
add_sym('body')
@stmt(For)
def conv_for(s, context):
    (assa, asst) = conv_ass(s.assign)
    (lista, listt) = conv_expr(s.list)
    cout(context, 'for %s in %s:', asst, listt)
    stmts = conv_stmts(s.body, context)
    fora = [assa, lista, symref('body', [int_len(stmts)] + stmts)]
    if s.else_:
        assert False
    return [symref('for', fora)]

# TODO
@stmt(From)
def conv_from(s, context):
    cout(context, 'from %s import %s', s.modname,
            ', '.join(import_names(s.names)))
    return []

add_sym('func')
add_sym('args')
add_sym('body')
add_sym('doc')
add_sym('decors')
@stmt(Function)
def conv_function(s, context):
    decs = []
    for decorator in s.decorators or []:
        (deca, dect) = conv_expr(decorator)
        cout(context, '@%s', dect)
        decs.append(deca)
    (argsa, argst) = extract_arglist(s)
    cout(context, 'def %s(%s):', s.name, ', '.join(argst))
    if s.doc:
        cout(context, repr(s.doc), indent_offset=1)
    stmts = conv_stmts(s.code, context)
    funca = [symref('name', [Str(s.name, [])]),
             symref('args', [int_len(argsa)] + argsa),
             symref('body', [int_len(stmts)] + stmts)]
    if s.doc:
        funca.append(symref('doc', [Str(s.doc)]))
    if decs:
        funca.append(symref('decors', decs))
    return [symref('func', funca)]

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
        conds.append(symref('case', [symref('else', []), int_len(stmts)]
                                    + stmts))
    return [symref('cond', conds)]

def import_names(nms):
    return ['%s%s' % (m, maybe('', lambda a: ' as ' + a, n)) for (m, n) in nms]

# TODO
@stmt(Import)
def conv_import(s, context):
    cout(context, 'import %s', ', '.join(import_names(s.names)))
    return []

@stmt(Pass)
def conv_pass(s, context):
    cout(context, 'pass')
    return []

add_sym('print')
@stmt(Print)
def conv_print(s, context):
    assert s.dest is None
    (exprsa, exprst) = conv_exprs(s.nodes)
    cout(context, 'print %s,', ', '.join(exprst))
    return [symref('exprstmt', [symcall('print', exprsa)])]

add_sym('println')
@stmt(Printnl)
def conv_printnl(s, context):
    assert s.dest is None
    (exprsa, exprst) = conv_exprs(s.nodes)
    cout(context, 'print %s', ', '.join(exprst))
    return [symref('exprstmt', [symcall('println', exprsa)])]

add_sym('return')
@stmt(Return)
def conv_return(s, context):
    (vala, valt) = conv_expr(s.value)
    cout(context, 'return %s', valt)
    return [symref('return', [vala])]

def conv_stmts(stmts, context):
    context.indent += 1
    converted = [conv_stmt(stmt, context) for stmt in stmts]
    context.indent -= 1
    return concat(converted)

add_sym('while')
add_sym('body')
@stmt(While)
def conv_while(s, context):
    (testa, testt) = conv_expr(s.test)
    cout(context, 'while %s:', testt)
    stmts = conv_stmts(s.body, context)
    return [symref('while', [testa, symref('body', [int_len(stmts)] + stmts)])]

ConvertContext = DT('ConvertContext', ('indent', int))

def cout(context, format, *args, **kwargs):
    indent = context.indent + kwargs.get('indent_offset', 0)
    line = '    ' * indent + format % args
    print line

def convert_file(filename):
    stmts = compiler.parseFile(filename).node.nodes
    from atom import Module as Module_
    return Module_(filename, None, conv_stmts(stmts, ConvertContext(-1)))

def escape(text):
    return text.replace('\\', '\\\\').replace('"', '\\"')

add_sym('module')
def emit_graph(mod, filename):
    f = open(filename, 'w')
    def do_emit(node, ctr):
        label = match(node,
                ('Int(n, _)', str),
                ('Str(s, _)', repr),
                ('Ref(r, m, _)', lambda r, m: r.subs[0].subs[0].strVal
                                              if m is boot_mod else '<ref>'))
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
