from atom import *
import compiler
from compiler.ast import *

def maybe(default, func, expr):
    return default if expr is None else func(expr)

# Avoid tuples in args for simplicity
def fst(t): (f, s) = t; return f
def snd(t):
    (f, s) = t; return s
def concat(lists): return reduce(list.__add__, lists, [])

# Bootstrap module
boot_mod = Module('bootstrap', None, [])
b_symbol = Ref(None, boot_mod, [Ref(None, boot_mod, [Str("symbol", [])])])
b_name = Ref(b_symbol, boot_mod, [Ref(None, boot_mod, [Str("name", [])])])
b_symbol.refAtom = b_symbol
b_symbol.subs[0].refAtom = b_name
b_name.subs[0].refAtom = b_name
boot_syms = [b_symbol, b_name]
boot_sym_names = {'symbol': b_symbol, 'name': b_name}

def add_sym(name):
    assert name not in boot_sym_names
    node = Ref(b_symbol, boot_mod, [Ref(b_name, boot_mod, [Str(name, [])])])
    boot_syms.append(node)
    boot_sym_names[name] = node

def symref(name, subs):
    assert name in boot_sym_names, "%s not a boot symbol" % (name,)
    return Ref(boot_sym_names[name], boot_mod, subs)

def symcall(name, subs):
    assert name in boot_sym_names, "%s not a boot symbol" % (name,)
    func = Ref(boot_sym_names[name], boot_mod, [])
    return symref('call', [func, Int(len(subs), [])] + subs)

def unknown_stmt(node, context):
    context.out('??%s %s??', node.__class__,
          ', '.join(filter(lambda x: not (x.startswith('_')), dir(node))))

def unknown_expr(node):
    return '%s?(%s)' % (str(node.__class__),
          ', '.join(filter(lambda x: not (x.startswith('_')), dir(node))))

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
    exprs = map(conv_expr, e.nodes)
    return (symref('and', [Int(len(exprs), [])]) + map(fst, exprs),
            ' and '.join(map(snd, exprs)))

add_sym('call')
@expr(CallFunc)
def conv_callfunc(e):
    (fa, ft) = conv_expr(e.node)
    exprs = map(conv_expr, e.args)
    return (symref('call', [fa, Int(len(exprs), [])] + map(fst, exprs)),
            '%s(%s)' % (ft, ', '.join(map(snd, exprs))))
    # {,d}star_args

map(add_sym, ['<', '>', '==', '!=', '<=', '>=',
              'is', 'is not', 'in', 'not in'])
@expr(Compare)
def conv_compare(e):
    assert len(e.ops) == 1
    (la, lt) = conv_expr(e.expr)
    (ra, rt) = conv_expr(e.ops[0][1])
    op = e.ops[0][0]
    return (symcall(op, [la, ra]), '%s %s %s' % (lt, op, rt))

add_sym('intlit'); add_sym('strlit')
@expr(Const)
def conv_const(e):
    v = e.value
    if isinstance(v, int):
        return (symref('intlit', [Int(v, [])]), str(v))
    elif isinstance(v, str):
        return (symref('strlit', [Str(v, [])]), repr(v))
    assert False, "Unknown literal type"

add_sym('dictlit')
@expr(Dict)
def conv_dict(e):
    keys = map(conv_expr, map(fst, e.items))
    vals = map(conv_expr, map(snd, e.items))
    pairs = [([ka, va], (kt, vt)) for ((ka, kt), (va, vt)) in zip(keys, vals)]
    return (symref('dictlit', concat(map(fst, pairs))),
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
    (assa, asst) = (Str("TODO", []), conv_ass(comp.assign))
    (lista, listt) = conv_expr(comp.iter if hasattr(comp, 'iter')
                               else comp.list)
    preds = []
    iftext = ""
    for if_ in comp.ifs:
        (ifa, ift) = conv_expr(if_.test)
        preds.append(ifa)
        iftext += ' if %s' % (ift,)
    return (symref('genexpr', [ea, assa, lista, Int(len(preds), [])] + preds),
            '%s for %s in %s%s' % (et, asst, listt, iftext))

add_sym('getattr')
@expr(Getattr)
def conv_getattr(e):
    (ea, et) = conv_expr(e.expr)
    nm = e.attrname
    return (symcall('getattr', [ea, Str(nm, [])]), '%s.%s' % (et, nm))

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
    return (symcall('?:', [ca, ta, fa]), "%s if %s else %s" % (tt, ct, ft))

def arg_pair(name):
    assert isinstance(name, str)
    return (symref('name', [Str(name, [])]), name)

add_sym('vararg'); add_sym('kwarg'); add_sym('default')
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
    return (symref('lambda', [Int(len(argsa), [])] + argsa + [codea]),
            'lambda %s: %s' % (', '.join(argst), codet))

add_sym('listlit')
@expr(List)
def conv_list(e):
    items = map(conv_expr, e.nodes)
    return (symref('listlit', [Int(len(items), [])] + map(fst, items)),
            '[%s]' % ', '.join(map(snd, items)))

@expr(ListComp)
def conv_listcomp(e):
    (compa, compt) = conv_genexprinner(e)
    return (compa, '[%s]' % compt)

add_sym('ident')
@expr(Name)
def conv_name(e):
    return (symref('ident', [Str(e.name, [])]), e.name)

add_sym('or')
@expr(Or)
def conv_or(e):
    exprs = map(conv_expr, e.nodes)
    return (symref('or', [Int(len(exprs), [])] + map(fst, exprs)),
            ' or '.join(map(snd, exprs)))

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
    return (symcall('subscript', [ea, sa]), '%s[%s]' % (et, st))

add_sym('tuplelit')
@expr(Tuple)
def conv_tuple(e):
    if len(e.nodes) == 1:
        (fa, ft) = conv_expr(e.nodes[0])
        return (symref('tuplelit', [Int(1, []), fa]), '(%s,)' % (ft,))
    items = map(conv_expr, e.nodes)
    return (symref('tuplelit', [Int(len(items), [])] + map(fst, items)),
            '(%s)' % ', '.join(map(snd, items)))

# STATEMENTS

conv_expr_ = lambda e: snd(conv_expr(e))

@stmt(Assert)
def conv_assert(s, context):
    context.out('assert %s%s', conv_expr_(s.test),
                maybe('', lambda e: ', ' + conv_expr_(e), s.fail))

@stmt(Assign)
def conv_assign(s, context):
    context.out('%s = %s', conv_ass(s.nodes[0]), conv_expr_(s.expr))

@stmt(AssList)
def conv_asslist(s, context):
    for node in s.nodes:
        context.out('%s', conv_ass(s))

@stmt(AssTuple)
def conv_asstuple(s, context):
    for node in s.nodes:
        if getattr(node, 'flags', '') == 'OP_DELETE':
            context.out('del %s', node.name)
        else:
            assert False, "Unknown AssTuple node: " + repr(node)

@stmt(AugAssign)
def conv_augassign(s, context):
    context.out('%s %s %s', conv_expr_(s.node), s.op, conv_expr_(s.expr))

@stmt(Class)
def conv_class(s, context):
    context.out('class %s%s:', s.name,
            '(%s)' % ', '.join(s.bases) if s.bases else '')
    if s.doc:
        context.out("    " + s.doc)
    conv_stmts(s.code, context)

@stmt(Discard)
def conv_discard(s, context):
    context.out('%s', conv_expr_(s.expr))

def conv_ass(s):
    if isinstance(s, AssName):
        return s.name
    elif isinstance(s, AssTuple):
        return '(%s)' % (', '.join(map(conv_ass, s.nodes)),)
    elif isinstance(s, AssAttr):
        return '%s.%s' % (conv_expr_(s.expr), s.attrname)
    else:
        return conv_expr_(s)

@stmt(For)
def conv_for(s, context):
    context.out('for %s in %s:', conv_ass(s.assign), conv_expr_(s.list))
    conv_stmts(s.body, context)
    if s.else_:
        conv_stmts(s.else_, context)

@stmt(From)
def conv_from(s, context):
    context.out('from %s import %s', s.modname,
            ', '.join(import_names(s.names)))

@stmt(Function)
def conv_function(s, context):
    for decorator in s.decorators or []:
        context.out('@%s', conv_expr_(decorator))
    (argsa, argst) = extract_arglist(s)
    context.out('def %s(%s):', s.name, ', '.join(argst))
    if s.doc:
        context.out(repr(s.doc), indent_offset=1)
    conv_stmts(s.code, context)

@stmt(If)
def conv_if(s, context):
    keyword = 'if'
    for (test, body) in s.tests:
        context.out('%s %s:', keyword, conv_expr_(test))
        conv_stmts(body, context)
        keyword = 'elif'
    if s.else_:
        context.out('else:')
        conv_stmts(s.else_, context)

def import_names(nms):
    return ['%s%s' % (m, maybe('', lambda a: ' as ' + a, n)) for (m, n) in nms]

@stmt(Import)
def conv_import(s, context):
    context.out('import %s', ', '.join(import_names(s.names)))

@stmt(Pass)
def conv_pass(s, context):
    context.out('pass')

@stmt(Print)
def conv_print(s, context):
    context.out('print %s%s,',
            maybe('', lambda e: '>>' + conv_expr_(e) + ', ', s.dest),
            ', '.join(map(conv_expr_, s.nodes)))

@stmt(Printnl)
def conv_printnl(s, context):
    context.out('print %s%s',
            maybe('', lambda e: '>>' + conv_expr_(e) + ', ', s.dest),
            ', '.join(map(conv_expr_, s.nodes)))

@stmt(Return)
def conv_return(s, context):
    context.out('return %s', conv_expr_(s.value))


def conv_stmts(stmts, context):
    context.indent += 1
    converted = [conv_stmt(stmt, context) for stmt in stmts]
    context.indent -= 1
    return converted

class ConvertContext:
    def __init__(self):
        self.indent = -1

    def out(self, format, *args, **kwargs):
        indent = self.indent + kwargs.get('indent_offset', 0)
        line = ('    ' * indent) + (format % args)
        print line

def convert_file(filename):
    stmts = compiler.parseFile(filename).node.nodes
    conv_stmts(stmts, ConvertContext())

convert_file("ast.py")

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
