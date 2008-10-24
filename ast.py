import atom
import compiler
from compiler.ast import *

def maybe(default, func, expr):
    return default if expr is None else func(expr)

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
    @expr(cls)
    def binop(e, o=op):
        return '%s %s %s' % (conv_expr(e.left), o, conv_expr(e.right))

for (cls, op) in {UnaryAdd: '+', UnarySub: '-',
                  Not: 'not ', Invert: '~'}.iteritems():
    @expr(cls)
    def unaop(e, o=op):
        return o + conv_expr(e.expr)
del cls, op

@expr(And)
def conv_and(e):
    return ' and '.join(map(conv_expr, e.nodes))

@expr(CallFunc)
def conv_callfunc(e):
    return '%s(%s)' % (conv_expr(e.node), ', '.join(map(conv_expr, e.args)))
    # {,d}star_args

@expr(Compare)
def conv_compare(e):
    tests = ['%s %s' % (op, conv_expr(ex)) for (op, ex) in e.ops]
    return '%s %s' % (conv_expr(e.expr), ' '.join(tests))

@expr(Const)
def conv_const(e):
    return repr(e.value)

@expr(Dict)
def conv_dict(e):
    return '{%s}' % ', '.join(': '.join(map(conv_expr, kv)) for kv in e.items)

@expr(GenExpr)
def conv_genexpr(e):
    return conv_expr(e.code)

@expr(GenExprInner)
def conv_genexprinner(e):
    assert len(e.quals) == 1
    comp = e.quals[0]
    ifs = [' if %s' % conv_expr(compif.test) for compif in comp.ifs]
    iter = comp.iter if hasattr(comp, 'iter') else comp.list
    return '%s for %s in %s%s' % (conv_expr(e.expr), conv_ass(comp.assign),
                                  conv_expr(iter), ''.join(ifs))

@expr(Getattr)
def conv_getattr(e):
    return '%s.%s' % (conv_expr(e.expr), e.attrname)

@expr(Keyword)
def conv_keyword(e):
    return '%s=%s' % (e.name, conv_expr(e.expr))

@expr(IfExp)
def conv_ifexp(e):
    return "%s if %s else %s" % tuple(map(conv_expr,
                                          [e.then, e.test, e.else_]))

def extract_arglist(s):
    names = s.argnames[:]
    args = ["**" + names.pop()] if s.kwargs else []
    if s.varargs:
        args.insert(0, "*" + names.pop())
    if s.defaults:
        dlen = len(s.defaults)
        args = ["%s=%s" % (n, conv_expr(d))
                for (n, d) in zip(names[-dlen:], s.defaults)] + args
        names = names[:-dlen]
    return names + args

@expr(Lambda)
def conv_lambda(e):
    return 'lambda %s: %s' % (', '.join(extract_arglist(e)), conv_expr(e.code))

@expr(List)
def conv_list(e):
    return '[%s]' % ', '.join(map(conv_expr, e.nodes))

@expr(ListComp)
def conv_listcomp(e):
    return '[%s]' % conv_genexprinner(e)

@expr(Name)
def conv_name(e):
    return e.name

@expr(Or)
def conv_or(e):
    return ' or '.join(map(conv_expr, e.nodes))

@expr(Slice)
def conv_slice(e):
    return '%s[%s:%s]' % (conv_expr(e.expr), maybe('', conv_expr, e.lower),
                                             maybe('', conv_expr, e.upper))

@expr(Subscript)
def conv_subscript(e):
    return '%s[%s]' % (conv_expr(e.expr), ', '.join(map(conv_expr, e.subs)))

@expr(Tuple)
def conv_tuple(e):
    if len(e.nodes) == 1:
        return '(%s,)' % conv_expr(e.nodes[0])
    return '(%s)' % ', '.join(map(conv_expr, e.nodes))

# STATEMENTS

@stmt(Assert)
def conv_assert(s, context):
    context.out('assert %s%s', conv_expr(s.test),
                maybe('', lambda e: ', ' + conv_expr(e), s.fail))

@stmt(Assign)
def conv_assign(s, context):
    context.out('%s = %s', conv_ass(s.nodes[0]), conv_expr(s.expr))

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
    context.out('%s %s %s', conv_expr(s.node), s.op, conv_expr(s.expr))

@stmt(Class)
def conv_class(s, context):
    context.out('class %s%s:', s.name,
            '(%s)' % ', '.join(s.bases) if s.bases else '')
    if s.doc:
        context.out("    " + s.doc)
    conv_stmts(s.code, context)

@stmt(Discard)
def conv_discard(s, context):
    context.out('%s', conv_expr(s.expr))

def conv_ass(s):
    if isinstance(s, AssName):
        return s.name
    elif isinstance(s, AssTuple):
        return '(%s)' % (', '.join([node.name for node in s.nodes]),)
    elif isinstance(s, AssAttr):
        return '%s.%s' % (conv_expr(s.expr), s.attrname)
    else:
        return conv_expr(s)

@stmt(For)
def conv_for(s, context):
    context.out('for %s in %s:', conv_ass(s.assign), conv_expr(s.list))
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
        context.out('@%s', conv_expr(decorator))
    context.out('def %s(%s):', s.name, ', '.join(extract_arglist(s)))
    if s.doc:
        context.out(repr(s.doc), indent_offset=1)
    conv_stmts(s.code, context)

@stmt(If)
def conv_if(s, context):
    keyword = 'if'
    for (test, body) in s.tests:
        context.out('%s %s:', keyword, conv_expr(test))
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
            maybe('', lambda e: '>>' + conv_expr(e) + ', ', s.dest),
            ', '.join(map(conv_expr, s.nodes)))

@stmt(Printnl)
def conv_printnl(s, context):
    context.out('print %s%s',
            maybe('', lambda e: '>>' + conv_expr(e) + ', ', s.dest),
            ', '.join(map(conv_expr, s.nodes)))

@stmt(Return)
def conv_return(s, context):
    context.out('return %s', conv_expr(s.value))


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
