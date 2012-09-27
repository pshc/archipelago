#!/usr/bin/python2
from os import system
from hashlib import sha256
from base import *
from bedrock import *
from globs import *
from types_builtin import *
from vat import *
import types

types_by_name['set'] = lambda: t_DT(Set)

# Shouldn't this be an env or something?
BUILTINS = {}
RUNTIME = {}

Builtin = DT('Builtin')

Env = DT('Env', ('type', Type))

Extrinsic = DT('Extrinsic', ('type', Type))

Var = DT('Var')

Pat, PatCtor, PatCapture, PatInt, PatStr, PatTuple, PatVar, PatWild = \
    ADT('Pat',
        'PatCtor', ('ctor', '*Ctor'), ('args', '[Pat]'),
        'PatCapture', ('var', Var), ('pattern', 'Pat'),
        'PatInt', ('val', int),
        'PatStr', ('val', str),
        'PatTuple', ('vals', '[Pat]'),
        'PatVar', ('var', Var),
        'PatWild')

MatchCase = DT('MatchCase', ('pat', Pat), ('result', 'Expr'))

CoreLiteral, IntLit, FloatLit, StrLit = ADT('CoreLiteral',
        'IntLit', ('val', int),
        'FloatLit', ('val', float),
        'StrLit', ('val', str))

CoreExpr, Attr, Bind, Call, Lit, Ternary, TupleLit, NullPtr, WithVar = \
    ADT('CoreExpr',
        'Attr', ('expr', 'CoreExpr'), ('field', '*Field'),
        'Bind', ('target', '*a'), # Binder a => a
        'Call', ('func', 'CoreExpr'), ('args', '[CoreExpr]'),
        'Lit', ('literal', CoreLiteral),
        'Ternary', ('test', 'CoreExpr'), ('then', 'CoreExpr'),
                   ('else_', 'CoreExpr'),
        'TupleLit', ('vals', '[CoreExpr]'),
        # XXX only used in the LLVM phase, move to own type
        'NullPtr',
        'WithVar', ('var', Var), ('expr', 'CoreExpr'))

Expr, E, And, DictLit, FuncExpr, GenExpr, \
        GetEnv, HaveEnv, InEnv, \
        GetExtrinsic, HasExtrinsic, ScopeExtrinsic, \
        ListLit, Match, Or = \
    ADT(('Expr', CoreExpr),
        'And', ('left', 'Expr'), ('right', 'Expr'),
        'DictLit', ('vals', '[(Expr, Expr)]'),
        'FuncExpr', ('func', 'Func(Expr)'),
        'GenExpr', ('expr', 'Expr'), ('pattern', 'Pat'),
                   ('listExpr', 'Expr'), ('preds', '[Expr]'),
        'GetEnv', ('env', '*Env'),
        'HaveEnv', ('env', '*Env'),
        'InEnv', ('env', '*Env'), ('init', 'Expr'), ('expr', 'Expr'),
        'GetExtrinsic', ('extrinsic', '*Extrinsic'), ('node', 'Expr'),
        'HasExtrinsic', ('extrinsic', '*Extrinsic'), ('node', 'Expr'),
        'ScopeExtrinsic', ('extrinsic', '*Extrinsic'), ('expr', 'Expr'),
        'ListLit', ('vals', '[Expr]'),
        'Match', ('expr', 'Expr'), ('cases', [MatchCase]),
        'Or', ('left', 'Expr'), ('right', 'Expr'))

AugOp, AugAdd, AugSubtract, AugMultiply, AugDivide, AugModulo = ADT('AugOp',
        'AugAdd', 'AugSubtract', 'AugMultiply', 'AugDivide', 'AugModulo')

Body = DT('Body', ('stmts', '[Stmt(e)]'))

CondCase = DT('CondCase', ('test', 'e'), ('body', 'Body(e)'))

Func = DT('Func', ('params', [Var]), ('body', 'Body(e)'))

Lhs, LhsVar, LhsAttr = ADT('Lhs',
        'LhsVar', ('var', '*Var'),
        'LhsAttr', ('sub', 'e'), ('attr', '*Field'))

CoreStmt, Assign, AugAssign, Break, Cond, Continue, Defn, \
    ExprStmt, Return, ReturnNothing, While = \
    ADT('CoreStmt',
        'Assign', ('lhs', 'Lhs(e)'), ('expr', 'e'),
        'AugAssign', ('op', AugOp), ('lhs', 'Lhs(e)'), ('expr', 'e'),
        'Break',
        'Cond', ('cases', ['CondCase(e)']),
        'Continue',
        'Defn', ('pat', Pat), ('expr', 'e'),
        'ExprStmt', ('expr', 'e'),
        'Return', ('expr', 'e'),
        'ReturnNothing',
        'While', ('test', 'e'), ('body', 'Body(e)'))

Stmt, S, Assert, Nop, WriteExtrinsic = \
    ADT(('Stmt', CoreStmt, {CoreExpr: Expr}),
        'Assert', ('test', 'e'), ('message', 'e'),
        'Nop',
        'WriteExtrinsic', ('extrinsic', '*Extrinsic'), ('node', 'e'),
                          ('val', 'e'), ('isNew', bool))

LitDecl = DT('LitDecl', ('var', Var), ('literal', CoreLiteral))

ModuleDecls = DT('ModuleDecls',
        ('cdecls', [Var]),
        ('dts', [DataType]),
        ('envs', [Env]),
        ('extrinsics', [Extrinsic]),
        ('lits', [LitDecl]),
        ('funcDecls', [Var]))

def blank_module_decls():
    return ModuleDecls([], [], [], [], [], [])

TopFunc = DT('TopFunc', ('var', '*Var'), ('func', 'Func(Expr)'))

CompilationUnit = DT('CompilationUnit', ('funcs', [TopFunc]))

STMTCTXT = new_env('STMTCTXT', '*Stmt')
EXPRCTXT = new_env('EXPRCTXT', '*Expr')
UNIFYCTXT = new_env('UNIFYCTXT', '(*Type, *Type)')

def with_context(desc, msg):
    if have_env(UNIFYCTXT):
        src, dest = env(UNIFYCTXT)
        desc = fmtcol("^DG^Types:^N {0} ^DG\n=====>^N {1}\n{2}",src,dest,desc)
    if have_env(EXPRCTXT):
        desc = fmtcol("^DG^Expr:^N {0}\n{1}", env(EXPRCTXT), desc)
    desc = fmtcol("\n^DG^At:^N {0}\n{1}", env(STMTCTXT), desc)
    return fmtcol("^DG{0}^N\n^Red{1}^N", desc, msg)

def builtin_ref(name):
    return E.Bind(BUILTINS[name])

def builtin_call(name, args):
    return E.Call(builtin_ref(name), args)

def lit_type(lit):
    return match(lit, ("IntLit(_)", TInt),
                      ("FloatLit(_)", TFloat),
                      ("StrLit(_)", TStr))

Bindable = new_typeclass('Bindable',
        ('isVar', 'a -> Var', lambda v: Nothing()))

# This is silly
# Maybe can have types opt-in to RTTI?
# Or just use Bindable a => a in prop and expand

@impl(Bindable, Var)
def isVar_Var(var):
    return Just(var)

default_impl(Bindable, Builtin)
default_impl(Bindable, Ctor)

# XXX only become bindable after expansion (ought to be a different typeclass)
default_impl(Bindable, Extrinsic)
default_impl(Bindable, Env)

# XXX maybe codegen
Nullable = new_typeclass('Nullable', ('isMaybe', 'a -> bool', lambda v: False))
@impl(Nullable, Ctor)
def isMaybe_Ctor(ctor):
    name = extrinsic(Name, ctor)
    return name == 'Just' or name == 'Nothing'
default_impl(Nullable, Builtin)
default_impl(Nullable, Var)

@matcher('key')
def _match_key(atom, ast):
    assert len(ast.args) == 1
    name = ast.args[0].value
    target = BUILTINS.get(name)
    return [] if atom is target else None

@matcher('sym')
def _match_sym(atom, ast):
    assert 2 <= len(ast.args) <= 3
    mod_name = ast.args[0].value
    assert mod_name in loaded_modules, "%s not loaded" % mod_name
    mod = loaded_modules[mod_name]
    if isinstance(atom, Ref):
        r = atom.refAtom
        if isinstance(r, Ref) and r.refAtom is _b_symbol:
            for sub in r.subs:
                if getattr(sub, 'refAtom', None) is _b_name:
                    nm = sub.subs[0].strVal
                    break
            else:
                return None
            m = match_try(nm, ast.args[1])
            if m is None or len(ast.args) == 2:
                return m
            msubs = match_try(atom.subs, ast.args[2])
            if msubs is not None:
                return m + msubs
    return None

@matcher('named')
def _match_named(atom, ast):
    assert len(ast.args) == 1
    if has_extrinsic(Name, atom):
        return match_try(extrinsic(Name, atom), ast.args[0])
    return None

def walk_deps(func, mod, seen):
    def walk(deps):
        for dep in deps:
            if dep in seen:
                continue
            seen.add(dep)
            walk(extrinsic(ModDeps, dep))
            func(dep)
    walk(extrinsic(ModDeps, mod))
    return seen

ModRepr = DT('ModRepr', ('write', 'str -> void'),
                        ('indent', int),
                        ('exts', [object]),
                        ('seen', set([object])),
                        ('weakIndices', {object: int}),
                        ('weakCtr', int))
MODREPR = new_env('MODREPR', ModRepr)

def write_mod_repr(filename, m, exts):
    with file(filename, 'w') as f:
        def write(x):
            f.write('%s%s\n' % ('  ' * env(MODREPR).indent, x))
        init = ModRepr(write, 0, exts, set(), {}, 0)
        in_env(MODREPR, init, lambda: _do_repr(m.root))

def _do_repr(s):
    c = env(MODREPR)
    if isinstance(s, Structured):
        dt = type(s)
        if s in c.seen:
            if s in c.weakIndices:
                c.write('<cyclic #%d>' % c.weakIndices[s])
            else:
                c.write('<cyclic %s 0x%x>' % (dt.__name__, id(s)))
            return
        c.seen.add(s)
        name = dt.__name__
        if s in c.weakIndices:
            name = '%s #%d' % (name, c.weakIndices[s])
        for ext in c.exts:
            if has_extrinsic(ext, s):
                name = '%s %s' % (name, extrinsic(ext, s))
        c.write(name)
        c.indent += 1
        form = extrinsic(FormSpec, dt)
        assert not isinstance(form, DataType)
        for field in form.fields:
            f = getattr(s, extrinsic(Name, field))
            p = match(field.type, ("TWeak(p)", Just), ("_", Nothing))
            if isJust(p):
                if isinstance(f, Structured):
                    if has_extrinsic(Name, f):
                        c.write('->%s' % (extrinsic(Name, f),))
                    else:
                        if f not in c.weakIndices:
                            c.weakCtr += 1
                            c.weakIndices[f] = c.weakCtr
                        c.write('->#%d %r' % (c.weakIndices[f], f))
                else:
                    c.write('->?? %r' % (f,))
            else:
                _do_repr(f)
        c.indent -= 1
    elif isinstance(s, (tuple, list)):
        l, r = '()' if isinstance(s, tuple) else '[]'
        if not s:
            c.write(fmtcol('^Blue{0}{1}^N', l, r))
        else:
            c.write(fmtcol('^Blue{0}^N', l))
            for o in s:
                _do_repr(o)
            c.write(fmtcol('^Blue{0}^N', r))
    elif isinstance(s, value_types):
        c.write(repr(s))
    else:
        assert False, "Can't deal with %r" % (s,)

STRINGIFY = new_env('STRINGIFY', [str])

def stringify(ast, t):
    t = parse_type(t)
    frags = []
    in_env(STRINGIFY, frags, lambda: visit(ExprStringifier, ast, t))
    return ''.join(frags)

def frag(s):
    env(STRINGIFY).append(s)
def frag_comma():
    frag(', ')

class ExprStringifier(Visitor):
    def Attr(self, a):
        self.visit('expr')
        frag('.%s' % (extrinsic(Name, a.field),))

    def Bind(self, bind):
        t = bind.target
        if has_extrinsic(Original, t):
            orig = extrinsic(Original, t)
            if matches(orig, "Lit(_)"):
                frag(repr(orig.literal.val))
                return
        frag(extrinsic(Name, t) if has_extrinsic(Name, t) else '<unnamed>')

    def Call(self, call):
        if matches(call.func, 'Bind(Builtin())'):
            if len(call.args) == 2:
                op = extrinsic(Name, call.func.target)
                if op == 'subscript':
                    self.visit('args', 0)
                    frag('[')
                    self.visit('args', 1)
                    frag(']')
                    return
                self.visit('args', 0)
                frag(' %s ' % (op,))
                self.visit('args', 1)
                return
            elif len(call.args) == 1:
                m = match(call.func.target)
                if m('key("not")'):
                    frag('!')
                    self.visit('args', 0)
                    return
                elif m('key("negate")'):
                    frag('-')
                    self.visit('args', 0)
                    return
        self.visit('func')
        frag('(')
        for i in xrange(len(call.args)):
            if i > 0:
                frag_comma()
            self.visit('args', i)
        frag(')')

    def Lit(self, lit):
        frag(repr(lit.literal.val))

    def Ternary(self, lit):
        self.visit('test')
        frag(' ? ')
        self.visit('then')
        frag(' : ')
        self.visit('else_')

    def And(self, e):
        self.visit('left')
        frag(' and ')
        self.visit('right')
    def Or(self, e):
        self.visit('left')
        frag(' or ')
        self.visit('right')

    def TupleLit(self, lit):
        frag('[')
        for i in xrange(len(lit.vals)):
            if i > 0:
                frag_comma()
            self.visit('vals', i)
        frag(']')
    def ListLit(self, lit):
        frag('[')
        for i in xrange(len(lit.vals)):
            if i > 0:
                frag_comma()
            self.visit('vals', i)
        frag(']')
    def DictLit(self, lit):
        assert False

    def NullPtr(self, null):
        frag('null')
    def WithVar(self, expr):
        self.visit('expr')

    def FuncExpr(self, fe):
        frag('<function %s>' % (extrinsic(Name, fe.func),))

    def InEnv(self, e):
        frag('in_env(%s' % (extrinsic(Name, e.env),))
        frag_comma()
        self.visit('init')
        frag_comma()
        self.visit('expr')
        frag(')')

    def ScopeExtrinsic(self, e):
        frag('scope_extrinsic(%s' % (extrinsic(Name, e.extrinsic),))
        frag_comma()
        self.visit('expr')
        frag(')')

    def Match(self, m):
        frag('match(')
        self.visit('expr')
        frag_comma()
        frag('...)')

    # PATTERNS

    def PatVar(self, pat):
        frag(extrinsic(Name, pat.var))

    def PatWild(self, pat):
        frag('_')

    def LhsVar(self, lhs):
        frag(extrinsic(Name, lhs.var))

    def LhsAttr(self, lhs):
        self.visit('sub')
        frag('.%s' % (extrinsic(Name, lhs.attr),))

    # STMTS

    def Assign(self, a):
        self.visit('lhs')
        frag(' = ')
        self.visit('expr')

    def AugAssign(self, a):
        self.visit('lhs')
        self.visit('op')
        self.visit('expr')

    def AugAdd(self, a): frag(' += ')
    def AugSubtract(self, a): frag(' -= ')
    def AugMultiply(self, a): frag(' *= ')
    def AugDivide(self, a): frag(' //= ')
    def AugModulo(self, a): frag(' %= ')

    def Break(self, b): frag('break')
    def Continue(self, c): frag('continue')

    def Cond(self, cond):
        pass # first if case done manually in llvm

    def CondCase(self, case):
        frag('elif ')
        self.visit('test')
        frag(':')

    def Defn(self, defn):
        self.visit('pat')
        frag(' := ')
        self.visit('expr')

    def Return(self, ret):
        frag('return ')
        self.visit('expr')

    def ReturnNothing(self, ret):
        frag('return')

    def While(self, w):
        frag('while ')
        self.visit('test')
        frag(':')

    def Assert(self, a):
        frag('assert ')
        self.visit('test')
        frag_comma()
        self.visit('message')

    def WriteExtrinsic(self, a):
        frag('add_extrinsic(' if a.isNew else 'update_extrinsic(')
        frag(extrinsic(Name, a.extrinsic))
        frag_comma()
        self.visit('node')
        frag_comma()
        self.visit('val')
        frag(')')

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
