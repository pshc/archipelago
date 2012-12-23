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
GlobalVar = DT('GlobalVar')

Pat, PatCtor, PatCapture, PatInt, PatStr, PatTuple, PatVar, PatWild = \
    ADT('Pat',
        'PatCtor', ('ctor', '*Ctor'), ('args', '[Pat]'),
        'PatCapture', ('var', Var), ('pattern', 'Pat'),
        'PatInt', ('val', int),
        'PatStr', ('val', str),
        'PatTuple', ('vals', '[Pat]'),
        'PatVar', ('var', Var),
        'PatWild')

MatchCase = DT('MatchCase', ('pat', Pat), ('result', 'e'))

CoreLiteral, IntLit, FloatLit, StrLit = ADT('CoreLiteral',
        'IntLit', ('val', int),
        'FloatLit', ('val', float),
        'StrLit', ('val', str))

CoreExpr, Attr, Bind, Call, Lit, TupleLit = \
    ADT('CoreExpr',
        'Attr', ('expr', 'CoreExpr'), ('field', '*Field'),
        'Bind', ('target', '*a'), # Binder a => a
        'Call', ('func', 'CoreExpr'), ('args', '[CoreExpr]'),
        'Lit', ('literal', CoreLiteral),
        'TupleLit', ('vals', '[CoreExpr]'))

Expr, E, And, DictLit, FuncExpr, GenExpr, \
        GetEnv, HaveEnv, InEnv, MakeCtx, \
        GetExtrinsic, HasExtrinsic, ScopeExtrinsic, \
        ListLit, Match, Or, Ternary = \
    ADT(('Expr', CoreExpr),
        'And', ('left', 'Expr'), ('right', 'Expr'),
        'DictLit', ('vals', '[(Expr, Expr)]'),
        'FuncExpr', ('func', 'Func(Expr)'),
        'GenExpr', ('expr', 'Expr'), ('pattern', 'Pat'),
                   ('listExpr', 'Expr'), ('preds', '[Expr]'),
        'GetEnv', ('env', '*Env'),
        'HaveEnv', ('env', '*Env'),
        'InEnv', ('env', '*Env'), ('init', 'Expr'), ('expr', 'Expr'),
        'MakeCtx', ('env', '*Env'), ('init', 'Expr'),
        'GetExtrinsic', ('extrinsic', '*Extrinsic'), ('node', 'Expr'),
        'HasExtrinsic', ('extrinsic', '*Extrinsic'), ('node', 'Expr'),
        'ScopeExtrinsic', ('extrinsic', '*Extrinsic'), ('expr', 'Expr'),
        'ListLit', ('vals', '[Expr]'),
        'Match', ('expr', 'Expr'), ('cases', ['MatchCase(Expr)']),
        'Or', ('left', 'Expr'), ('right', 'Expr'),
        'Ternary', ('test', 'Expr'), ('then', 'Expr'),
                   ('else_', 'Expr'))

AugOp, AugAdd, AugSubtract, AugMultiply, AugDivide, AugModulo = ADT('AugOp',
        'AugAdd', 'AugSubtract', 'AugMultiply', 'AugDivide', 'AugModulo')

Body = DT('Body', ('stmts', '[Stmt(e)]'))

CondCase = DT('CondCase', ('test', 'e'), ('body', 'Body(e)'))

BlockCondCase = DT('BlockCondCase', ('test', 'Body(e)'), ('body', 'Body(e)'))

Func = DT('Func', ('params', [Var]), ('body', 'Body(e)'))

Lhs, LhsVar, LhsAttr, LhsSlot = ADT('Lhs',
        'LhsVar', ('var', '*Var'),
        'LhsAttr', ('sub', 'e'), ('attr', '*Field'),
        # TODO move to quilt
        'LhsSlot', ('sub', 'e'), ('index', int))

VoidExpr, VoidCall, VoidInEnv = ADT('VoidExpr',
        'VoidCall', ('func', 'e'), ('args', ['e']),
        'VoidInEnv', ('env', '*Env'), ('init', 'e'), ('expr', 'VoidExpr(e)'))

CoreStmt, Assign, AugAssign, Break, Cond, Continue, Defn, \
    Return, ReturnNothing, While, VoidStmt = \
    ADT('CoreStmt',
        'Assign', ('lhs', 'Lhs(e)'), ('expr', 'e'),
        'AugAssign', ('op', AugOp), ('lhs', 'Lhs(e)'), ('expr', 'e'),
        'Break',
        'Cond', ('cases', ['CondCase(e)']),
        'Continue',
        'Defn', ('pat', Pat), ('expr', 'e'),
        'Return', ('expr', 'e'),
        'ReturnNothing',
        'While', ('test', 'e'), ('body', 'Body(e)'),
        'VoidStmt', ('voidExpr', 'VoidExpr(e)'))

Stmt, S, Assert, BlockCond, BlockMatch, BreakUnless, NextCase, Nop, \
        PushEnv, PopEnv, WriteExtrinsic = \
    ADT(('Stmt', CoreStmt, {CoreExpr: Expr}),
        'Assert', ('test', 'e'), ('message', 'e'),
        'BlockCond', ('cases', '[BlockCondCase(e)]'),
        'BlockMatch', ('expr', 'e'), ('cases', '[MatchCase(Body(e))]'),
        'BreakUnless', ('test', 'e'),
        'NextCase', ('test', 'e'),
        'Nop',
        'PushEnv', ('env', '*Env'), ('init', 'e'),
        'PopEnv', ('env', '*Env'),
        'WriteExtrinsic', ('extrinsic', '*Extrinsic'), ('node', 'e'),
                          ('val', 'e'), ('isNew', bool))

LitDecl = DT('LitDecl', ('var', GlobalVar), ('literal', CoreLiteral))

ModuleDecls = DT('ModuleDecls',
        ('cdecls', [GlobalVar]),
        ('dts', [DataType]),
        ('envs', [Env]),
        ('extrinsics', [Extrinsic]),
        ('lits', [LitDecl]),
        ('funcDecls', [GlobalVar]),
        # XXX hack; should store in serialized extrs
        ('grabBag', [GlobalVar]))

def blank_module_decls():
    return ModuleDecls([], [], [], [], [], [], [])

TopFunc = DT('TopFunc', ('var', '*GlobalVar'), ('func', 'Func(e)'))

CompilationUnit = DT('CompilationUnit', ('funcs', ['TopFunc(Expr)']))

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

def lit_type(lit):
    return match(lit, ("IntLit(_)", TInt),
                      ("FloatLit(_)", TFloat),
                      ("StrLit(_)", TStr))

Bindable = new_typeclass('Bindable',
        ('isLocalVar', 'a -> bool', lambda v: False),
        ('asLocalVar', 'a -> Maybe(Var)', lambda v: Nothing()))

# This is silly

@impl(Bindable, Var)
def isLocalVar_Var(var):
    return True
@impl(Bindable, Var)
def asLocalVar_Var(var):
    return Just(var)

default_impl(Bindable, GlobalVar)
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
default_impl(Nullable, GlobalVar)

@matcher('key')
def _match_key(atom, args):
    assert len(args) == 1
    name = args[0]['val']
    target = BUILTINS.get(name)
    return [] if atom is target else None

@matcher('sym')
def _match_sym(atom, args):
    assert 2 <= len(args) <= 3
    mod_name = args[0].val
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
            m = match_try(nm, args[1])
            if m is None or len(args) == 2:
                return m
            msubs = match_try(atom.subs, args[2])
            if msubs is not None:
                return m + msubs
    return None

@matcher('named')
def _match_named(atom, args):
    assert len(args) == 1
    if has_extrinsic(Name, atom):
        return match_try(extrinsic(Name, atom), args[0])
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

def write_mod_repr(filename, m, exts=[]):
    if not env(GENOPTS).dumpViews:
        return
    with file(filename, 'w') as f:
        def write(x):
            f.write('%s%s\n' % ('  ' * env(MODREPR).indent, x))
        init = ModRepr(write, 0, exts, set(), {}, 0)
        in_env(MODREPR, init, lambda: _do_repr(m.root))

def tree(atom, exts=[]):
    def write(x):
        print '%s%s' % ('  ' * env(MODREPR).indent, x)
    init = ModRepr(write, 0, exts, set(), {}, 10000)
    in_env(MODREPR, init, lambda: _do_repr(atom))

def _do_repr(s):
    c = env(MODREPR)
    if isinstance(s, Structured):
        dt = type(s)
        if s in c.seen:
            if s in c.weakIndices:
                c.write('<cyclic #%d>' % c.weakIndices[s])
            else:
                c.write('<cyclic %s %s>' % (dt.__name__, short_id(s)))
            return
        c.seen.add(s)
        name = [dt.__name__]
        if s in c.weakIndices:
            name.append('#%d' % (c.weakIndices[s],))
        if has_extrinsic(Name, s):
            name.append(fmtcol('^Red{0!r}^N', extrinsic(Name, s)))
        name.append(short_id(s))
        for ext in c.exts:
            if has_extrinsic(ext, s):
                name.append(repr(extrinsic(ext, s)))
        c.write(' '.join(name))
        c.indent += 1
        form = extrinsic(FormSpec, dt)
        assert not isinstance(form, DataType)
        for field in form.fields:
            f = getattr(s, extrinsic(Name, field))
            if matches(field.type, "TWeak(_)"):
                if isinstance(f, Structured):
                    if has_extrinsic(Name, f):
                        c.write('->%s %s' % (extrinsic(Name, f), short_id(f)))
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
        frag('.%s' % (extrinsic(FieldSymbol, a.field),))
    def AttrIx(self, a):
        self.visit('expr')
        frag('._ix')

    def Bind(self, bind):
        t = bind.target
        if has_extrinsic(Original, t):
            orig = extrinsic(Original, t)
            if matches(orig, "Lit(_)"):
                frag(repr(orig.literal.val))
                return
        if Bindable.isLocalVar(t):
            frag(var_name(t))
        elif has_extrinsic(GlobalSymbol, t):
            frag(global_name(t))
        else:
            frag(extrinsic(Name, t))
    def ReadGlobal(self, read):
        frag('@%s' % (global_name(read.var),))

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
    def VoidCall(self, call):
        self.Call(call)
    def CallIndirect(self, call):
        self.Call(call)

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
    def SizeOf(self, sizeof):
        m = match(sizeof)
        if m("SizeOf(IPtr(IData(dt) or IDataCtor(dt)))"):
            frag('sizeof %s' % (extrinsic(Name, m.dt),))
        else:
            frag('sizeof ...')
    def Undefined(self, undef):
        frag('undef')
    def FuncVal(self, e):
        ctx = match(e.ctx, ("Just(v)", var_name),
                           ("Nothing()", lambda: "null"))
        frag('{&%s, %s}' % (global_name(e.funcVar), ctx))

    def FuncExpr(self, fe):
        frag('<function %s>' % (extrinsic(Name, fe.func),))

    def InEnv(self, e):
        frag('in_env(%s' % (global_name(e.env),))
        frag_comma()
        self.visit('init')
        frag_comma()
        self.visit('expr')
        frag(')')
    def VoidInEnv(self, e):
        self.InEnv(e)

    def ScopeExtrinsic(self, e):
        frag('scope_extrinsic(%s' % (global_name(e.extrinsic),))
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
        frag(var_name(pat.var))

    def PatWild(self, pat):
        frag('_')

    def LhsVar(self, lhs):
        frag(var_name(lhs.var))

    def LhsAttr(self, lhs):
        self.visit('sub')
        frag('.%s' % (extrinsic(FieldSymbol, lhs.attr),))

    def LhsSlot(self, lhs):
        self.visit('sub')
        frag('.slot[%d]' % (lhs.index,))

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

    def Nop(self, nop):
        frag('nop')

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
        frag(global_name(a.extrinsic))
        frag_comma()
        self.visit('node')
        frag_comma()
        self.visit('val')
        frag(')')

def var_name(var):
    return extrinsic(LocalSymbol, var)

def global_name(target):
    return extrinsic(GlobalSymbol, target).symbol

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
