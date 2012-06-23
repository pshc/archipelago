#!/usr/bin/python2
from os import system
from hashlib import sha256
from base import *
from bedrock import *
from globs import *
from types_builtin import *
import types

types_by_name['set'] = lambda: TData(Set.__dt__.__form__)

# Shouldn't this be an env or something?
BUILTINS = {}

Builtin = DT('Builtin')

Env = DT('Env', ('type', Type))

Extrinsic = DT('Extrinsic', ('type', Type))

Var = DT('Var')

Binding, BindBuiltin, BindCtor, BindVar = \
    ADT('Binding',
        'BindBuiltin', ('builtin', '*Builtin'),
        'BindCtor', ('ctor', '*Ctor'),
        'BindVar', ('var', '*Var'))

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

Expr, And, Attr, Bind, Call, DictLit, FuncExpr, GenExpr, \
        GetEnv, GetExtrinsic, InEnv, \
        IntLit, ListLit, Match, Or, StrLit, Ternary, TupleLit = \
    ADT('Expr',
        'And', ('left', 'Expr'), ('right', 'Expr'),
        'Attr', ('expr', 'Expr'), ('field', '*Field'),
        'Bind', ('binding', 'Binding'),
        'Call', ('func', 'Expr'), ('args', '[Expr]'),
        'DictLit', ('vals', '[(Expr, Expr)]'),
        'FuncExpr', ('func', 'Func'),
        'GenExpr', ('expr', 'Expr'), ('pattern', 'Pat'),
                   ('listExpr', 'Expr'), ('preds', '[Expr]'),
        'GetEnv', ('env', '*Env'),
        'GetExtrinsic', ('extrinsic', '*Extrinsic'), ('node', 'Expr'),
        'InEnv', ('env', '*Env'), ('init', 'Expr'), ('expr', 'Expr'),
        'IntLit', ('val', int),
        'ListLit', ('vals', '[Expr]'),
        'Match', ('expr', 'Expr'), ('cases', [MatchCase]),
        'Or', ('left', 'Expr'), ('right', 'Expr'),
        'StrLit', ('val', str),
        'Ternary', ('test', 'Expr'), ('then', 'Expr'), ('else_', 'Expr'),
        'TupleLit', ('vals', '[Expr]'))

AugOp, AugAdd, AugSubtract, AugMultiply, AugDivide, AugModulo = ADT('AugOp',
        'AugAdd', 'AugSubtract', 'AugMultiply', 'AugDivide', 'AugModulo')

Body = DT('Body', ('stmts', '[Stmt]'))

CondCase = DT('CondCase', ('test', Expr), ('body', Body))

Func = DT('Func', ('params', [Var]), ('body', Body))

Lhs, LhsVar, LhsAttr, LhsTuple = ADT('Lhs',
        'LhsVar', ('var', '*Var'),
        'LhsAttr', ('sub', Expr), ('attr', '*Field'),
        'LhsTuple', ('vals', '[Lhs]'))

Stmt, Assert, Assign, AugAssign, Break, Cond, Continue, Defn, \
    ExprStmt, Return, ReturnNothing, While = \
    ADT('Stmt',
        'Assert', ('test', Expr), ('message', Expr),
        'Assign', ('lhs', Lhs), ('expr', Expr),
        'AugAssign', ('op', AugOp), ('lhs', Lhs), ('expr', Expr),
        'Break',
        'Cond', ('cases', [CondCase]), ('elseCase', 'Maybe(Body)'),
        'Continue',
        'Defn', ('var', 'Var'), ('expr', Expr),
        'ExprStmt', ('expr', Expr),
        'Return', ('expr', Expr),
        'ReturnNothing',
        'While', ('test', Expr), ('body', Body))

TopLevel, TopDefn, TopDT, TopExtrinsic, TopEnv = \
    ADT('TopLevel',
        'TopDefn', ('var', Var), ('expr', Expr),
        'TopDT', ('form', 'DataType'),
        'TopExtrinsic', ('extrinsic', Extrinsic),
        'TopEnv', ('env', Env))

STMTCTXT = new_env('STMTCTXT', '*Stmt')
EXPRCTXT = new_env('EXPRCTXT', '*Expr')

CompilationUnit = DT('CompilationUnit', ('tops', [TopLevel]))

def symcall(name, params):
    return Call(Bind(BindBuiltin(BUILTINS[name])), params)

def getname(sym):
    return match(sym, ('named(nm)', identity))

def _fix_type(t):
    return t() if isinstance(t, (type, types.FunctionType)) else t

def make_builtin_scheme(name, t):
    tvars = {}
    if t is None:
        assert False, 'Unknown builtin %s' % (name,)
    if isinstance(t, tuple):
        if None in t:
            assert False, 'Incomplete builtin %s: %s' % (name, t)
        t = map(_fix_type, t)
        t = TFunc(t[:-1], t[-1])
    else:
        t = _fix_type(t)
    def builtin_typevar(v):
        index = match(v, ('TVar(n)', identity))
        if index not in tvars:
            tvar = TypeVar()
            add_extrinsic(Name, tvar, chr(96 + index))
            tvars[index] = tvar
        return TVar(tvars[index])
    t = map_type_vars(builtin_typevar, t)
    return t, tvars

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

ModRepr = DT('ModRepr', ('write', 'str -> void'),
                        ('indent', int),
                        ('exts', [object]),
                        ('seen', set([object])),
                        ('weakIndices', {object: int}),
                        ('weakCtr', int))
MODREPR = new_env('MODREPR', ModRepr)

def write_mod_repr(filename, m, exts):
    with file(filename, 'w') as f:
        had_color = env(GENOPTS).color
        env(GENOPTS).color = False

        def write(x):
            f.write('%s%s\n' % ('  ' * env(MODREPR).indent, x))
        init = ModRepr(write, 0, exts, set(), {}, 0)
        in_env(MODREPR, init, lambda: _do_repr(m.root))

        env(GENOPTS).color = had_color

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
        brief = pretty_brief(name, s)
        if s in c.weakIndices:
            name = '%s #%d' % (name, c.weakIndices[s])
        for ext in c.exts:
            if has_extrinsic(ext, s):
                name = '%s %s' % (name, extrinsic(ext, s))
        c.write(name)
        c.indent += 1
        form = dt.__form__
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
            c.write(l + r)
        else:
            c.write(l)
            for o in s:
                _do_repr(o)
            c.write(r)
    elif isinstance(s, value_types):
        c.write(repr(s))
    else:
        assert False, "Can't deal with %r" % (s,)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
