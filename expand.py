#!/usr/bin/env python2
from base import *
from atom import *
from quilt import *
import globs
import vat

ExFunc, ExStaticDefn, ExInnerFunc = ADT('ExFunc',
        'ExStaticDefn',
        'ExInnerFunc', ('closedVars', 'set([*Var])'),
                       ('outerFunc', '*ExFunc'))

EXFUNC = new_env('EXFUNC', ExFunc)

ExGlobal = DT('ExGlobal', ('newDecls', ModuleDecls),
                          ('newDefns', [TopFunc]),
                          ('ownModules', ['*Module']))

EXGLOBAL = new_env('EXGLOBAL', ExGlobal)

IMPORTBINDS = new_env('IMPORTBINDS', set(['a'])) # Bindable

CtorIndex = new_extrinsic('CtorIndex', int)
FieldIndex = new_extrinsic('FieldIndex', int)

# DEFNS

ClosureInfo = DT('ClosureInfo', ('func', Func), ('isClosure', bool))
Closure = new_extrinsic('Closure', ClosureInfo)

ClosedVarFunc = new_extrinsic('ClosedVar', ExFunc)

LocalFunctionSymbol = new_extrinsic('LocalFunctionSymbol', str)

GeneratedLocal = new_extrinsic('GeneratedLocal', bool)

def iconvert(a):
    add_extrinsic(LLVMTypeOf, a, convert_type(extrinsic(TypeOf, a)))

def copy_type(dest, src):
    # bleh... vat?
    add_extrinsic(LLVMTypeOf, dest, extrinsic(LLVMTypeOf, src))
    if has_extrinsic(TypeCast, src):
        add_extrinsic(TypeCast, dest, extrinsic(TypeCast, src))

def runtime_call(name, args):
    f = RUNTIME[name]
    bind = E.Bind(f)
    copy_type(bind, f)
    return E.Call(bind, args)

class VarCloser(vat.Visitor):
    def TopFunc(self, top):
        in_env(EXFUNC, ExStaticDefn(), lambda: self.visit('func'))

    def Defn(self, defn):
        m = match(defn)
        if m("Defn(PatVar(var), FuncExpr(f))"):
            # Extract function-in-function
            var, f = m.args
            info = ExInnerFunc(set(), env(EXFUNC))
            in_env(EXFUNC, info, lambda: self.visit('expr'))
            isClosure = len(info.closedVars) > 0
            glob = env(EXGLOBAL)
            glob.newDecls.funcDecls.append(var)
            glob.newDefns.append(TopFunc(var, f))
            add_extrinsic(Closure, f, ClosureInfo(f, isClosure))

    def PatVar(self, pat):
        add_extrinsic(ClosedVarFunc, pat.var, env(EXFUNC))

    def Bind(self, bind):
        mv = Bindable.isVar(bind.target)
        if isJust(mv):
            m = match(env(EXFUNC))
            if m('f==ExInnerFunc(closedVars, _)'):
                f, closedVars = m.args
                v = fromJust(mv)
                if has_extrinsic(ClosedVarFunc, v):
                    if extrinsic(ClosedVarFunc, v) is not f:
                        closedVars.add(v)


class FuncExpander(vat.Mutator):
    def Defn(self, defn):
        if matches(defn, "Defn(PatVar(_), FuncExpr(_))"):
            return Nop()
        return self.mutate()

    def FuncExpr(self, fe):
        # Extract lambda expression
        info = ExInnerFunc(set(), env(EXFUNC))
        f = in_env(EXFUNC, info, lambda: self.mutate('func'))
        isClosure = len(info.closedVars) > 0
        var = Var()
        glob = env(EXGLOBAL)
        glob.newDecls.funcDecls.append(var)
        glob.newDefns.append(TopFunc(var, f))
        add_extrinsic(Closure, f, ClosureInfo(f, isClosure))
        bind = E.Bind(var)
        t = extrinsic(TypeOf, f)
        add_extrinsic(TypeOf, bind, t)
        add_extrinsic(TypeOf, var, t)
        return bind

def expand_closures(unit):
    t = t_DT(CompilationUnit)
    vat.visit(VarCloser, unit, t)
    vat.mutate(FuncExpander, unit, t)

class LitExpander(vat.Mutator):
    def Lit(self, lit):
        m = match(lit.literal)
        if m('StrLit(_)'):
            v = Var()
            add_extrinsic(Name, v, '.LC%d' % (vat.orig_loc(lit).index,))
            vat.set_orig(v, lit)
            env(EXGLOBAL).newDecls.lits.append(LitDecl(v, lit.literal))
            expr = E.Bind(v)
            add_extrinsic(TypeOf, expr, TStr())
            add_extrinsic(TypeOf, v, TStr())
            return expr
        else:
            return lit

def convert_decl_types(decls):
    map_(iconvert, decls.cdecls)
    for dt in decls.dts:
        for ctor in dt.ctors:
            for field in ctor.fields:
                add_extrinsic(LLVMTypeOf, field, convert_type(field.type))
    for env in decls.envs:
        add_extrinsic(LLVMTypeOf, env, convert_type(env.type))
    for lit in decls.lits:
        iconvert(lit.var)
    map_(iconvert, decls.funcDecls)

THREADENV = new_env('THREADENV', 'Maybe(Var)')

class TypeConverter(vat.Visitor):
    def t_Expr(self, e):
        self.visit()
        iconvert(e)

    def Var(self, v):
        iconvert(v)

    def Func(self, f):
        self.visit('params')

        threadedVar = Nothing()
        if extrinsic(TypeOf, f).meta.takesEnv:
            # Add context parameter
            var = Var()
            add_extrinsic(Name, var, 'ctx')
            add_extrinsic(LLVMTypeOf, var, IVoidPtr())
            add_extrinsic(GeneratedLocal, var, True)
            threadedVar = Just(var)
            f.params.append(var)

        in_env(THREADENV, threadedVar, lambda: self.visit('body'))
        iconvert(f)

    def Call(self, e):
        self.visit('func')
        self.visit('args')
        if extrinsic(TypeOf, e.func).meta.takesEnv:
            m = match(env(THREADENV))
            if m('Just(ctx)'):
                ctx = m.arg
                bind = E.Bind(ctx)
                copy_type(bind, ctx)
                m.ret(bind)
            else:
                null = E.NullPtr()
                add_extrinsic(LLVMTypeOf, null, IVoidPtr())
                m.ret(null)
            e.args.append(m.result())
        iconvert(e)

class EnvExtrConverter(vat.Mutator):
    def GetEnv(self, e):
        call = runtime_call('_getenv', [bind_env(e.env)])
        copy_type(call, e)
        return call

    def HaveEnv(self, e):
        call = runtime_call('_haveenv', [bind_env(e.env)])
        copy_type(call, e)
        return call

    def GetExtrinsic(self, e):
        extr = bind_extrinsic(e.extrinsic)
        node = self.mutate('node')
        call = runtime_call('_getextrinsic', [extr, node])
        copy_type(call, e)
        return call

    def HasExtrinsic(self, e):
        extr = bind_extrinsic(e.extrinsic)
        node = self.mutate('node')
        call = runtime_call('_hasextrinsic', [extr, node])
        copy_type(call, e)
        return call

    def ScopeExtrinsic(self, e):
        return self.mutate('expr') # TEMP

    def WriteExtrinsic(self, s):
        f = '_addextrinsic' if s.isNew else '_updateextrinsic'
        extr = bind_extrinsic(s.extrinsic)
        node = self.mutate('node')
        val = self.mutate('val')
        e = runtime_call(f, [extr, node, val])
        add_extrinsic(LLVMTypeOf, e, IVoid())
        return S.ExprStmt(e)

def bind_env(e):
    bind = E.Bind(e)
    add_extrinsic(LLVMTypeOf, bind, IVoidPtr())
    return bind

def bind_extrinsic(extr):
    bind = E.Bind(extr)
    add_extrinsic(LLVMTypeOf, bind, IVoidPtr())
    return bind

class ImportMarker(vat.Visitor):
    def Bind(self, bind):
        tar = bind.target
        if has_extrinsic(GeneratedLocal, tar):
            return
        external = has_extrinsic(CFunction, tar) and extrinsic(CFunction, tar)
        if not external:
            external = vat.orig_loc(tar).module not in env(EXGLOBAL).ownModules
        if external:
            env(IMPORTBINDS).add(tar)

LayoutInfo = DT('LayoutInfo', ('extrSlot', 'Maybe(int)'),
                              ('discrimSlot', 'Maybe(int)'))
DataLayout = new_extrinsic('DataLayout', LayoutInfo)

def dt_layout(dt):
    base = 0
    info = LayoutInfo(Nothing(), Nothing())
    if not dt.opts.valueType:
        info.extrSlot = Just(base)
        base += 1
    if len(dt.ctors) > 1:
        info.discrimSlot = Just(base)
        base += 1
    add_extrinsic(DataLayout, dt, info)
    for i, ctor in enumerate(dt.ctors):
        add_extrinsic(CtorIndex, ctor, i)
        for ix, field in enumerate(ctor.fields):
            add_extrinsic(FieldIndex, field, ix + base)


GlobalInfo = DT('GlobalInfo', ('symbol', str), ('isFunc', bool))
GlobalSymbol = new_extrinsic('GlobalSymbol', GlobalInfo)

CFunction = new_extrinsic('CFunction', bool)

def unique_global(v, isFunc):
    # Would prefer not to do this check
    # Need firmer uniquer pass order
    if has_extrinsic(GlobalSymbol, v):
        symbol = extrinsic(GlobalSymbol, v).symbol
    else:
        symbol = extrinsic(Name, v)
        add_extrinsic(GlobalSymbol, v, GlobalInfo(symbol, isFunc))
    return symbol

def unique_static_global(v):
    name = extrinsic(Name, v)
    add_extrinsic(LocalFunctionSymbol, v, name)
    return name

class Uniquer(vat.Visitor):
    def TopFunc(self, top):
        # somewhat redundant with unique_decls()
        # however currently we don't know which order they'll be called in...
        sym = unique_global(top.var, True)
        add_extrinsic(Name, top.func, sym)
        self.visit()

    def Defn(self, defn):
        m = match(defn)
        if m("Defn(PatVar(var), FuncExpr(f))"):
            var, f = m.args
            add_extrinsic(Name, f, unique_static_global(var))
            self.visit('expr')
        else:
            self.visit()

def unique_decls(decls):
    for v in decls.cdecls:
        unique_global(v, True)

        # XXX: avoid this check
        # (shouldn't be uniquing the old decls anyway)
        if not has_extrinsic(CFunction, v):
            add_extrinsic(CFunction, v, True)

    for env in decls.envs:
        unique_global(env, False)
    for extr in decls.extrinsics:
        unique_global(extr, False)

    for var in decls.funcDecls:
        unique_global(var, True)
    for lit in decls.lits:
        unique_global(lit.var, False)

# GLUE

def expand_decls(decls):
    convert_decl_types(decls)
    finish_decls(decls)

def finish_decls(decls):
    map_(dt_layout, decls.dts)
    unique_decls(decls)

def expand_unit(decls, unit):
    t = t_DT(CompilationUnit)
    scope_extrinsic(ClosedVarFunc, lambda: expand_closures(unit))
    vat.mutate(LitExpander, unit, t)

    # Prepend generated TopFuncs now
    unit.funcs = env(EXGLOBAL).newDefns + unit.funcs

    convert_decl_types(decls)
    vat.visit(TypeConverter, unit, t)

    vat.mutate(EnvExtrConverter, unit, t)

    finish_decls(decls)

    vat.visit(ImportMarker, unit, t)
    vat.visit(Uniquer, unit, t)

def in_intramodule_env(func):
    captures = {}
    extrs = [Closure, LocalFunctionSymbol, vat.Original, GeneratedLocal]
    return in_env(IMPORTBINDS, set(),
            lambda: capture_scoped(extrs, captures, func))

def in_intermodule_env(func):
    captures = {}
    extrs = [LLVMTypeOf, DataLayout, CtorIndex, FieldIndex,
            GlobalSymbol, CFunction]
    return capture_scoped(extrs, captures, func)

def expand_module(decl_mod, defn_mod):
    expand_decls(decl_mod.root)

    # Clone decls and defns as mutable replacements
    def clone():
        decls = vat.clone(decl_mod.root, [Name, TypeOf, CFunction])
        unit = vat.clone(defn_mod.root, [Name, TypeOf])
        vat.rewrite(unit)
        return decls, unit
    new_decls, new_unit = vat.in_vat(clone)

    # Mutate clones
    in_env(EXGLOBAL, ExGlobal(new_decls, [], [decl_mod, defn_mod]),
        lambda: expand_unit(new_decls, new_unit))

    return (new_decls, new_unit)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
