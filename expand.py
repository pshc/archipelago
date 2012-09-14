#!/usr/bin/env python2
from base import *
from atom import *
import globs
import vat

FlowNode = DT('FlowNode', ('outflows', 'set([FlowNode])'),
                          ('returns', bool))

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

# TRAINWRECK

ClosureInfo = DT('ClosureInfo', ('func', Func), ('isClosure', bool))
Closure = new_extrinsic('Closure', ClosureInfo)

GlobalInfo = DT('GlobalInfo', ('symbol', str), ('isFunc', bool))
GlobalSymbol = new_extrinsic('GlobalSymbol', GlobalInfo)
LocalFunctionSymbol = new_extrinsic('LocalFunctionSymbol', str)

VarUsageInfo = DT('VarUsageInfo', ('isReassigned', bool))
VarUsage = new_extrinsic('VarUsage', VarUsageInfo)

VarInfo = DT('VarInfo', ('function', ExFunc))
LocalVar = new_extrinsic('LocalVar', VarInfo)

CtorIndex = new_extrinsic('CtorIndex', int)
FieldIndex = new_extrinsic('FieldIndex', int)

LayoutInfo = DT('LayoutInfo', ('extrSlot', 'Maybe(int)'),
                              ('discrimSlot', 'Maybe(int)'))
DataLayout = new_extrinsic('DataLayout', LayoutInfo)

def orig_loc(obj):
    # Ugh, I don't like the conditional check...
    if has_extrinsic(vat.Original, obj):
        obj = extrinsic(vat.Original, obj)
    return extrinsic(Location, obj)

# DEFNS

class UnitMutator(vat.Mutator):
    def Defn(self, defn):
        m = match(defn)
        if m("Defn(PatVar(v), FuncExpr(f))"):
            # Globalify function-in-function
            var, f = m.args

            # Skip ex_pat_var since this is becoming global?
            name = extrinsic(Name, var) # ought to be uniqued
            add_extrinsic(Name, f, name)
            add_extrinsic(LocalFunctionSymbol, var, name)

            info = ex_func(f.params, f.body)
            isClosure = len(info.closedVars) > 0
            glob = env(EXGLOBAL)
            glob.newDecls.funcDecls.append(var)
            glob.newDefns.append(TopFunc(var, f))
            add_extrinsic(Closure, f, ClosureInfo(f, isClosure))

            # now need to replace all references with binds to that var...

        else:
            defn.pat = self.mutate(defn.pat)
            defn.expr = self.mutate(defn.expr)
        return defn

    def FuncExpr(self, f):
        # Globalify lambda expression
        info = ex_func(f.params, f.body)
        isClosure = len(info.closedVars) > 0
        var = Var()
        glob = env(EXGLOBAL)
        glob.newDecls.funcDecls.append(var)
        glob.newDefns.append(TopFunc(var, f))
        add_extrinsic(Closure, f, ClosureInfo(f, isClosure))
        return Bind(var)

    def Lit(self, lit):
        m = match(lit)
        if m('StrLit(s)'):
            s = m.arg
            v = Var()
            add_extrinsic(Name, v, '.LC%d' % (orig_loc(lit).index,))
            env(EXGLOBAL).newDecls.lits.append(LitDecl(v, StrLit(s)))
            return Bind(v)
        else:
            return lit

class VarVisitor(vat.Visitor):
    def TopFunc(self, top):
        add_extrinsic(Name, top.func, extrinsic(Name, top.var))
        unique_global(top.var, True)
        in_env(EXFUNC, ExStaticDefn(), lambda: self.visit(top.func))

    def Bind(self, bind):
        target = bind.target
        if orig_loc(target).module not in env(EXGLOBAL).ownModules:
            env(IMPORTBINDS).add(target)
        v = Bindable.isVar(target)
        if isJust(v):
            ex_bind_var(fromJust(v))

    def LhsVar(self, lhs):
        # this isn't a binding, why call this?
        ex_bind_var(lhs.var)

        if not has_extrinsic(VarUsage, lhs.var):
            add_extrinsic(VarUsage, lhs.var, VarUsageInfo(True))

    def PatVar(self, pat):
        add_extrinsic(LocalVar, pat.var, VarInfo(env(EXFUNC)))

    def Assign(self, ass):
        # reversed order (XXX: multiple passes will deprecate this)
        self.visit(ass.expr)
        self.visit(ass.lhs)

    def AugAssign(self, ass):
        # as above
        self.visit(ass.expr)
        self.visit(ass.lhs)

def ex_bind_var(self, v):
    m = match(env(EXFUNC))
    if m('f==ExInnerFunc(closVars, _)'):
        f, closVars = m.args
        if has_extrinsic(LocalVar, v):
            assert isinstance(v, Var)
            info = extrinsic(LocalVar, v)
            if info.function != f:
                closVars.add(v)

# DECLS

def unique_global(v, isFunc):
    add_extrinsic(GlobalSymbol, v, GlobalInfo(extrinsic(Name, v), isFunc))

def ex_dt(dt):
    """Computes struct layout."""
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

def ex_top_cdecl(v):
    unique_global(v, True)

def expand_decls(decls):
    map(ex_top_cdecl, decls.cdecls)
    map(ex_dt, decls.dts)
    for lit in decls.lits:
        unique_global(lit.var, False)

def in_intramodule_env(func):
    captures = {}
    extrs = [Closure, VarUsage, LocalFunctionSymbol,
            vat.Original]
    return in_env(IMPORTBINDS, set(),
            lambda: capture_scoped(extrs, captures, func))

def in_intermodule_env(func):
    captures = {}
    extrs = [DataLayout, CtorIndex, FieldIndex, GlobalSymbol]
    return capture_scoped(extrs, captures, func)

def expand_module(decl_mod, defn_mod):
    expand_decls(decl_mod.root)

    # Clone decls and defns as mutable replacements
    def clone():
        decls = vat.clone(decl_mod.root, [Name, TypeOf])
        unit = vat.clone(defn_mod.root, [Name, TypeOf])
        vat.rewrite(unit)
        return decls, unit
    new_decls, new_unit = vat.in_vat(clone)

    # Expand over cloned definitions
    in_env(EXGLOBAL, ExGlobal(new_decls, [], [decl_mod, defn_mod]),
        lambda: scope_extrinsic(LocalVar,
        lambda: ex_unit(new_unit)
    ))

    # Finally, prepare our new decls
    expand_decls(new_decls)

    return (new_decls, new_unit)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
