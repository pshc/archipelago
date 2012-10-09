#!/usr/bin/env python2
from base import *
from atom import *
from quilt import *
import globs
import vat

ExFunc, ExStaticDefn, ExInnerFunc = ADT('ExFunc',
        'ExStaticDefn',
        'ExInnerFunc', ('closedVars', 'set([*Var])'))

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

ClosedVarFunc = new_extrinsic('ClosedVar', '*ExFunc')
VarGlobalReplacement = new_extrinsic('VarGlobalReplacement', '*GlobalVar')

def iconvert(a):
    add_extrinsic(LLVMTypeOf, a, convert_type(extrinsic(TypeOf, a)))

def iconvert_func(a):
    add_extrinsic(LLVMTypeOf, a, convert_func_type(extrinsic(TypeOf, a)))

def copy_type(dest, src):
    # bleh... vat?
    add_extrinsic(LLVMTypeOf, dest, extrinsic(LLVMTypeOf, src))

def cast(src, dest, e):
    assert not itypes_equal(src, dest), "%s already of %s type" % (e, src)
    casted = Cast(src, dest, e)
    add_extrinsic(LLVMTypeOf, casted, dest)
    return casted

def cast_from_voidptr(e, t):
    return match(t, ('IVoidPtr()', lambda: e),
                    ('_', lambda: cast(IVoidPtr(), t, e)))

def cast_to_voidptr(e, t):
    return match(t, ('IVoidPtr()', lambda: e),
                    ('_', lambda: cast(t, IVoidPtr(), e)))

def runtime_call(name, args):
    f = RUNTIME[name]
    ft = extrinsic(LLVMTypeOf, f)
    bind = L.Bind(f)
    add_extrinsic(LLVMTypeOf, bind, ft)
    call = L.Call(bind, args)
    add_extrinsic(LLVMTypeOf, call, ft.ret)
    return call

def runtime_void_call(name, args):
    f = RUNTIME[name]
    bind = L.Bind(f)
    copy_type(bind, f)
    return S.VoidStmt(VoidCall(bind, args))

class ClosureExpander(vat.Mutator):
    def TopFunc(self, top):
        top.func = in_env(EXFUNC, ExStaticDefn(), lambda: self.mutate('func'))
        return top

    def Defn(self, defn):
        wasFuncExpr = matches(defn.expr, 'FuncExpr(_)')
        defn = self.mutate()
        if wasFuncExpr:
            # Special case: extract `f := lambda [...]` form directly
            m = match(defn)
            if m("Defn(PatVar(var), Bind(globalVar))"):
                var, globalVar = m.args
                add_extrinsic(VarGlobalReplacement, var, globalVar)
                update_extrinsic(Name, globalVar, extrinsic(Name, var))
                return Nop()
        return defn

    def FuncExpr(self, fe):
        # Extract any other (inline) func expression
        info = ExInnerFunc(set())
        f = in_env(EXFUNC, info, lambda: self.mutate('func'))
        isClosure = len(info.closedVars) > 0
        var = GlobalVar()
        glob = env(EXGLOBAL)
        glob.newDecls.funcDecls.append(var)
        glob.newDefns.append(TopFunc(var, f))
        add_extrinsic(Closure, f, ClosureInfo(f, isClosure))
        bind = L.Bind(var)
        t = extrinsic(TypeOf, f)
        add_extrinsic(TypeOf, bind, t)
        add_extrinsic(TypeOf, var, t)
        add_extrinsic(Name, var, "lambda")
        set_orig(var, fe)
        return bind

    def PatCapture(self, pat):
        add_extrinsic(ClosedVarFunc, pat.var, env(EXFUNC))
        pat.pattern = self.mutate('pattern')
        return pat
    def PatVar(self, pat):
        add_extrinsic(ClosedVarFunc, pat.var, env(EXFUNC))
        return pat

    def Bind(self, bind):
        mv = Bindable.asLocalVar(bind.target)
        if isJust(mv):
            v = fromJust(mv)
            wasClosed = False
            m = match(env(EXFUNC))
            if m('f==ExInnerFunc(closedVars)'):
                f, closedVars = m.args
                if has_extrinsic(ClosedVarFunc, v):
                    if extrinsic(ClosedVarFunc, v) is not f:
                        closedVars.add(v)
                        wasClosed = True

            if has_extrinsic(VarGlobalReplacement, v):
                assert not wasClosed, "TODO closed-over lambda?"
                bind.target = extrinsic(VarGlobalReplacement, v)

        return bind

class FuncValGenerator(vat.Mutator):
    def Call(self, e):
        if is_indirect_func(e.func):
            e.func = self.mutate('func')
            e.args = self.mutate('args')
            ft = extrinsic(TypeOf, e.func)
            indcall = CallIndirect(e.func, e.args, ft.meta.takesEnv)
            add_extrinsic(TypeOf, indcall, extrinsic(TypeOf, e))
            return indcall
        else:
            # skip e.func since no func val needs to be generated
            e.args = self.mutate('args')
            return e

    def VoidCall(self, c):
        if is_indirect_func(c.func):
            return self.mutate()
            """
            ft = extrinsic(TypeOf, c.func)
            #indcall = VoidCallIndirect(c.func, c.args, ft.meta.takesEnv)
            add_extrinsic(TypeOf, indcall, extrinsic(TypeOf, e))
            return indcall
            """
        else:
            # skip c.func since no func val needs to be generated
            c.args = self.mutate('args')
            return c

    def Bind(self, e):
        if not Bindable.isLocalVar(e.target):
            t = extrinsic(TypeOf, e)
            if matches(t, "TFunc(_, _, _)"):
                assert isinstance(e.target, GlobalVar)
                val = FuncVal(e.target, Nothing())
                add_extrinsic(TypeOf, val, extrinsic(TypeOf, e))
                return val
        return self.mutate()

def expand_closures(unit):
    scope_extrinsic(ClosedVarFunc, lambda:
            scope_extrinsic(VarGlobalReplacement, lambda:
            vat.mutate(ClosureExpander, unit, t_DT(ExpandedUnit))))

def is_indirect_func(e):
    if not matches(e, "Bind(_)"):
        return True
    return Bindable.isLocalVar(e.target)

class LitExpander(vat.Mutator):
    def Lit(self, lit):
        m = match(lit.literal)
        if m('StrLit(_)'):
            v = GlobalVar()
            add_extrinsic(Name, v, '.LC%d' % (vat.orig_loc(lit).index,))
            vat.set_orig(v, lit)
            env(EXGLOBAL).newDecls.lits.append(LitDecl(v, lit.literal))
            expr = L.Bind(v)
            add_extrinsic(TypeOf, expr, TStr())
            add_extrinsic(TypeOf, v, TStr())
            return expr
        else:
            return lit

def builtin_call(name, args):
    return L.Call(L.Bind(BUILTINS[name]), args)

class AssertionExpander(vat.Mutator):
    def Assert(self, a):
        check = builtin_call('not', [self.mutate('test')])
        add_extrinsic(TypeOf, check.func, extrinsic(TypeOf, check.func.target))
        add_extrinsic(TypeOf, check, TBool())

        # temp
        fail = RUNTIME['fail']
        bfail = L.Bind(fail)
        add_extrinsic(TypeOf, bfail, extrinsic(TypeOf, fail))

        message = self.mutate('message')
        call = S.VoidStmt(VoidCall(bfail, [message]))
        return S.Cond([CondCase(check, Body([call]))])

def convert_decl_types(decls):
    map_(iconvert_func, decls.cdecls)

    for dt in decls.dts:
        for ctor in dt.ctors:
            fts = []
            for field in ctor.fields:
                ft = convert_type(field.type)
                fts.append(ft)
                add_extrinsic(LLVMTypeOf, field, ft)
            ctort = IFunc(fts, IPtr(IData(dt)), IFuncMeta(False))
            add_extrinsic(LLVMTypeOf, ctor, ctort)

    for env in decls.envs:
        add_extrinsic(LLVMTypeOf, env, convert_type(env.type))
    for lit in decls.lits:
        iconvert(lit.var)
    map_(iconvert_func, decls.funcDecls)

THREADENV = new_env('THREADENV', 'Maybe(Var)')
InEnvCtxVar = new_extrinsic('InEnvCtxVar', Var)

class TypeConverter(vat.Mutator):
    def Call(self, e):
        # Direct calls need to convert to direct func types
        if matches(e.func, "Bind(_)"):
            iconvert_func(e.func)
            e.args = self.mutate('args')
        else:
            e = self.mutate()
        iconvert(e)
        return convert_expr_casts(e)

    def CallVoid(self, c):
        if matches(c.func, "Bind(_)"):
            iconvert_func(c.func)
            c.args = self.mutate('args')
        else:
            c = self.mutate()
        iconvert(c)
        return c

    def t_LExpr(self, e):
        e = self.mutate()
        iconvert(e)
        return convert_expr_casts(e)

    def t_Pat(self, p):
        p = self.mutate()
        iconvert(p)

        if not original_has(TypeCast, p):
            return p
        src, dest = original(TypeCast, p)
        add_extrinsic(LLVMPatCast, p, (convert_type(src), convert_type(dest)))
        return p

    def Var(self, v):
        iconvert(v)
        return v

def convert_expr_casts(e):
    if not original_has(TypeCast, e):
        return e
    src, dest = original(TypeCast, e)
    isrc = convert_type(src)
    idest = convert_type(dest)
    if itypes_equal(isrc, idest):
        assert types_punned(src, dest), \
                "Pointless non-pun cast %s -> %s" % (src, dest)
        return e
    return cast(isrc, idest, e)

class MaybeConverter(vat.Mutator):
    def Call(self, call):
        if matches(call.func, 'Bind(_)'):
            if Nullable.isMaybe(call.func.target):
                args = call.args
                if len(args) == 1:
                    arg = self.mutate('args', 0)
                    t = i_ADT(Maybe)
                    # Arg was probably cast to void* (for the just field)
                    # cast it to Maybe, as the Just() is now omitted
                    arg = cast_from_voidptr(arg, t)
                    update_extrinsic(LLVMTypeOf, arg, t)
                    return arg
                else:
                    assert len(args) == 0
                    null = NullPtr()
                    copy_type(null, call)
                    return null
        return self.mutate()

def add_call_ctx(func, args):
    if extrinsic(TypeOf, func).meta.takesEnv:
        m = match(env(THREADENV))
        if m('Just(ctx)'):
            ctx = m.arg
            bind = L.Bind(ctx)
            copy_type(bind, ctx)
            m.ret(bind)
        else:
            null = NullPtr()
            add_extrinsic(LLVMTypeOf, null, IVoidPtr())
            m.ret(null)
        args.append(m.result())

def expand_inenv(e, returnsValue, exprMutator):
    # Defer to the llvm pass until we have expression flattening
    e.init = cast_to_voidptr(e.init, extrinsic(LLVMTypeOf, e.init))
    m = match(env(THREADENV))
    if m('Just(ctx)'):
        ctx = m.arg
        add_extrinsic(InEnvCtxVar, e, ctx)
        e.expr = exprMutator()
        return e
    else:
        # Don't have a ctx var yet, need to introduce one
        ctx = new_ctx_var()
        add_extrinsic(InEnvCtxVar, e, ctx)
        e.expr = in_env(THREADENV, Just(ctx), exprMutator)
        if returnsValue:
            w = WithVar(ctx, e)
            copy_type(w, e)
        else:
            w = VoidWithVar(ctx, e)
        return w

class EnvExtrConverter(vat.Mutator):
    def Func(self, f):
        f.params = self.mutate('params')

        threadedVar = Nothing()
        if extrinsic(TypeOf, f).meta.takesEnv:
            # Add context parameter
            var = new_ctx_var()
            threadedVar = Just(var)
            f.params.append(var)

        f.body = in_env(THREADENV, threadedVar, lambda: self.mutate('body'))
        iconvert_func(f)
        return f

    def Call(self, e):

        # TEMP
        if matches(e.func, "Bind(key('_make_ctx'))"):
            environ = bind_env(e.args.pop(0).expr.env)
            null = NullPtr()
            add_extrinsic(LLVMTypeOf, null, IVoidPtr())
            arg = self.mutate('args')[0]
            call = runtime_call('_pushenv', [environ, null, arg])
            return call

        e.func = self.mutate('func')
        e.args = self.mutate('args')
        add_call_ctx(e.func, e.args)
        return e

    def IndirectCall(self, e):
        e.func = self.mutate('func')
        e.args = self.mutate('args')
        add_call_ctx(e.func, e.args)
        return e

    def VoidCall(self, c):
        c.func = self.mutate('func')
        c.args = self.mutate('args')
        add_call_ctx(c.func, c.args)
        return c

    def FuncVal(self, e):
        assert isNothing(e.ctx)
        e.ctx = env(THREADENV)
        return e

    def GetEnv(self, e):
        call = runtime_call('_getenv', [bind_env(e.env), bind_env_ctx()])
        return cast_from_voidptr(call, extrinsic(LLVMTypeOf, e))

    def HaveEnv(self, e):
        return runtime_call('_haveenv', [bind_env(e.env), bind_env_ctx()])

    def InEnv(self, e):
        e.init = self.mutate('init')
        return expand_inenv(e, True, lambda: self.mutate('expr'))

    def VoidInEnv(self, e):
        e.init = self.mutate('init')
        return expand_inenv(e, False, lambda: self.mutate('expr'))

    def GetExtrinsic(self, e):
        extr = bind_extrinsic(e.extrinsic)
        node = self.mutate('node')
        node = cast_to_voidptr(node, extrinsic(LLVMTypeOf, node))
        call = runtime_call('_getextrinsic', [extr, node])
        return cast_from_voidptr(call, extrinsic(LLVMTypeOf, e))

    def HasExtrinsic(self, e):
        extr = bind_extrinsic(e.extrinsic)
        node = self.mutate('node')
        node = cast_to_voidptr(node, extrinsic(LLVMTypeOf, node))
        return runtime_call('_hasextrinsic', [extr, node])

    def ScopeExtrinsic(self, e):
        return self.mutate('expr') # TEMP

    def WriteExtrinsic(self, s):
        f = '_addextrinsic' if s.isNew else '_updateextrinsic'
        extr = bind_extrinsic(s.extrinsic)
        node = self.mutate('node')
        val = self.mutate('val')
        node = cast_to_voidptr(node, extrinsic(LLVMTypeOf, node))
        val = cast_to_voidptr(val, extrinsic(LLVMTypeOf, val))
        return runtime_void_call(f, [extr, node, val])

def new_ctx_var():
    var = Var()
    add_extrinsic(Name, var, 'ctx')
    add_extrinsic(LLVMTypeOf, var, IVoidPtr())
    return var

def bind_env(e):
    bind = L.Bind(e)
    add_extrinsic(LLVMTypeOf, bind, IVoidPtr())
    return bind

def bind_env_ctx():
    bind = L.Bind(fromJust(env(THREADENV)))
    add_extrinsic(LLVMTypeOf, bind, IVoidPtr())
    return bind

def bind_extrinsic(extr):
    bind = L.Bind(extr)
    add_extrinsic(LLVMTypeOf, bind, IVoidPtr())
    return bind

class ImportMarker(vat.Visitor):
    def Bind(self, bind):
        tar = bind.target
        if Bindable.isLocalVar(tar):
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

FieldSymbol = new_extrinsic('FieldSymbol', str)

LocalSymbol = new_extrinsic('LocalSymbol', str)
EXLOCALS = new_env('EXLOCALS', {str: int})

def unique_global(v, isFunc):
    symbol = extrinsic(Name, v)
    add_extrinsic(GlobalSymbol, v, GlobalInfo(symbol, isFunc))

def unique_local(v):
    name = extrinsic(Name, v)
    lcls = env(EXLOCALS)
    index = lcls.get(name, 0) + 1
    lcls[name] = index
    assert '.' not in name
    if index > 1:
        name = '%s.no%d' % (name, index)
    add_extrinsic(LocalSymbol, v, name)

class LocalVarUniquer(vat.Visitor):
    def Func(self, func):
        in_env(EXLOCALS, {}, lambda: self.visit())

    def Var(self, var):
        unique_local(var)

def unique_decls(decls):
    for v in decls.cdecls:
        unique_global(v, True)
        add_extrinsic(CFunction, v, True)

    for dt in decls.dts:
        unique_global(dt, True)
        for ctor in dt.ctors:
            unique_global(ctor, True)
            for field in ctor.fields:
                add_extrinsic(FieldSymbol, field, extrinsic(Name, field))

    for env in decls.envs:
        unique_global(env, False)
    for extr in decls.extrinsics:
        unique_global(extr, False)

    for var in decls.funcDecls:
        unique_global(var, True)
    for lit in decls.lits:
        unique_global(lit.var, False)

# GLUE

def _prepare_decls(decls):
    convert_decl_types(decls)

def _finish_decls(decls):
    map_(dt_layout, decls.dts)
    unique_decls(decls)

def expand_decls(decls):
    _prepare_decls(decls)
    _finish_decls(decls)

def expand_unit(unit):
    t = t_DT(ExpandedUnit)
    expand_closures(unit)
    vat.mutate(FuncValGenerator, unit, t)
    vat.mutate(LitExpander, unit, t)
    vat.mutate(AssertionExpander, unit, t)

    # Prepend generated TopFuncs now
    unit.funcs = env(EXGLOBAL).newDefns + unit.funcs

    _prepare_decls(env(EXGLOBAL).newDecls)

    vat.mutate(TypeConverter, unit, t)
    vat.mutate(MaybeConverter, unit, t)
    vat.mutate(EnvExtrConverter, unit, t)

    _finish_decls(env(EXGLOBAL).newDecls)

    vat.visit(ImportMarker, unit, t)
    vat.visit(LocalVarUniquer, unit, t)

def in_intramodule_env(func):
    captures = {}
    extrs = [Closure, LLVMPatCast,
            vat.Original, LocalSymbol,
            InEnvCtxVar]

    # XXX workaround for insufficiently staged compilation
    defs = "malloc,match_fail,_pushenv,_popenv".split(',')
    default_binds = set(RUNTIME[d] for d in defs)

    return in_env(IMPORTBINDS, default_binds,
            lambda: capture_scoped(extrs, captures, func))

def in_intermodule_env(func):
    captures = {}
    extrs = [LLVMTypeOf, DataLayout, CtorIndex, FieldIndex,
            GlobalSymbol, CFunction, FieldSymbol]
    return capture_scoped(extrs, captures, func)

def expand_module(decl_mod, defn_mod):
    expand_decls(decl_mod.root)
    new_decls = blank_module_decls()

    # Clone defns as mutable defns-using-LExprs
    def transmute():
        mapping = {
            t_DT(CompilationUnit): t_DT(ExpandedUnit),
            t_ADT(Expr): t_ADT(LExpr),
        }
        extrs = [Name, TypeOf]
        unit = vat.transmute(defn_mod.root, mapping, extrs)
        vat.rewrite(unit)
        return unit
    new_unit = vat.in_vat(transmute)

    # Mutate clones
    in_env(EXGLOBAL, ExGlobal(new_decls, [], [decl_mod, defn_mod]),
        lambda: expand_unit(new_unit))

    return (new_decls, new_unit)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
