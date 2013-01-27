#!/usr/bin/env python2
from base import *
from atom import *
from quilt import *
import drum
import flatten
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

# DEFNS

ClosureInfo = DT('ClosureInfo', ('func', Func), ('isClosure', bool))
Closure = new_extrinsic('Closure', ClosureInfo)

ClosedVarFunc = new_extrinsic('ClosedVar', '*ExFunc')
VarGlobalReplacement = new_extrinsic('VarGlobalReplacement', '*GlobalVar')

def iconvert(a):
    add_extrinsic(LLVMTypeOf, a, convert_type(extrinsic(TypeOf, a)))

def iconvert_func_var(a):
    add_extrinsic(LLVMTypeOf, a, convert_func_type(extrinsic(TypeOf, a)))

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
                add_extrinsic(VarGlobalReplacement, m.var, m.globalVar)
                update_extrinsic(Name, m.globalVar, extrinsic(Name, m.var))
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
        t = extrinsic(TypeOf, fe)
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
                if has_extrinsic(ClosedVarFunc, v):
                    if extrinsic(ClosedVarFunc, v) is not m.f:
                        m.closedVars.add(v)
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
            indcall = CallIndirect(e.func, e.args, ft.meta.envParam)
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
            #indcall = VoidCallIndirect(c.func, c.args, ft.meta.envParam)
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

        message = self.mutate('message')
        fail = flatten.runtime_void_call('fail', [message])
        case = CondCase(check, Body([fail]))
        set_orig(case, a)
        cond = S.Cond([case])
        set_orig(cond, a)
        return cond

def convert_decl_types(decls):
    map_(iconvert_func_var, decls.cdecls)

    for dt in decls.dts:
        if extrinsic(Name, dt) == 'Maybe':
            continue # XXX maybe codegen
        for ctor in dt.ctors:
            fts = []
            for field in ctor.fields:
                ft = convert_type(field.type)
                fts.append(IParam(ft, is_strong_ptr(ft)))
                add_extrinsic(LLVMTypeOf, field, ft)
            ctort = IFunc(fts, IPtr(IData(dt)), IFuncMeta(False))
            add_extrinsic(LLVMTypeOf, ctor, ctort)

    for env in decls.envs:
        add_extrinsic(LLVMTypeOf, env, convert_type(env.type))
    for lit in decls.lits:
        iconvert(lit.var)
    map_(iconvert_func_var, decls.funcDecls)

ThreadedEnvVar = DT('ThreadedEnvVar', ('var', 'Maybe(Var)'), ('depth', int))
THREADENV = new_env('THREADENV', ThreadedEnvVar)

class TypeConverter(vat.Mutator):
    def Call(self, e):
        # Direct calls need to convert to direct func types
        if matches(e.func, "Bind(_)"):
            iconvert_func_var(e.func)
            e.args = self.mutate('args')
        else:
            e = self.mutate()
        iconvert(e)
        return convert_expr_casts(e)

    def CallVoid(self, c):
        if matches(c.func, "Bind(_)"):
            iconvert_func_var(c.func)
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

        if not has_extrinsic(TypeCast, p):
            return p
        src, dest = extrinsic(TypeCast, p)
        add_extrinsic(LLVMPatCast, p, (convert_type(src), convert_type(dest)))
        return p

    def Var(self, v):
        iconvert(v)
        return v

def convert_expr_casts(e):
    if not has_extrinsic(TypeCast, e):
        return e
    src, dest = extrinsic(TypeCast, e)
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
                    # cast it to Maybe, as the Just() is now omitted
                    argT = extrinsic(LLVMTypeOf, arg)
                    arg = cast(argT, i_ADT(Maybe), arg)
                    return arg
                else:
                    assert len(args) == 0
                    null = NullPtr()
                    copy_type(null, call)
                    return null
        return self.mutate()

def add_call_ctx(func, args):
    if extrinsic(TypeOf, func).meta.envParam:
        m = match(env(THREADENV).var)
        if m('Just(ctx)'):
            bind = L.Bind(m.ctx)
            copy_type(bind, m.ctx)
            m.ret(bind)
        else:
            null = NullPtr()
            add_extrinsic(LLVMTypeOf, null, IVoidPtr())
            m.ret(null)
        args.append(m.result())

class EnvExtrConverter(vat.Mutator):
    def BlockFunc(self, func):
        threadedVar = Nothing()
        origDepth = 0
        ft = extrinsic(TypeOf, func.var)
        if ft.meta.envParam:
            # Add context parameter
            var = new_ctx_var()
            threadedVar = Just(var)
            origDepth = 1
            func.params.append(LVar(var))

        info = ThreadedEnvVar(threadedVar, origDepth)
        _ = in_env(THREADENV, info, lambda: self.mutate('blocks'))
        assert info.depth == origDepth, "Unbalanced env push/pops"
        return func

    def FuncExpr(self, fe):
        assert False

    def PushEnv(self, stmt):
        bindEnv = L.Bind(stmt.env)
        add_extrinsic(LLVMTypeOf, bindEnv, IVoidPtr())

        init = self.mutate('init')
        init = cast_to_voidptr(init, extrinsic(LLVMTypeOf, init))
        threaded = env(THREADENV)
        threaded.depth += 1

        m = match(threaded.var)
        if m('Just(ctxVar)'):
            # Update the old ctx value with the pushed ctx
            bindCtx = L.Bind(m.ctxVar)
            add_extrinsic(LLVMTypeOf, bindCtx, IVoidPtr())
            call = runtime_call('_pushenv', [bindEnv, bindCtx, init])
            lhs = LhsVar(m.ctxVar)
            add_extrinsic(LLVMTypeOf, lhs, IVoidPtr())
            return S.Assign(lhs, call)
        else:
            # Don't have a ctx var yet, need to introduce one
            null = NullPtr()
            add_extrinsic(LLVMTypeOf, null, IVoidPtr())
            call = runtime_call('_pushenv', [bindEnv, null, init])
            ctx = new_ctx_var()
            threaded.var = Just(ctx)
            pat = PatVar(ctx)
            add_extrinsic(LLVMTypeOf, pat, IVoidPtr())
            return S.Defn(pat, call)

    def PopEnv(self, stmt):
        bindEnv = L.Bind(stmt.env)
        add_extrinsic(LLVMTypeOf, bindEnv, IVoidPtr())

        threaded = env(THREADENV)
        assert threaded.depth > 0, "Env underflow"
        threaded.depth -= 1

        ctxVar = fromJust(threaded.var)
        bindCtx = L.Bind(ctxVar)
        add_extrinsic(LLVMTypeOf, bindCtx, IVoidPtr())
        call = runtime_call('_popenv', [bindEnv, bindCtx])
        if threaded.depth > 0:
            lhs = LhsVar(ctxVar)
            add_extrinsic(LLVMTypeOf, lhs, IVoidPtr())
            return S.Assign(lhs, call)
        else:
            # clean up this context
            threaded.var = Nothing()
            # TODO: check the return value here against null
            # (ugh, need to insert block... couldn't this be done earlier?)
            # just discard for now
            discard = PatWild()
            add_extrinsic(LLVMTypeOf, discard, IVoidPtr())
            return S.Defn(discard, call)

    def CreateCtx(self, e):
        environ = bind_env(e.env)
        null = NullPtr()
        add_extrinsic(LLVMTypeOf, null, IVoidPtr())
        init = self.mutate('init')
        init = cast_to_voidptr(init, extrinsic(LLVMTypeOf, init))
        call = runtime_call('_pushenv', [environ, null, init])
        return call

    def DestroyCtx(self, e):
        environ = bind_env(e.env)
        ctx = self.mutate('ctx')
        ctx = cast_to_voidptr(ctx, extrinsic(LLVMTypeOf, ctx))
        call = runtime_call('_popenv', [environ, ctx])
        return call

    def Call(self, e):
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
        e.ctx = env(THREADENV).var
        return e

    def GetEnv(self, e):
        call = runtime_call('_getenv', [bind_env(e.env), bind_env_ctx()])
        return cast_from_voidptr(call, extrinsic(LLVMTypeOf, e))

    def HaveEnv(self, e):
        return runtime_call('_haveenv', [bind_env(e.env), bind_env_ctx()])

    def InEnv(self, e):
        assert False, "Ought to be flattened"
    def VoidInEnv(self, e):
        assert False, "Ought to be flattened"

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
    bind = L.Bind(fromJust(env(THREADENV).var))
    add_extrinsic(LLVMTypeOf, bind, IVoidPtr())
    return bind

def bind_extrinsic(extr):
    bind = L.Bind(extr)
    add_extrinsic(LLVMTypeOf, bind, IVoidPtr())
    return bind

CtorReplacement = new_extrinsic('CtorReplacement', '*GlobalVar')

def generate_ctor(ctor, dt):
    ctort = IPtr(IDataCtor(ctor))
    inst = Var()
    add_extrinsic(Name, inst, 'inst')
    add_extrinsic(LLVMTypeOf, inst, ctort)

    sizeof = SizeOf(IPtr(IDataCtor(ctor)))
    add_extrinsic(LLVMTypeOf, sizeof, IInt())
    instPtr = runtime_call('gc_alloc', [sizeof])
    instPtr = cast(IVoidPtr(), IPtr(IDataCtor(ctor)), instPtr)
    pat = PatVar(inst)
    add_extrinsic(LLVMTypeOf, pat, ctort)
    instDefn = S.Defn(pat, instPtr)

    ps = []
    stmts = [instDefn]

    def assign_slot(slot, ft, val):
        instBind = L.Bind(inst)
        add_extrinsic(LLVMTypeOf, instBind, ctort)
        lhs = LhsSlot(instBind, slot)
        add_extrinsic(LLVMTypeOf, lhs, ft)
        add_extrinsic(LLVMTypeOf, val, ft)
        stmts.append(S.Assign(lhs, val))

    layout = extrinsic(DataLayout, dt)
    if layout.gcSlot >= 0:
        ctorLayout = extrinsic(CtorLayout, ctor)
        gcSpec = match(ctorLayout.formVar, ('Just(v)', L.Bind),
                                           ('Nothing()', NullPtr))
        assign_slot(layout.gcSlot, IVoidPtr(), gcSpec)

    if layout.extrSlot >= 0:
        assign_slot(layout.extrSlot, IVoidPtr(), NullPtr())

    discrim = layout.discrimSlot >= 0
    if discrim:
        index = extrinsic(CtorIndex, ctor)
        assign_slot(layout.discrimSlot, IInt(), L.Lit(IntLit(index)))

    for field in ctor.fields:
        ft = extrinsic(LLVMTypeOf, field)
        param = Register()
        add_extrinsic(Name, param, extrinsic(Name, field))
        add_extrinsic(LLVMTypeOf, param, ft)
        ps.append(LRegister(param))

        instBind = L.Bind(inst)
        add_extrinsic(LLVMTypeOf, instBind, ctort)
        lhs = LhsAttr(instBind, field)
        val = L.Bind(param)
        add_extrinsic(LLVMTypeOf, lhs, ft)
        add_extrinsic(LLVMTypeOf, val, ft)
        stmts.append(S.Assign(lhs, val))

    retVal = L.Bind(inst)
    add_extrinsic(LLVMTypeOf, retVal, ctort)
    if discrim:
        retVal = cast(IPtr(IDataCtor(ctor)), IPtr(IData(dt)), retVal)
    block = Block('.0', stmts, [], TermReturn(retVal), [])

    funcVar = GlobalVar()
    add_extrinsic(Name, funcVar, extrinsic(Name, ctor))
    add_extrinsic(LLVMTypeOf, funcVar, extrinsic(LLVMTypeOf, ctor))
    glob = env(EXGLOBAL)
    glob.newDecls.funcDecls.append(funcVar)

    add_extrinsic(CtorReplacement, ctor, funcVar)
    set_orig(funcVar, ctor)

    # don't bother recording inst as a gcroot since it could never get
    # swept anyway (currently) as gc_alloc() doesn't get called after
    # its initialization
    gcVars = []
    return BlockFunc(funcVar, gcVars, ps, [block])

class CtorReplacer(vat.Mutator):
    def Bind(self, bind):
        if has_extrinsic(CtorReplacement, bind.target):
            bind.target = extrinsic(CtorReplacement, bind.target)
        assert not matches(bind.target, "Ctor(_)"), "Ctor not gone?"
        return bind

def replace_ctors(decls, flat):
    ctor_funcs = []
    for dt in decls.dts:
        if extrinsic(Name, dt) == 'Maybe':
            continue # XXX maybe codegen
        for ctor in dt.ctors:
            ctor_funcs.append(generate_ctor(ctor, dt))
    flat.funcs = ctor_funcs + flat.funcs
    vat.mutate(CtorReplacer, flat, t_DT(BlockUnit))


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

def dt_layout(dt):
    base = 0
    info = LayoutInfo(-1, -1, -1)
    if dt.opts.garbageCollected:
        info.gcSlot = base
        base += 1
    if not dt.opts.valueType:
        info.extrSlot = base
        base += 1
    discrim = len(dt.ctors) > 1
    if discrim:
        info.discrimSlot = base
        base += 1
    add_extrinsic(DataLayout, dt, info)
    for i, ctor in enumerate(dt.ctors):
        add_extrinsic(DataLayout, ctor, info)
        if discrim:
            add_extrinsic(CtorIndex, ctor, i)
        for ix, field in enumerate(ctor.fields):
            add_extrinsic(FieldIndex, field, ix + base)

def dt_gc_layout(dt):
    layout = extrinsic(DataLayout, dt)
    if layout.gcSlot < 0:
        return

    layoutVars = env(EXGLOBAL).newDecls.grabBag

    for ctor in dt.ctors:
        gcFields = []
        for field in ctor.fields:
            if is_field_garbage_collected(field):
                gcFields.append(field)

        info = CtorInfo(Nothing(), gcFields)
        if len(gcFields) > 0:
            var = GlobalVar()
            add_extrinsic(Name, var, extrinsic(Name, ctor) + '__form')
            add_extrinsic(LLVMTypeOf, var, IVoidPtr())
            set_orig(var, ctor)
            layoutVars.append(var)
            info.formVar = Just(var)
        add_extrinsic(CtorLayout, ctor, info)

def gen_gc_layouts(decls):
    for dt in decls.dts:
        dt_gc_layout(dt)

def is_field_garbage_collected(field):
    m = match(field.type)
    if m('TData(dt, _)'):
        if extrinsic(Name, m.dt) == 'Type':
            return False # XXX
        if m.dt.opts.valueType:
            assert False, 'value type oh no'
        else:
            return True
    elif m('TPrim(_) or TWeak(_)'):
        return False
    else:
        return False # for now

CFunction = new_extrinsic('CFunction', bool)

EXLOCALS = new_env('EXLOCALS', {str: int})

def unique_global(v, isFunc):
    symbol = extrinsic(Name, v)
    add_extrinsic(GlobalSymbol, v, GlobalInfo(symbol, isFunc))

def unique_local(v):
    name = extrinsic(Name, v) if has_extrinsic(Name, v) else 'tmp'
    lcls = env(EXLOCALS)
    index = lcls.get(name, 0) + 1
    lcls[name] = index
    assert '.' not in name
    if index > 1:
        name = '%s.no%d' % (name, index)
    add_extrinsic(LocalSymbol, v, name)

class LocalVarUniquer(vat.Visitor):
    def BlockFunc(self, func):
        in_env(EXLOCALS, {}, lambda: self.visit())

    def Var(self, var):
        unique_local(var)

    def Register(self, reg):
        unique_local(reg)

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

    for var in decls.grabBag:
        unique_global(var, False)

# GLUE

def _prepare_decls(decls):
    convert_decl_types(decls)

def _finish_decls(decls):
    map_(dt_layout, decls.dts)
    unique_decls(decls)

def expand_decls(decls):
    _prepare_decls(decls)
    _finish_decls(decls)

def expand_unit(old_decl_mod, unit):
    t = t_DT(ExpandedUnit)

    expand_closures(unit)

    vat.mutate(FuncValGenerator, unit, t)
    vat.mutate(LitExpander, unit, t)
    vat.mutate(AssertionExpander, unit, t)

    gen_gc_layouts(old_decl_mod.root)

    # Prepend generated TopFuncs now
    unit.funcs = env(EXGLOBAL).newDefns + unit.funcs

    flat = flatten.flatten_unit(unit)
    t = t_DT(BlockUnit)

    drum.walk(flat)

    _prepare_decls(env(EXGLOBAL).newDecls)

    vat.mutate(TypeConverter, flat, t)
    vat.mutate(MaybeConverter, flat, t)
    vat.mutate(EnvExtrConverter, flat, t)

    replace_ctors(old_decl_mod.root, flat)

    _finish_decls(env(EXGLOBAL).newDecls)

    vat.visit(ImportMarker, flat, t)
    vat.visit(LocalVarUniquer, flat, t)
    return flat

def in_intramodule_env(func):
    captures = {}
    extrs = [Closure, LLVMPatCast,
            vat.Original, LocalSymbol,
            IRComments]

    # XXX workaround for insufficiently staged compilation
    defs = """
    malloc,free,
    gc_array,gc_array_ptr,gc_array_len,gc_array_subscript
    """.replace(' ', '').replace('\n', '').split(',')
    default_binds = set(RUNTIME[d] for d in defs)

    return in_env(IMPORTBINDS, default_binds,
            lambda: capture_scoped(extrs, captures, func))

def in_intermodule_env(func):
    captures = {}
    extrs = [LLVMTypeOf, DataLayout, CtorLayout, CtorIndex, FieldIndex,
            GlobalSymbol, CFunction, FieldSymbol, CtorReplacement]
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
        extrs = [Name, TypeOf, TypeCast, ResultOf]
        unit = vat.transmute(defn_mod.root, mapping, extrs)
        vat.rewrite(unit)
        return unit
    new_unit = vat.in_vat(transmute)

    # Mutate clones
    glob = ExGlobal(new_decls, [], [decl_mod, defn_mod])
    flat_unit = in_env(EXGLOBAL, glob, lambda: expand_unit(decl_mod, new_unit))

    return new_decls, flat_unit

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
