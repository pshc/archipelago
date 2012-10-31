from atom import *
from astconv import AstHint, AstType
import vat

Inward = DT('Inward', ('closedVars', {'*TypeVar': Type}))
INWARD = new_env('INWARD', Inward)

def set_type(e, t):
    assert isinstance(t, Type), "%s is not a type" % (t,)
    add_extrinsic(TypeOf, e, t)

# Augment AST with instantiation records

INSTSUSED = new_env('INSTSUSED', {TypeVar: Type})

def record_tvar(tv):
    insts = env(INSTSUSED)
    if tv not in insts:
        nm = extrinsic(Name, tv)
        it = env(INWARD).closedVars.get(nm)
        if it is not None:
            assert isinstance(it, TypeVar)
            insts[tv] = TVar(it)

def scan_inst_data(tvs, apps):
    map_(record_tvar, tvs)
    map_(scan_inst, apps)

def scan_inst_func(ps, r):
    map_(scan_inst, ps)
    if matches(r, ('Ret(_)')):
        scan_inst(r.type)

def scan_inst(s):
    match(s,
        ('TVar(tv)', record_tvar),
        ('TPrim(_)', nop),
        ('TTuple(ts)', lambda ts: map_(scan_inst, ts)),
        ('TFunc(ps, r, _)', scan_inst_func),
        ('TData(DataType(_, tvs, _), apps)', scan_inst_data),
        ('TArray(t)', scan_inst),
        ('TWeak(t)', scan_inst))

def instantiate_type(site, t):
    insts = {}
    in_env(INSTSUSED, insts, lambda: scan_inst(t))
    for k in insts.keys():
        if insts[k] is None:
            del insts[k]
    #if insts:
    #    add_extrinsic(InstMap, site, insts)

def instantiate(site, v):
    if has_extrinsic(TypeOf, v):
        instantiate_type(site, extrinsic(TypeOf, v))

class Scanner(vat.Visitor):
    def t_Expr(self, e):
        with_hint_maybe(e, lambda: self.visit())

    def Bind(self, bind):
        instantiate(bind, bind.target)
        with_hint_maybe(bind, lambda: self.visit())

    def LhsVar(self, lhs):
        instantiate(lhs, lhs.var)

    # Ideally with type info here we would fix fields. Deferred to prop.
    def LhsAttr(self, lhs):
        self.visit()
    def Attr(self, e):
        self.visit()

    def Func(self, f):
        scan_func(f)

def scan_func(f):
    if not has_extrinsic(AstType, f):
        vat.visit(Scanner, f.body, "Body(Expr)")
        return

    tvars = {}
    ftstr = extrinsic(AstType, f)
    ft = parse_new_type(ftstr, tvars)
    tps = ft.paramTypes
    ps = f.params
    assert len(tps) == len(ps), "Mismatched param count: %s\n%s" % (tps,ps)
    set_type(f, ft)

    closed = env(INWARD).closedVars
    closed.update(tvars)
    in_env(INWARD, Inward(closed),
            lambda: vat.visit(Scanner, f.body, "Body(Expr)"))

def with_hint_maybe(e, func):
   if has_extrinsic(AstHint, e):
        old = env(INWARD).closedVars
        new = extrinsic(AstHint, e)
        for k, v in new.iteritems():
            if k not in old or old[k] != v:
                up = old.copy()
                up.update(new)
                in_env(INWARD, Inward(up), func)
                return
   func()

def scan_unit(unit):
    def go():
        for top in unit.funcs:
            in_env(STMTCTXT, top, lambda: scan_func(top.func))
    in_env(INWARD, Inward({}), go)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
