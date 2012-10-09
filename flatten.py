from base import *
from atom import *
from quilt import *
import vat

FLAT = new_env('FLAT', Body)

def push_stmt(s):
    env(FLAT).stmts.append(s)

class Flattener(vat.Mutator):
    def Body(self, body):
        new_body = Body([])
        _ = in_env(FLAT, new_body, lambda: self.mutate('stmts'))
        return new_body

    def t_Stmt(self, stmt):
        stmt = self.mutate()
        push_stmt(stmt)
        return stmt

    def And(self, e):
        bools = []

        left = self.mutate('left')
        tmp = Var()
        bools.append(tmp)
        pat = PatVar(tmp)
        bools.append(pat)
        push_stmt(S.Defn(pat, left))

        thenBlock = Body([])
        right = in_env(FLAT, thenBlock, lambda: self.mutate('right'))
        thenBlock.stmts.append(S.Assign(LhsVar(tmp), right))

        bindTmp = L.Bind(tmp)
        bools.append(bindTmp)
        then = CondCase(bindTmp, thenBlock)
        push_stmt(S.Cond([then]))

        output = L.Bind(tmp)
        bools.append(output)
        for b in bools:
            add_extrinsic(TypeOf, b, TBool())
        return output

    def Or(self, e):
        bools = []

        left = self.mutate('left')
        tmp = Var()
        bools.append(tmp)
        pat = PatVar(tmp)
        bools.append(pat)
        push_stmt(S.Defn(pat, left))

        thenBlock = Body([])
        right = in_env(FLAT, thenBlock, lambda: self.mutate('right'))
        thenBlock.stmts.append(S.Assign(LhsVar(tmp), right))

        bindTmp = L.Bind(tmp)
        bools.append(bindTmp)
        then = CondCase(builtin_call('not', [bindTmp]), thenBlock)
        push_stmt(S.Cond([then]))

        output = L.Bind(tmp)
        bools.append(output)
        for b in bools:
            add_extrinsic(TypeOf, b, TBool())
        return output

def builtin_call(name, args):
    f = BUILTINS[name]
    ft = extrinsic(TypeOf, f)
    bind = L.Bind(f)
    add_extrinsic(TypeOf, bind, ft)
    call = L.Call(bind, args)
    add_extrinsic(TypeOf, call, ft.result.type)
    return call

def flatten_unit(unit):
    vat.mutate(Flattener, unit, t_DT(ExpandedUnit))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
