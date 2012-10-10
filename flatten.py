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
        left = self.mutate('left')
        tmp = define_temp_var(left)
        thenBlock = store_scope_result(tmp, lambda: self.mutate('right'))
        bindTmp = L.Bind(tmp)
        add_extrinsic(TypeOf, bindTmp, TBool())
        then = CondCase(bindTmp, thenBlock)
        push_stmt(S.Cond([then]))

        output = L.Bind(tmp)
        add_extrinsic(TypeOf, output, TBool())
        return output

    def Or(self, e):
        left = self.mutate('left')
        tmp = define_temp_var(left)
        thenBlock = store_scope_result(tmp, lambda: self.mutate('right'))
        bindTmp = L.Bind(tmp)
        add_extrinsic(TypeOf, bindTmp, TBool())
        then = CondCase(builtin_call('not', [bindTmp]), thenBlock)
        push_stmt(S.Cond([then]))

        output = L.Bind(tmp)
        add_extrinsic(TypeOf, output, TBool())
        return output

    def Ternary(self, e):
        retType = extrinsic(TypeOf, e)
        undef = Undefined()
        add_extrinsic(TypeOf, undef, retType)
        result = define_temp_var(undef)
        test = self.mutate('test')
        trueBlock = store_scope_result(result, lambda: self.mutate('then'))
        falseBlock = store_scope_result(result, lambda: self.mutate('else_'))
        push_stmt(S.Cond([CondCase(test, trueBlock),
                          CondCase(true(), falseBlock)]))
        output = L.Bind(result)
        add_extrinsic(TypeOf, output, retType)
        return output

def define_temp_var(init):
    t = extrinsic(TypeOf, init)
    var = Var()
    add_extrinsic(TypeOf, var, t)
    pat = PatVar(var)
    add_extrinsic(TypeOf, pat, t)
    push_stmt(S.Defn(pat, init))
    return var

def store_scope_result(var, func):
    body = Body([])
    result = in_env(FLAT, body, func)
    body.stmts.append(S.Assign(LhsVar(var), result))
    return body

def builtin_call(name, args):
    f = BUILTINS[name]
    ft = extrinsic(TypeOf, f)
    bind = L.Bind(f)
    add_extrinsic(TypeOf, bind, ft)
    call = L.Call(bind, args)
    add_extrinsic(TypeOf, call, ft.result.type)
    return call

def true():
    bind = L.Bind(BUILTINS['True'])
    add_extrinsic(TypeOf, bind, TBool())
    return bind

def flatten_unit(unit):
    vat.mutate(Flattener, unit, t_DT(ExpandedUnit))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
