#!/usr/bin/env python
from base import *
from atom import *
from builtins import *

CScope = DT('CScope', ('csStmts', [Atom]),
                      ('csFunc', str),
                      ('csOuterScope', 'CScope'))
CSCOPE = None

def csym(name, subs):
    """
    This is what it should look like:

    global CSYMS, CMOD
    return Ref(CSYMS[name], CMOD, subs)
    """
    if name not in boot_sym_names:
        add_sym(name)
    return symref(name, subs)

def csym_(name):
    return csym(name, [])

def cptr(t):
    return csym('ptr', [t])

def cname(nm):
    return csym('name', [Str(nm, [])])

def _c_type(t):
    return match(t,
        ("TInt()", lambda: csym_('int')),
        ("TStr()", lambda: cptr(csym_('char'))),
        ("TTuple(_)", lambda: csym_('tuple')),
        ("TNullable(v)", _c_type),
        ("TVar(_)", lambda: cptr(csym_('void'))),
        ("TVoid()", lambda: csym_('void')),
        ("TData(named(nm))", lambda nm: cptr(csym('structref', [str_(nm)]))))

def c_type(t, tvars):
    return _c_type(atoms_to_type(t, dict((v, TVar(0)) for v in tvars)))

def c_scheme(ta):
    t = atoms_to_scheme(ta)
    return _c_type(t.schemeType)

def as_c_op(a):
    return match(a, ("Ref(named(nm, contains(key('unaryop' or 'binaryop'))), "
                     "_, _)", identity),
                    ("_", lambda: None))

def c_defref(r, nm):
    # TODO
    assert as_c_op(r) is None, "Can't pass around built-in C op %s" % (nm,)
    return str_(nm)

def callnamed(nm, args):
    return csym('call', [str_(nm), int_len(args)] + args)

def c_call(f, args):
    op = as_c_op(f)
    if op is not None:
        return csym(op, map(c_expr, args))
    else:
        return csym('call', [c_expr(f), int_len(args)] + map(c_expr, args))

def c_tuple(ts):
    f = 'tuple%d' % (len(ts),) # TODO
    return callnamed(f, map(c_expr, ts))

def c_expr(e):
    return match(e,
        ("Int(i, _)", lambda i: Int(i, [])),
        ("Str(s, _)", lambda s: csym('strlit', [str_(s)])),
        ("r==Ref(named(nm, contains(key('type'))), _, _)", c_defref),
        ("r==Ref(named(nm) and key('ctor'), _, _)", c_defref),
        ("key('call', cons(f, sized(args)))", c_call),
        ("key('tuplelit', sized(ts))", c_tuple))

def is_func_scope(scope):
    return scope.csFunc is not None

def c_assign(a, e):
    ce = c_expr(e)
    nm, needs_decl = match(a,
        ("key('var') and named(nm)", lambda nm: (nm, True)),
        ("Ref(named(nm, contains(key('type'))), _, _)",
            lambda nm: (nm, False)))
    if needs_decl:
        ct = match(a, ("key('var', contains(t==key('type')))", c_scheme))
        global CSCOPE
        func = CSCOPE
        definition = lambda: stmt(csym('vardefn', [str_(nm), ct, ce]))
        is_decl_or_defn = lambda s: match(s,
                ("key('vardecl' or 'vardefn')", lambda: True),
                ("_", lambda: False))
        # Check to see if we can set this right where we declare it
        if is_func_scope(func):
            can_assign_now = True
            if all(map(is_decl_or_defn, func.csStmts)):
                definition()
                return
        # Otherwise find a suitable place to declare this variable
        while not is_func_scope(func):
            if func.csOuterScope is None: # global?
                definition()
                return
            func = func.csOuterScope
        i = 0
        while i < len(func.csStmts) and is_decl_or_defn(func.csStmts[i]):
            i += 1
        func.csStmts.insert(i, csym('vardecl', [str_(nm), ct]))
    stmt(csym('=', [str_(nm), ce]))

def c_cond(subs, cs):
    cases = []
    for (t, b) in cs:
        ct = c_expr(t)
        cb = c_body(b, None)
        list_append(cases, csym('case', [ct, int_len(cb)] + cb))
    else_ = match(subs, ("contains(key('else', sized(body)))", identity),
                        ("_", lambda: None))
    if else_ is not None:
        cb = c_body(else_, None)
        list_append(cases, csym('else', [int_len(cb)] + cb))
    stmt(csym('if', cases))

def c_while(t, body):
    # OH GOD SIDE EFFECTS?
    ct = c_expr(t)
    cb = c_body(body, None)
    stmt(csym('while', [ct, int_len(cb)] + cb))

def c_assert(t, m):
    stmt(csym('exprstmt', [callnamed('assert', [c_expr(t), c_expr(m)])]))

def c_DT(cs, vs, nm):
    discrim = len(cs) > 1
    ctors = []
    structs = []
    # Convert ctors to structs
    for c in cs:
        cnm, fs = match(c, ("named(nm, all(fs, f==key('field')))", tuple2))
        fields = [match(f, ("named(nm, contains(key('type', cons(t, _))))",
                            lambda fnm, t: (c_type(t, vs), fnm))) for f in fs]
        cfields = [csym('field', [t, str_(fnm)]) for (t, fnm) in fields]
        if discrim:
            list_append(structs, csym('field', [csym('struct', cfields),
                                                str_(cnm)]))
        else:
            stmt(csym('decl', [csym('struct', [symname(cnm)] + cfields)]))
        ctors.append((cnm, fields))
    enumsym = lambda cnm: str_('%s%s' % (nm, cnm))
    if discrim:
        # Generate our extra struct-around-union-around-ctors
        enum = csym('enum', [csym('implicitconst', [enumsym(getname(c))])
                             for c in cs])
        union = csym('union', structs)
        stmt(csym('decl', [csym('struct', [symname(nm),
                csym('field', [enum, str_('ix')]),
                csym('field', [union, str_('s')])])]))
    # Ctor functions
    retT = lambda: csym('structref', [str_(nm)])
    for (cnm, fields) in ctors:
        var = lambda: str_(cnm.lower())
        args = [csym('arg', [t, str_(anm)]) for (t, anm) in fields]
        setup = [csym('vardefn', [var(), cptr(retT()),
                callnamed('malloc', [csym('sizeof', [retT()])])])]
        if discrim:
            list_append(setup, csym('=', [csym('->', [var(), str_('ix')]),
                                          enumsym(cnm)]))
        # Set all the fields from ctor args
        for (ct, fnm) in fields:
            field = lambda: str_(fnm)
            if discrim:
                s = csym('=', [csym('.', [csym('.', [csym('->',
                    [var(), str_('s')]), str_(cnm)]), field()]), field()])
            else:
                s = csym('=', [csym('->', [var(), field()]), field()])
            list_append(setup, s)
        list_append(setup, csym('return', [var()]))
        stmt(csym('func', [cptr(retT()), str_(cnm),
                csym('args', [int_len(args)] + args),
                csym('body', [int_len(setup)] + setup)]))

def c_args(args):
    return [match(a, ("named(nm, contains(t==key('type')))",
                      lambda nm, t: csym('arg', [c_scheme(t), str_(nm)])))
            for a in args]

def c_func(t, args, body, nm):
    # Wow this is bad
    t_ = atoms_to_scheme(t).schemeType
    retT = c_scheme(scheme_to_atoms(Scheme([], t_.funcRet)))

    cb = c_body(body, nm)
    stmt(csym('func', [retT, str_(nm),
            csym('args', [int_len(args)] + c_args(args)),
            csym('body', [int_len(cb)] + cb)]))

def c_stmt(s):
    match(s,
        ("key('exprstmt', cons(e, _))",
            lambda e: stmt(csym('exprstmt', [c_expr(e)]))),
        ("key('=', cons(a, cons(e, _)))", c_assign),
        ("key('cond', ss and all(cs, key('case', cons(t, sized(b)))))",c_cond),
        ("key('while', cons(t, contains(key('body', sized(b)))))", c_while),
        ("key('assert', cons(t, cons(m, _)))", c_assert),
        ("key('DT', all(cs, c==key('ctor'))\
                and all(vs, v==key('typevar'))) and named(nm)", c_DT),
        ("key('func', contains(t==key('type')) "
                 "and contains(key('args', sized(a))) "
                 "and contains(key('body', sized(b)))) and named(nm)", c_func),
        ("key('return', cons(e, _))",
            lambda e: stmt(csym("return", [c_expr(e)]))),
        ("key('returnnothing')", lambda: stmt(csym_("returnnothing"))))

def stmt(s):
    global CSCOPE
    list_append(CSCOPE.csStmts, s)

def c_body(ss, funcinfo):
    global CSCOPE
    outer = CSCOPE
    CSCOPE = CScope([], funcinfo, outer)
    for s in ss:
        c_stmt(s)
    assert outer is CSCOPE.csOuterScope
    ss = CSCOPE.csStmts
    CSCOPE = outer
    return ss

def mogrify(mod):
    global CSCOPE
    CSCOPE = CScope([], None, None)
    ss = c_body(mod.roots, None)
    return Module("c_" + mod.name, None, ss)

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    write_mod_repr('hello', short)
    import hm
    hm.infer_types(short.roots)
    write_mod_repr('hello', short)
    print 'Inferred types.'
    c = mogrify(short)
    print 'Mogrified.'
    write_mod_repr('hello', c)
    serialize_module(short)
    serialize_module(c)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
