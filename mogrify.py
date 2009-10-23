#!/usr/bin/env python
from base import *
from atom import *
from builtins import *

CScope = DT('CScope', ('csStmts', [Atom]),
                      ('csFunc', str),
                      ('csIdentifierAtoms', {Atom: Atom}),
                      ('csStructNameAtoms', {Atom: Atom}),
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
        ("TData(a)", lambda a: cptr(struct_ref(a))))

def c_type(t, tvars):
    return _c_type(atoms_to_type(t, dict((v, TVar(0)) for v in tvars)))

def c_scheme(ta):
    t = atoms_to_scheme(ta)
    return _c_type(t.schemeType)

def as_c_op(a):
    return match(a, ("Ref(named(nm, contains(key('unaryop' or 'binaryop'))), "
                     "_, _)", identity),
                    ("_", lambda: None))

def set_identifier(atom, nm):
    global CSCOPE
    assert isinstance(nm, basestring)
    s = str_(nm)
    assert atom not in CSCOPE.csIdentifierAtoms
    CSCOPE.csIdentifierAtoms[atom] = s
    return s

# Bleh duplication
def set_struct_name(atom, nm):
    global CSCOPE
    assert isinstance(nm, basestring)
    s = str_(nm)
    assert atom not in CSCOPE.csStructNameAtoms
    CSCOPE.csStructNameAtoms[atom] = s
    return csym('name', [s])

def identifier_ref(a):
    global CSCOPE
    scope = CSCOPE
    while scope is not None:
        s = scope.csIdentifierAtoms.get(a)
        if s is not None:
            return Ref(s, None, [])
        scope = scope.csOuterScope
    if a in boot_syms:
        return str_(getname(a))
    assert False, '%r not in identifier scope' % (a,)

def struct_ref(a):
    global CSCOPE
    scope = CSCOPE
    while scope is not None:
        s = scope.csStructNameAtoms.get(a)
        if s is not None:
            return csym('structref', [Ref(s, None, [])])
        scope = scope.csOuterScope
    assert False, '%r not in struct name scope' % (a,)

def c_defref(r, a):
    # TODO
    assert as_c_op(r) is None, "Can't pass around built-in C op %s" % (nm,)
    return identifier_ref(a)

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

def global_scope():
    global CSCOPE
    scope = CSCOPE
    while scope.csOuterScope is not None:
        scope = scope.csOuterScope
    return scope

def strlit(s):
    return csym('strlit', [str_(s)])

def assert_false(msg_e):
    return csym('exprstmt', [callnamed('assert', [int_(0), msg_e])])

def c_match(e, retT, cs):
    eT = match(e.subs, ("contains(t==key('type'))", identity))
    fnm = 'matcher'
    sf = surrounding_func()
    if sf is not None:
        fnm = '%s_%s' % (sf.csFunc, fnm)
    arg = csym('arg', [c_scheme(eT)])
    arg.subs.append(set_identifier(arg, 'expr'))
    if_ = csym('if', []) # TODO
    body = [if_, assert_false(strlit('%s failed' % (fnm,)))]
    f = make_func(None, c_scheme(retT), fnm, [arg], body, [csym_('static')])
    list_append(global_scope().csStmts, f)
    return callnamed(fnm, [c_expr(e)])

def c_expr(e):
    return match(e,
        ("Int(i, _)", int_),
        ("Str(s, _)", strlit),
        ("r==Ref(a==named(_, contains(key('type'))), _, _)", c_defref),
        ("r==Ref(a==named(_) and key('ctor'), _, _)", c_defref),
        ("key('call', cons(f, sized(args)))", c_call),
        ("key('tuplelit', sized(ts))", c_tuple),
        ("key('match', cons(e, contains(retT==key('type')) "
                       "and all(cs, c==key('case'))))", c_match))

def is_func_scope(scope):
    return scope.csFunc is not None

def surrounding_func():
    global CSCOPE
    func = CSCOPE
    while func is not None and not is_func_scope(func):
        func = func.csOuterScope
    return func

def stmt_after_vardecls(stmt, scope):
    i = 0
    while i < len(scope.csStmts) and is_decl_or_defn(scope.csStmts[i]):
        i += 1
    scope.csStmts.insert(i, stmt)

def is_decl_or_defn(s):
    return match(s, ("key('vardecl' or 'vardefn')", lambda: True),
                    ("_", lambda: False))

def c_assign(a, e):
    ce = c_expr(e)
    nm, var, needs_decl = match(a,
        ("key('var') and named(nm)", lambda nm: (nm, a, True)),
        ("Ref(v==named(nm, contains(key('type'))), _, _)",
            lambda v, nm: (nm, v, False)))
    if needs_decl:
        s = set_identifier(var, nm)
        ct = match(a, ("key('var', contains(t==key('type')))", c_scheme))
        definition = lambda: stmt(csym('vardefn', [s, ct, ce]))
        # Check to see if we can set this right where we declare it
        global CSCOPE
        if is_func_scope(CSCOPE) and all(map(is_decl_or_defn, CSCOPE.csStmts)):
            definition()
            return
        # Otherwise find a suitable place to declare this variable
        func = surrounding_func()
        if func is None:
            definition()
            return
        stmt_after_vardecls(csym('vardecl', [s, ct]), func)
    stmt(csym('=', [identifier_ref(var), ce]))

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

def c_DT(dt, cs, vs, nm):
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
            stmt(csym('decl', [csym('struct', [set_struct_name(dt, nm)]
                                              + cfields)]))
        ctors.append((c, cnm, fields))
    enumsym = lambda cnm: str_('%s%s' % (nm, cnm))
    if discrim:
        # Generate our extra struct-around-union-around-ctors
        enum = csym('enum', [csym('enumerator', [enumsym(getname(c))])
                             for c in cs])
        union = csym('union', structs)
        stmt(csym('decl', [csym('struct', [set_struct_name(dt, nm),
                csym('field', [enum, str_('ix')]),
                csym('field', [union, str_('s')])])]))
    # Ctor functions
    for (ctor, cnm, fields) in ctors:
        var = lambda: str_(cnm.lower())
        args = [csym('arg', [t, str_(anm)]) for (t, anm) in fields]
        setup = [csym('vardefn', [var(), cptr(struct_ref(dt)),
                callnamed('malloc', [csym('sizeof', [struct_ref(dt)])])])]
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
        stmt(make_func(ctor, cptr(struct_ref(dt)), cnm, args, setup, []))

def c_args(args):
    return [match(a, ("named(nm, contains(t==key('type')))",
             lambda nm, t: csym('arg', [c_scheme(t), set_identifier(a, nm)])))
            for a in args]

def make_func(f, retT, nm, args, body, extra_attrs):
    fa = csym('func', [])
    s = set_identifier(f if f is not None else fa, nm)
    fa.subs = [retT, s, csym('args', [int_len(args)] + args),
               csym('body', [int_len(body)] + body)] + extra_attrs
    return fa

def c_func(f, t, args, body, nm):
    # Wow this is bad
    t_ = atoms_to_scheme(t).schemeType
    retT = c_scheme(scheme_to_atoms(Scheme([], t_.funcRet)))
    ca = c_args(args)
    cb = c_body(body, nm)
    stmt(make_func(f, retT, nm, ca, cb, []))

def c_stmt(s):
    match(s,
        ("key('exprstmt', cons(e, _))",
            lambda e: stmt(csym('exprstmt', [c_expr(e)]))),
        ("key('=', cons(a, cons(e, _)))", c_assign),
        ("key('cond', ss and all(cs, key('case', cons(t, sized(b)))))",c_cond),
        ("key('while', cons(t, contains(key('body', sized(b)))))", c_while),
        ("key('assert', cons(t, cons(m, _)))", c_assert),
        ("dt==key('DT', all(cs, c==key('ctor'))\
                and all(vs, v==key('typevar'))) and named(nm)", c_DT),
        ("f==key('func', contains(t==key('type')) "
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
    CSCOPE = CScope([], funcinfo, {}, {}, outer)
    for s in ss:
        c_stmt(s)
    assert outer is CSCOPE.csOuterScope
    ss = CSCOPE.csStmts
    CSCOPE = outer
    return ss

def mogrify(mod):
    global CSCOPE
    CSCOPE = CScope([], None, {}, {}, None)
    for s in mod.roots:
        c_stmt(s)
    return Module("c_" + mod.name, None, CSCOPE.csStmts)

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
