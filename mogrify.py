#!/usr/bin/env python
from base import *
from atom import *
from builtins import *

CScope = DT('CScope', ('csStmts', [Atom]),
                      ('csFuncName', str),
                      ('csIdentifierAtoms', {Atom: Atom}),
                      ('csStructNameAtoms', {Atom: Atom}),
                      ('csOuterScope', 'CScope'))
CSCOPE = None

DtInfo = DT('DtInfo', ('diIndexName', Atom),
                      ('diUnionName', Atom))
FieldInfo = DT('FieldInfo', ('fiDtInfo', DtInfo),
                            ('fiFieldName', Atom),
                            ('fiCtorName', Atom))

CGlobal = DT('CGlobal', ('cgIncludes', set([str])),
                        ('cgDTs', {Atom: DtInfo}),
                        ('cgCtors', {Atom: (Atom, Atom, Atom)}),
                        ('cgFields', {Atom: FieldInfo}),
                        ('cgTupleFuncs', {int: (Atom, Atom)}),
                        ('cgTupleType', Atom))
CGLOBAL = None

def add_include(filename):
    global CGLOBAL
    set_add(CGLOBAL.cgIncludes, filename)

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

def nmref(atom):
    assert isinstance(atom, Str), "Expected Str, got %s" % (atom,)
    return Ref(atom, None, [])

def _c_type(t):
    global CGLOBAL
    return match(t,
        ("TInt()", lambda: csym_('int')),
        ("TStr()", lambda: cptr(csym_('char'))),
        ("TTuple(_)", lambda: cptr(Ref(CGLOBAL.cgTupleType, None, []))),
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

def set_identifier(atom, nm, scope):
    if scope is None:
        global CSCOPE
        scope = CSCOPE
    assert isinstance(nm, basestring)
    s = str_(nm)
    assert atom not in scope.csIdentifierAtoms
    scope.csIdentifierAtoms[atom] = s
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
            return nmref(s)
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
            return csym('structref', [nmref(s)])
        scope = scope.csOuterScope
    assert False, '%r not in struct name scope' % (a,)

def vardefn_malloced(nm, t, t_size):
    add_include('stdlib.h')
    nm_atom = str_(nm)
    setup = csym('vardefn', [nm_atom, cptr(t), callnamed('malloc', [t_size])])
    return ([setup], lambda: nmref(nm_atom))

def c_defref(r, a):
    # TODO
    assert as_c_op(r) is None, "Can't pass around built-in C op %s" % (nm,)
    return match(r, # XXX: special cases, blah
            ("key('True')", lambda: int_(1)),
            ("key('False')", lambda: int_(0)),
            ("key('None')", lambda: csym_('NULL')),
            ("_", lambda: identifier_ref(a)))

def callnamed(nm, args):
    assert isinstance(nm, basestring)
    return csym('call', [str_(nm), int_len(args)] + args)

def callnamedref(nm_atom, args):
    assert isinstance(nm_atom, Str)
    return csym('call', [nmref(nm_atom), int_len(args)] + args)

# Binary operator shortcut
def bop(a, op, b):
    return csym(op, [a, b])

def c_call(f, args):
    op = as_c_op(f)
    if op is not None:
        return csym(op, map(c_expr, args))
    # big hack comin' up
    elif match(f, ('key("printf")', lambda: True), ('_', lambda: False)):
        add_include('stdio.h')
        fstr = c_expr(args[0])
        args = match(args[1], ('key("tuplelit", sized(args))', identity))
        return csym('call', [c_expr(f), int_(len(args)+1), fstr]
                + map(c_expr, args))
    else:
        return csym('call', [c_expr(f), int_len(args)] + map(c_expr, args))

# Currently boxed and void*'d to hell... hmmm...
def c_tuple(ts):
    n = len(ts)
    global CGLOBAL
    tupleT = lambda: Ref(CGLOBAL.cgTupleType, None, [])
    if n not in CGLOBAL.cgTupleFuncs:
        add_include('stdlib.h')
        nm = str_('tuple%d' % (n,))
        args = []
        body, var = vardefn_malloced('tup', tupleT(),
                bop(csym('sizeof', [tupleT()]), '*', int_(n)))
        i = 0
        while i < n:
            argnm = str_('t%d' % (i,))
            arg = csym('arg', [cptr(csym_('void')), argnm])
            list_append(args, arg)
            list_append(body,
                bop(csym('subscript', [var(), int_(i)]), '=', nmref(argnm)))
            i += 1
        list_append(body, csym('return', [var()]))
        f = make_func(None, cptr(tupleT()), nm, args, body, [csym_('static')])
        CGLOBAL.cgTupleFuncs[n] = (nm, f)
    else:
        nm, f = CGLOBAL.cgTupleFuncs[n]
    return callnamedref(nm, map(c_expr, ts))

def global_scope():
    global CSCOPE
    scope = CSCOPE
    while scope.csOuterScope is not None:
        scope = scope.csOuterScope
    return scope

def strlit(s):
    return csym('strlit', [str_(s)])

def assert_false(msg_e):
    add_include('assert.h')
    # TODO: Use msg_e
    return csym('exprstmt', [callnamed('assert', [int_(0)])])

CMatch = DT('CMatch', ('cmDecls', {str: (Atom, Atom, Atom)}),
                      ('cmConds', [Atom]),
                      ('cmAssigns', [Atom]),
                      ('cmCurExpr', Atom))
CMATCH = None

def c_match_int_literal(i):
    global CMATCH
    list_append(CMATCH.cmConds, bop(CMATCH.cmCurExpr, '==', int_(i)))

def c_match_str_literal(s):
    global CMATCH
    add_include('string.h')
    list_append(CMATCH.cmConds, bop(callnamed('strcmp',
        [CMATCH.cmCurExpr, strlit(s)]), '==', int_(0)))

def c_match_tuple(ps):
    global CMATCH
    old_expr = CMATCH.cmCurExpr
    i = 0
    for p in ps:
        CMATCH.cmCurExpr = csym('subscript', [old_expr, int_(i)])
        c_match_case(p)
        i += 1
    CMATCH.cmCurExpr = old_expr

def c_match_ctor(c, args):
    global CMATCH
    global CGLOBAL
    # Check index
    dt, cixname, csname = CGLOBAL.cgCtors[c]
    old_expr = CMATCH.cmCurExpr
    if cixname is not None:
        test = bop(bop(old_expr, '->', str_('ix')), '==', nmref(cixname))
        list_append(CMATCH.cmConds, test)
    fields = match(c, ("key('ctor', all(fs, f==key('field')))",
                       identity))
    get_field = None
    if csname is not None:
        get_field = lambda old_expr, fnm: bop(bop(bop(
            old_expr, '->', str_('s')), '.', nmref(csname)), '.', fnm)
    else:
        get_field = lambda old_expr, fnm: bop(old_expr, '->', fnm)
    for arg, field in zip(args, fields):
        # TODO: cmCurExpr will be duplicated across the AST... ugh...
        fnm = CGLOBAL.cgFields[field].fiFieldName
        CMATCH.cmCurExpr = get_field(old_expr, nmref(fnm))
        c_match_case(arg)
    CMATCH.cmCurExpr = old_expr

def c_match_var(v, t, nm):
    global CMATCH
    while nm in CMATCH.cmDecls:
        nm += '_'
    varnm = str_(nm)
    CMATCH.cmDecls[nm] = (v, varnm, csym('vardecl', [varnm, c_scheme(t)]))
    list_append(CMATCH.cmAssigns, bop(nmref(varnm), '=', CMATCH.cmCurExpr))

def c_match_capture(v, p):
    c_match_case(v)
    c_match_case(p)

def c_match_case(case):
    match(case,
            ("key('wildcard')", lambda: None),
            ("Int(i, _)", c_match_int_literal),
            ("Str(s, _)", c_match_str_literal),
            ("key('tuplelit', sized(ps))", c_match_tuple),
            ("key('ctor', cons(Ref(c, _, _), sized(args)))", c_match_ctor),
            ("v==key('var', contains(t==key('type'))) and named(nm)",
                c_match_var),
            ("key('capture', cons(v, cons(p, _)))", c_match_capture))

def c_match_case_names(case):
    return match(case,
            ("Int(i, _)", lambda: ['int']),
            ("Str(s, _)", lambda: ['str']),
            ("key('tuplelit', sized(ps))",
                lambda ps: concat_map(c_match_make_name, ps)),
            ("key('ctor', cons(Ref(c, _, _), _))", lambda c: [getname(c)]),
            ("named(nm) or key('capture', cons(named(nm), _))",
                lambda nm: [nm]),
            ("_", lambda: []))

def and_together(conds):
    if len(conds) == 0:
        return int_(1)
    elif len(conds) == 1:
        return conds[0]
    else:
        c = conds.pop(0)
        return bop(c, '&&', and_together(conds))

def c_match(e, retT, cs):
    eT = match(e.subs, ("contains(t==key('type'))", identity))
    sf = surrounding_func()
    nms = ['match'] if sf is None else [sf.csFuncName, 'match']
    arg = csym('arg', [c_scheme(eT)])
    argnm = set_identifier(arg, 'expr', None)
    list_append(arg.subs, argnm)
    # Convert each case to an if statement, with some decls for match vars
    cases = []
    decls = []
    global CMATCH
    for c in cs:
        m, b = match(c, ("key('case', cons(m, cons(b, _)))", tuple2))
        CMATCH = CMatch({}, [], [], argnm)
        c_match_case(m)
        list_concat(nms, c_match_case_names(m))
        matchvars = {}
        for orig_var, var_nm, new_var in CMATCH.cmDecls.itervalues():
            matchvars[orig_var] = var_nm
            list_append(decls, new_var)
        # Convert the success expr with the match vars bound to their decls
        global CSCOPE
        old_scope = CSCOPE
        CSCOPE = CScope([], 'matchfunc', matchvars, {}, old_scope)
        stmts = CMATCH.cmAssigns + [csym('return', [c_expr(b)])]
        CSCOPE = old_scope
        test = and_together(CMATCH.cmConds)
        list_append(cases, csym('case', [test, int_len(stmts)] + stmts))
    # Phew! Finally, create our match function
    fnm = str_('_'.join(nms))
    body = decls + [csym('if', cases),
                    assert_false(strlit('%s failed' % (fnm.strVal,)))]
    f = make_func(None, c_scheme(retT), fnm, [arg], body, [csym_('static')])
    list_append(global_scope().csStmts, f)
    return callnamedref(fnm, [c_expr(e)])

def c_attr(struct, a):
    global CGLOBAL
    fi = CGLOBAL.cgFields[a]
    if fi.fiCtorName is None:
        return bop(c_expr(struct), '->', nmref(fi.fiFieldName))
    else:
        return bop(bop(bop(c_expr(struct), '->', nmref(fi.fiCtorName)),
                '.', nmref(fi.fiDtInfo.diUnionName)),
                '.', nmref(fi.fiFieldName))

def c_expr(e):
    return match(e,
        ("Int(i, _)", int_),
        ("Str(s, _)", strlit),
        ("r==Ref(a==named(_, contains(key('type'))), _, _)", c_defref),
        ("r==Ref(a==named(_) and key('ctor'), _, _)", c_defref),
        ("key('call', cons(f, sized(args)))", c_call),
        ("key('tuplelit', sized(ts))", c_tuple),
        ("key('match', cons(e, contains(retT==key('type')) "
                       "and all(cs, c==key('case'))))", c_match),
        ("key('attr', cons(s, cons(Ref(a, _, _), _)))", c_attr))

def is_func_scope(scope):
    return scope.csFuncName is not None

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
        ct = match(a, ("key('var', contains(t==key('type')))", c_scheme))
        definition = lambda s: stmt(csym('vardefn', [s, ct, ce]))
        # Check to see if we can set this right where we declare it
        global CSCOPE
        if is_func_scope(CSCOPE) and all(map(is_decl_or_defn, CSCOPE.csStmts)):
            definition(set_identifier(var, nm, CSCOPE))
            return
        # Otherwise find a suitable place to declare this variable
        func = surrounding_func()
        if func is None:
            definition(set_identifier(var, nm, global_scope()))
            return
        # Declare it at the top of the function, but set it back here
        s = set_identifier(var, nm, func)
        stmt_after_vardecls(csym('vardecl', [s, ct]), func)
    stmt(bop(identifier_ref(var), '=', ce))

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
    add_include('assert.h')
    # TODO: Use m
    stmt(csym('exprstmt', [callnamed('assert', [c_expr(t)])]))

def c_DT(dt, cs, vs, nm):
    global CGLOBAL
    discrim = len(cs) > 1
    ctors = []
    structs = []
    enumsyms = []
    # Convert ctors to structs
    for c in cs:
        cnm, fs = match(c, ("named(nm, all(fs, f==key('field')))",
                            lambda cnm, fs: (str_(cnm), fs)))
        fields = [match(f, ("f==key('field', contains(key('type',cons(t,_))))",
                            lambda f, t: (c_type(t, vs), CGLOBAL.cgFields[f])))
                  for f in fs]
        cfields = [csym('field', [t, fi.fiFieldName]) for (t, fi) in fields]
        if discrim:
            cdt, cixname, csname = CGLOBAL.cgCtors[c]
            list_append(structs, csym('field', [csym('struct', cfields),
                                                csname]))
            list_append(enumsyms, csym('enumerator', [cixname]))
        else:
            stmt(csym('decl', [csym('struct', [set_struct_name(dt, nm)]
                                              + cfields)]))
        ctors.append((c, cnm, fields))
    dtinfo = CGLOBAL.cgDTs[dt]
    discrim_union = discrim_ix = None
    if discrim:
        # Generate our extra struct-around-union-around-ctors
        enum = csym('enum', enumsyms)
        union = csym('union', structs)
        discrim_ix = lambda: nmref(dtinfo.diIndexName)
        discrim_union = lambda: nmref(dtinfo.diUnionName)
        stmt(csym('decl', [csym('struct', [set_struct_name(dt, nm),
                csym('field', [enum, dtinfo.diIndexName]),
                csym('field', [union, dtinfo.diUnionName])])]))
    # Ctor functions
    for (ctor, cnm, fields) in ctors:
        cdt, cixname, csname = CGLOBAL.cgCtors[ctor]
        varnm = cnm.strVal.lower()
        body, var = vardefn_malloced(varnm, struct_ref(dt),
                                     csym('sizeof', [struct_ref(dt)]))
        argnms = {}
        if discrim:
            list_append(body, bop(bop(var(), '->', discrim_ix()),
                                  '=', nmref(cixname)))
        # Set all the fields from ctor args
        args = []
        for (ct, fi) in fields:
            argnm = str_(fi.fiFieldName.strVal)
            # Check for name conflicts; this should be done more generally
            while argnm.strVal == varnm:
                argnm.strVal = argnm.strVal + '_'
            # Add the arg and assign it
            list_append(args, csym('arg', [ct, argnm]))
            fieldref = nmref(fi.fiFieldName)
            if discrim:
                s = bop(bop(bop(var(), '->', discrim_union()),
                            '.', nmref(csname)), '.', fieldref)
            else:
                s = bop(var(), '->', fieldref)
            list_append(body, bop(s, '=', nmref(argnm)))
        list_append(body, csym('return', [var()]))
        stmt(make_func(ctor, cptr(struct_ref(dt)), cnm, args, body, []))

def make_func(f, retT, nm, args, body, extra_attrs):
    global CSCOPE
    fa = csym('func', [])
    atom = f if f is not None else fa
    assert isinstance(nm, Str)
    assert atom not in CSCOPE.csIdentifierAtoms
    CSCOPE.csIdentifierAtoms[atom] = nm
    fa.subs = [retT, nm, csym('args', [int_len(args)] + args),
               csym('body', [int_len(body)] + body)] + extra_attrs
    return fa

def _setup_func(scope, nm, args, cargs):
    scope.csFuncName = nm
    idents = {}
    for a in args:
        nm, t = match(a, ("named(nm, contains(t==key('type')))", tuple2))
        carg = csym('arg', [c_scheme(t), set_identifier(a, nm, scope)])
        list_append(cargs, carg)

def c_func(f, t, args, body, nm):
    # Wow this is bad
    t_ = atoms_to_scheme(t).schemeType
    retT = c_scheme(scheme_to_atoms(Scheme([], t_.funcRet)))
    ca = []
    cb = c_body(body, lambda scope: _setup_func(scope, nm, args, ca))
    stmt(make_func(f, retT, str_(nm), ca, cb, []))

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

def c_body(ss, scope_func):
    global CSCOPE
    outer = CSCOPE
    CSCOPE = CScope([], None, {}, {}, outer)
    if scope_func is not None:
        scope_func(CSCOPE)
    for s in ss:
        c_stmt(s)
    assert outer is CSCOPE.csOuterScope
    ss = CSCOPE.csStmts
    CSCOPE = outer
    return ss

def scan_DTs(roots):
    dts = {}
    ctors = {}
    fields = {}
    for root in roots:
        dt, cs = match(root, ("dt==key('DT', all(cs, c==key('ctor')))",tuple2),
                             ("_", lambda: (None, [])))
        if dt is None:
            continue
        dtnm = getname(dt)
        discrim = (len(cs) != 1)
        dtinfo = DtInfo(str_('ix'), str_('s')) if discrim \
                                               else DtInfo(None, None)
        dts[dt] = dtinfo
        for c in cs:
            cnm = getname(c)
            fs = match(c.subs, ("all(fs, f==key('field') and named(nm))",
                                identity))
            enumname = None
            structname = None
            if discrim:
                enumname = str_(dtnm + cnm)
                structname = str_(cnm)
            ctors[c] = (dt, enumname, structname)
            for f, fnm in fs:
                fields[f] = FieldInfo(dtinfo, str_(fnm), structname)
    tupleT = csym('typedef', [cptr(csym_('void')), str_('tuple')])
    return CGlobal(set(), dts, ctors, fields, {}, tupleT)

def mogrify(mod):
    global CSCOPE
    CSCOPE = CScope([], None, {}, {}, None)
    global CGLOBAL
    CGLOBAL = scan_DTs(mod.roots)
    for s in mod.roots:
        c_stmt(s)
    incls = [csym('includesys', [str_(incl)]) for incl in CGLOBAL.cgIncludes]
    tup_funcs = [f for (nm, f) in CGLOBAL.cgTupleFuncs.itervalues()]
    if len(tup_funcs) > 0:
        list_prepend(tup_funcs, CGLOBAL.cgTupleType)
    cstmts = incls + tup_funcs + CSCOPE.csStmts
    return Module("c_" + mod.name, None, cstmts)

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
