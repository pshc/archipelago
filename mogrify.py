#!/usr/bin/env python2
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
CtorInfo = DT('CtorInfo', ('ciDtInfo', DtInfo),
                          ('ciEnumName', Atom),
                          ('ciStructName', Atom))
FieldInfo = DT('FieldInfo', ('fiDtInfo', DtInfo),
                            ('fiFieldName', Atom),
                            ('fiCtorName', Atom))

CGlobal = DT('CGlobal', ('cgTypeAnnotations', {Atom: Scheme}),
                        ('cgIncludes', set([str])),
                        ('cgDTs', {Atom: DtInfo}),
                        ('cgCtors', {Atom: CtorInfo}),
                        ('cgFields', {Atom: FieldInfo}),
                        ('cgTupleFuncs', {int: (Atom, Atom)}),
                        ('cgTupleType', Atom))
CGLOBAL = None

# As usual, defeats the whole purpose.
loaded_export_struct_name_atoms = {}

def add_include(filename):
    global CGLOBAL
    set_add(CGLOBAL.cgIncludes, filename)

# ensure we don't accidentally use symref() since it will be accepted silently
_atom_symref = symref
del symref
del add_sym
def csym(name, subs):
    assert isinstance(subs, list), 'Expected list; got %s' % (subs,)
    return Ref(CSYM_NAMES[name], subs)

CSYM_NAMES = {}
def add_csym(*names):
    for name in names:
        if name not in CSYM_NAMES:
            CSYM_NAMES[name] = None

def csym_(name):
    return csym(name, [])

add_csym('ptr')
def cptr(t):
    return csym('ptr', [t])

add_csym('name')
def cname(nm):
    return csym('name', [str_(nm)])

def nmref(atom):
    assert isinstance(atom, Str), "Expected Str, got %s" % (atom,)
    return Ref(atom, [])

def lookup_scheme(e):
    global CGLOBAL
    assert e in CGLOBAL.cgTypeAnnotations, "No type annotation for %s" % (e,)
    return CGLOBAL.cgTypeAnnotations[e]

add_csym('int', 'char', 'void', 'somefunc_t')
def c_type(t):
    global CGLOBAL
    return match(t,
        ("TInt() or TBool()", lambda: csym_('int')),
        ("TStr()", lambda: cptr(csym_('char'))),
        ("TTuple(_)", lambda: cptr(Ref(CGLOBAL.cgTupleType, []))),
        ("TNullable(t)", c_type),
        ("TVoid()", lambda: csym_('void')),
        ("TVar(_)", lambda: cptr(csym_('void'))),
        ("TData(a)", lambda a: cptr(struct_ref(a))),
        ("TFunc(_, _)", lambda: csym_('somefunc_t')), # TODO
        ("TApply(t, _)", c_type))

def c_type_(ta):
    t = atoms_to_type(ta)
    #print 'CONVERTED TYPE', t, 'INTO CTYPE:'
    result = c_type(t)
    #print result
    return result

def c_scheme(s):
    return match(s, ("Scheme(_, t)", c_type))

def as_c_op(a):
    return match(a,
       ("Ref(named(nm, contains(key('unaryop' or 'binaryop'))), _)", identity),
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
add_csym('name')
def set_struct_name(atom, nm):
    global CSCOPE
    assert isinstance(nm, basestring)
    s = str_(nm)
    assert atom not in CSCOPE.csStructNameAtoms
    CSCOPE.csStructNameAtoms[atom] = s
    loaded_export_struct_name_atoms[atom] = s
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

add_csym('structref')
def struct_ref(a):
    global CSCOPE
    scope = CSCOPE
    while scope is not None:
        s = scope.csStructNameAtoms.get(a)
        if s is not None:
            return csym('structref', [nmref(s)])
        scope = scope.csOuterScope
    # TEMP; should be really checking the imports list
    if a in loaded_export_struct_name_atoms:
        return csym('structref', [nmref(loaded_export_struct_name_atoms[a])])
    assert False, '%r not in struct name scope' % (a,)

add_csym('vardef')
def vardefn_malloced(nm, t, t_size):
    add_include('stdlib.h')
    nm_atom = str_(nm)
    setup = csym('vardefn', [nm_atom, cptr(t), callnamed('malloc', [t_size])])
    return ([setup], lambda: nmref(nm_atom))

add_csym('NULL')
def c_defref(r, a):
    # TODO
    assert as_c_op(r) is None, "Can't pass around built-in C op %s" % (nm,)
    return match(r, # XXX: special cases, blah
            ("key('True')", lambda: int_(1)),
            ("key('False')", lambda: int_(0)),
            ("key('None')", lambda: csym_('NULL')),
            ("_", lambda: identifier_ref(a)))

add_csym('call')
def callnamed(nm, args):
    assert isinstance(nm, basestring)
    return csym('call', [str_(nm), int_len(args)] + args)

def callnamedref(nm_atom, args):
    assert isinstance(nm_atom, Str)
    return csym('call', [nmref(nm_atom), int_len(args)] + args)

add_csym('+', '-', '*', '==', '!=', '<', '<=', '>', '>=')
# Binary operator shortcut
def bop(a, op, b):
    return csym(op, [a, b])

add_csym('call')
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

add_csym('arg', 'return', 'static')
# This sucks, we should be converting the lambda into a func earlier
def c_lambda(lam, args, e):
    argTs, retT = match(lookup_scheme(lam), ('Scheme(_, TFunc(a, r))', tuple2))
    fnm = str_('lambda')
    cargs = [csym('arg', [c_type(t), None]) for a, t in zip(args, argTs)]
    # XXX: use _setup_func instead OR REVAMP THIS CRAP
    def _setup_lambda(scope):
        scope.csFuncName = fnm.strVal
        for a, ca in zip(args, cargs):
            ca.subs[1] = set_identifier(a, getname(a), scope)
    cb = c_body([_atom_symref('return', [e])], _setup_lambda)
    lam = make_func(None, c_type(retT), fnm, cargs, cb, [csym_('static')])
    insert_global_decl(lam)
    return nmref(fnm)

add_csym('sizeof', 'arg', 'void', 'subscript', '=', 'return', 'static')
# Currently boxed and void*'d to hell... hmmm...
def c_tuple(ts):
    n = len(ts)
    global CGLOBAL
    tupleT = lambda: Ref(CGLOBAL.cgTupleType, [])
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

def insert_global_decl(f):
    list_append(global_scope().csStmts, f)

add_csym('strlit')
def strlit(s):
    return csym('strlit', [str_(s)])

add_csym('exprstmt', 'assert')
def assert_false(msg_e):
    add_include('assert.h')
    # TODO: Use msg_e
    return csym('exprstmt', [callnamed('assert', [int_(0)])])

CMatch = DT('CMatch', ('cmDecls', {str: (Atom, Atom, Atom)}),
                      ('cmConds', [Atom]),
                      ('cmAssigns', [Atom]),
                      ('cmCurExpr', Atom))
CMATCH = None

add_csym('==')
def c_match_int_literal(i):
    global CMATCH
    list_append(CMATCH.cmConds, bop(CMATCH.cmCurExpr, '==', int_(i)))

add_csym('==')
def c_match_str_literal(s):
    global CMATCH
    add_include('string.h')
    list_append(CMATCH.cmConds, bop(callnamed('strcmp',
        [CMATCH.cmCurExpr, strlit(s)]), '==', int_(0)))

add_csym('subscript')
def c_match_tuple(ps):
    global CMATCH
    old_expr = CMATCH.cmCurExpr
    i = 0
    for p in ps:
        CMATCH.cmCurExpr = csym('subscript', [old_expr, int_(i)])
        c_match_case(p)
        i += 1
    CMATCH.cmCurExpr = old_expr

add_csym('->', '.')
def c_field_lookup(mogrified_expr, fieldinfo):
    fi = fieldinfo
    if fi.fiCtorName is None:
        return bop(mogrified_expr, '->', nmref(fi.fiFieldName))
    else:
        return bop(bop(bop(mogrified_expr,
                '->', nmref(fi.fiDtInfo.diUnionName)),
                '.', nmref(fi.fiCtorName)),
                '.', nmref(fi.fiFieldName))

add_csym('->')
def c_ctor_index_test(mogrified_expr, test_op, ctorinfo):
    ci = ctorinfo
    assert ci.ciEnumName
    return bop(bop(mogrified_expr, '->', nmref(ci.ciDtInfo.diIndexName)),
            test_op, nmref(ci.ciEnumName))

add_csym('==')
def c_match_ctor(c, args):
    global CMATCH
    global CGLOBAL
    # Check index
    ci = CGLOBAL.cgCtors[c]
    old_expr = CMATCH.cmCurExpr
    if ci.ciEnumName is not None:
        list_append(CMATCH.cmConds, c_ctor_index_test(old_expr, '==', ci))
    fields = match(c, ("key('ctor', all(fs, f==key('field')))",
                       identity))
    for arg, field in zip(args, fields):
        # TODO: cmCurExpr will be duplicated across the AST... ugh...
        CMATCH.cmCurExpr = c_field_lookup(old_expr, CGLOBAL.cgFields[field])
        c_match_case(arg)
    CMATCH.cmCurExpr = old_expr

add_csym('vardecl', '=')
def c_match_var(v, nm):
    t = lookup_scheme(v)
    # TODO: Do this more generally
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
            ("key('ctor', cons(Ref(c, _), sized(args)))", c_match_ctor),
            ("v==key('var') and named(nm)", c_match_var),
            ("key('capture', cons(v, cons(p, _)))", c_match_capture))

def c_match_case_names(case):
    return match(case,
            ("Int(i, _)", lambda: ['int']),
            ("Str(s, _)", lambda: ['str']),
            ("key('tuplelit', sized(ps))",
                lambda ps: concat_map(c_match_make_name, ps)),
            ("key('ctor', cons(Ref(c, _), _))", lambda c: [getname(c)]),
            ("named(nm) or key('capture', cons(named(nm), _))",
                lambda nm: [nm]),
            ("_", lambda: []))

add_csym('&&')
def and_together(conds):
    if len(conds) == 0:
        return int_(1)
    elif len(conds) == 1:
        return conds[0]
    else:
        c = conds.pop(0)
        return bop(c, '&&', and_together(conds))

add_csym('else', 'case', 'if')
def c_match_cases(cs, argnm, result_f):
    # Convert each case to an if statement, with some decls for match vars
    sf = surrounding_func()
    nms = ['match'] if sf is None else [sf.csFuncName, 'match']
    cases = []
    decls = []
    body = []
    otherwise = False
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
        case = CMATCH.cmAssigns + [result_f(c_expr(b))]
        CSCOPE = old_scope
        if len(CMATCH.cmConds) == 0:
            if len(cases) == 0:
                body = case
            else:
                list_append(cases, csym('else', [int_len(case)] + case))
                otherwise = True
            break
        test = and_together(CMATCH.cmConds)
        list_append(cases, csym('case', [test, int_len(case)] + case))
    fnm = '_'.join(nms)
    if len(body) == 0:
        if not otherwise:
            list_append(cases, csym('else', [int_(1),
                        assert_false('%s failed' % (fnm,))]))
        body = [csym('if', cases)]
    return (str_(fnm), decls, body)

def _is_void_atom_type(s): # DUMB
    return match(s, ("key('type', cons(key('void'), _))", lambda: True),
                    ("_", lambda: False))

def c_match_bits(m):
    e, cs = match(m, ("key('match', cons(e, all(cs,c==key('case'))))", tuple2))
    eT = c_scheme(lookup_scheme(e))
    retT = c_scheme(lookup_scheme(m))
    return e, eT, retT, cs

add_csym('arg', 'exprstmt', 'return', 'static')
def c_match(matchExpr):
    e, eT, retT, cs = c_match_bits(matchExpr)
    arg = csym('arg', [eT])
    argnm = set_identifier(arg, 'expr', None)
    list_append(arg.subs, argnm)
    res_action = 'exprstmt' if _is_void_atom_type(retT) else 'return'

    fnm, decls, caseStmts = c_match_cases(cs, argnm,
            lambda ce: csym(res_action, [ce]))

    body = decls + caseStmts
    f = make_func(None, retT, fnm, [arg], body, [csym_('static')])
    insert_global_decl(f)
    return callnamedref(fnm, [c_expr(e)])

add_csym('exprstmt', '=', 'vardecl')
def c_match_inline(matchExpr, inline_f):
    e, eT, retT, cs = c_match_bits(matchExpr)
    func = surrounding_func()
    assert func is not None
    # NOTE: This is conjuring two new variables out of nowhere that don't get
    #         registered in the symbol table
    #       This has nasty implications for symbol clashing detection
    # TODO: Inline this in a previous pass
    match_nm = c_assign_new_vardecl(None, eT, 'match', e, func)
    res_nm = str_('result')
    is_void = _is_void_atom_type(retT)

    fnm, decls, body = c_match_cases(cs, match_nm,
            lambda ce: csym('exprstmt', [ce]) if is_void
                       else bop(nmref(res_nm), '=', ce))

    if not is_void:
        list_append(decls, csym('vardecl', [res_nm, retT]))
    insert_vardecls(decls, func)
    stmts(body)
    if not is_void:
        stmt(inline_f(nmref(res_nm)))

def c_attr(struct, a):
    global CGLOBAL
    fi = CGLOBAL.cgFields[a]
    return c_field_lookup(c_expr(struct), fi)

def c_expr(e):
    return match(e,
        ("Int(i, _)", int_),
        ("Str(s, _)", strlit),
        ("key('call', cons(f, sized(args)))", c_call),
        ("lam==key('lambda', sized(args, cons(e, _)))", c_lambda),
        ("key('tuplelit', sized(ts))", c_tuple),
        ("key('match')", lambda: c_match(e)),
        ("key('attr', cons(s, cons(Ref(a, _), _)))", c_attr),
        ("r==Ref(a, _)", c_defref))

# Can inline stmts required for computing `e' right here; and the final value
# inlines into the final stmt with `stmt_f'
def c_expr_inline_stmt(e, stmt_f):
    match(e,
        ("key('match')", lambda: c_match_inline(e, stmt_f)),
        ("_", lambda: stmt(stmt_f(c_expr(e)))))

def is_func_scope(scope):
    return scope.csFuncName is not None

def surrounding_func():
    global CSCOPE
    func = CSCOPE
    while func is not None and not is_func_scope(func):
        func = func.csOuterScope
    return func

def insert_vardecls(decls, scope):
    i = 0
    while i < len(scope.csStmts) and is_decl_or_defn(scope.csStmts[i]):
        i += 1
    scope.csStmts[i:i] = decls

def is_decl_or_defn(s):
    return match(s, ("key('vardecl' or 'vardefn')", lambda: True),
                    ("_", lambda: False))

add_csym('vardecl', '=')
def c_assign_new_vardecl(var, csch, nm, e, func_scope):
    s = set_identifier(var, nm, func_scope) if var is not None else str_(nm)
    insert_vardecls([csym('vardecl', [s, csch])], func_scope)
    c_expr_inline_stmt(e, lambda c: bop(s, '=', c))
    return s

add_csym('vardefn')
def c_assign_new_decl(var, e):
    ct = c_scheme(lookup_scheme(var))
    nm = getname(var)
    func = surrounding_func()
    if func is not None:
        c_assign_new_vardecl(var, ct, nm, e, func)
    else:
        s = set_identifier(var, nm, global_scope())
        stmt(csym('vardefn', [s, ct, c_expr(e)]))

add_csym('=')
def c_assign_existing(var, e):
    c_expr_inline_stmt(e, lambda c: bop(identifier_ref(var), '=', c))

add_csym('case', 'else', 'if')
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

add_csym('while')
def c_while(t, body):
    # OH GOD SIDE EFFECTS?
    ct = c_expr(t)
    cb = c_body(body, None)
    stmt(csym('while', [ct, int_len(cb)] + cb))

add_csym('exprstmt', 'assert')
def c_assert(t, m):
    add_include('assert.h')
    # TODO: Use m
    stmt(csym('exprstmt', [callnamed('assert', [c_expr(t)])]))

add_csym('field', 'struct', 'enumerator', 'decl', 'enum', 'union', 'sizeof',
        '=', 'arg', 'return')
def c_DT(dt, cs, vs, nm):
    global CGLOBAL
    discrim = len(cs) > 1
    ctors = []
    structs = []
    enumsyms = []
    dt_nm_atom = set_struct_name(dt, nm)
    # Convert ctors to structs
    for c in cs:
        fs = match(c, ("key('ctor', all(fs, f==key('field')))", identity))
        fields = [match(f, ("f==key('field', contains(key('type',cons(t,_))))",
                            lambda f, t: (c_type_(t), CGLOBAL.cgFields[f])))
                  for f in fs]
        cfields = [csym('field', [t, fi.fiFieldName]) for (t, fi) in fields]
        if discrim:
            ci = CGLOBAL.cgCtors[c]
            list_append(structs, csym('field', [csym('struct', cfields),
                                                ci.ciStructName]))
            list_append(enumsyms, csym('enumerator', [ci.ciEnumName]))
        else:
            stmt(csym('decl', [csym('struct', [dt_nm_atom] + cfields)]))
        ctors.append((c, fields))
    dtinfo = CGLOBAL.cgDTs[dt]
    if discrim:
        # Generate our extra struct-around-union-around-ctors
        enum = csym('enum', enumsyms)
        union = csym('union', structs)
        stmt(csym('decl', [csym('struct', [dt_nm_atom,
                csym('field', [enum, dtinfo.diIndexName]),
                csym('field', [union, dtinfo.diUnionName])])]))
    # Ctor functions
    for (ctor, fields) in ctors:
        ci = CGLOBAL.cgCtors[ctor]
        ctornm = str_(getname(ctor))
        varnm = ctornm.strVal.lower()
        body, var = vardefn_malloced(varnm, struct_ref(dt),
                                     csym('sizeof', [struct_ref(dt)]))
        argnms = {}
        if discrim:
            list_append(body, c_ctor_index_test(var(), '=', ci))
        # Set all the fields from ctor args
        args = []
        for (ct, fi) in fields:
            argnm = str_(fi.fiFieldName.strVal)
            # Check for name conflicts; this should be done more generally
            while argnm.strVal == varnm:
                argnm.strVal = argnm.strVal + '_'
            # Add the arg and assign it
            list_append(args, csym('arg', [ct, argnm]))
            assignment = bop(c_field_lookup(var(), fi), '=', nmref(argnm))
            list_append(body, assignment)
        list_append(body, csym('return', [var()]))
        stmt(make_func(ctor, cptr(struct_ref(dt)), ctornm, args, body, []))

add_csym('func', 'args', 'body')
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

add_csym('arg')
def _setup_func(scope, nm, args, argTs, cargs):
    scope.csFuncName = nm
    for a, t in zip(args, argTs):
        carg = csym('arg', [c_type(t), set_identifier(a, getname(a), scope)])
        list_append(cargs, carg)

def c_func(f, args, body, nm):
    t = lookup_scheme(f)
    argTs, retT = match(t, ("Scheme(_, TFunc(args, ret))", tuple2))
    ca = []
    cb = c_body(body, lambda scope: _setup_func(scope, nm, args, argTs, ca))
    stmt(make_func(f, c_type(retT), str_(nm), ca, cb, []))

add_csym('exprstmt', 'return')
def c_stmt(s):
    match(s,
        ("key('exprstmt', cons(e, _))",
            lambda e: c_expr_inline_stmt(e, lambda c: csym('exprstmt', [c]))),
        ("key('=', cons(v==key('var'), cons(e, _)))", c_assign_new_decl),
        ("key('=', cons(Ref(v, _), cons(e, _)))", c_assign_existing),
        ("key('cond', ss and all(cs, key('case', cons(t, sized(b)))))",c_cond),
        ("key('while', cons(t, contains(key('body', sized(b)))))", c_while),
        ("key('assert', cons(t, cons(m, _)))", c_assert),
        ("dt==key('DT', all(cs, c==key('ctor'))\
                and all(vs, v==key('typevar'))) and named(nm)", c_DT),
        ("f==key('func', contains(key('args', sized(a))) "
                 "and contains(key('body', sized(b)))) and named(nm)", c_func),
        ("key('return', cons(e, _))",
            lambda e: c_expr_inline_stmt(e, lambda c: csym('return', [c]))),
        ("key('returnnothing')", lambda: stmt(csym_("returnnothing"))))

def stmt(s):
    global CSCOPE
    list_append(CSCOPE.csStmts, s)

def stmts(ss):
    global CSCOPE
    CSCOPE.csStmts += ss

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

add_csym('typedef', 'void')
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
            ctors[c] = CtorInfo(dtinfo, enumname, structname)
            for f, fnm in fs:
                fields[f] = FieldInfo(dtinfo, str_(fnm), structname)
    tupleT = csym('typedef', [cptr(csym_('void')), str_('tuple')])
    return CGlobal({}, set(), dts, ctors, fields, {}, tupleT)

add_csym('includesys')
def mogrify(mod, types):
    global CSCOPE
    CSCOPE = CScope([], None, {}, loaded_export_struct_name_atoms, None)
    global CGLOBAL
    CGLOBAL = scan_DTs(mod.roots)
    CGLOBAL.cgTypeAnnotations = types
    for s in mod.roots:
        c_stmt(s)
    incls = [csym('includesys', [str_(incl)]) for incl in CGLOBAL.cgIncludes]
    tup_funcs = [f for (nm, f) in CGLOBAL.cgTupleFuncs.itervalues()]
    if len(tup_funcs) > 0:
        list_prepend(tup_funcs, CGLOBAL.cgTupleType)
    cstmts = incls + tup_funcs + CSCOPE.csStmts
    return Module("c_" + mod.name, None, cstmts)

# ALL CSYMS CREATED
csym_roots = []
for nm in CSYM_NAMES.keys():
    CSYM_NAMES[nm] = sym = _atom_symref('symbol', [symname(nm)])
    csym_roots.append(sym)
serialize_module(Module('csyms', None, csym_roots))

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    write_mod_repr('hello', short, [])
    import hm
    types = hm.infer_types(short.roots)
    write_mod_repr('hello', short, [types])
    print 'Inferred types.'
    c = mogrify(short, types)
    print 'Mogrified.'
    write_mod_repr('hello', c, [])
    serialize_module(short)
    serialize_module(c)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
