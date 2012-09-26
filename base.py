import compiler
from types import FunctionType

SUPERS = {}
DATATYPES = {}
CTORS = {}

class Structured(object):
    pass

class CopiedCtors(object):
    pass

_deferred_type_parses = []

def _make_ctor(name, members, superclass):
    nms = tuple(nm for nm, t in members)
    ix = len(DATATYPES)
    def __init__(self, *args, **tvars):
        self._ix = ix
        for i, nm in enumerate(nms):
            setattr(self, nm, args[i])
    attrs = dict(__slots__=(nms + ('_ix',)), __init__=__init__,
                 __types__=tuple(t for nm, t in members))
    ctor = type(name, (superclass,), attrs)
    SUPERS[ctor] = superclass
    superclass.ctors.append(ctor)
    CTORS.setdefault(name, []).append(ctor)
    return ctor

def DT(*members, **opts):
    members = list(members)
    name = members.pop(0)
    t = type(name, (Structured,), {'ctors': [], '_opts': opts})
    ctor = _make_ctor(name, members, t)
    _dt_form(t, None)
    DATATYPES[name] = t
    return ctor

def ADT(*ctors, **opts):
    ctors = list(ctors)
    tname = ctors.pop(0)
    derivedFrom = None
    derivedSubsts = None
    if isinstance(tname, tuple):
        if len(tname) == 3:
            tname, derivedFrom, subs = tname
            derivedSubsts = dict((extrinsic(FormSpec,s), extrinsic(FormSpec,d))
                                 for s, d in subs.iteritems())
        else:
            tname, derivedFrom = tname
    t = type(tname, (Structured,), {'ctors': [], '_opts': opts})
    data = [t]
    ctor_ix = 0

    def setup_ctor(name, members):
        d = _make_ctor(name, members, t)
        d.__module__ = tname
        d._ctor_ix = ctor_ix
        return d

    tvars = None
    if derivedFrom:
        tvars = {}
        shortcut = CopiedCtors()
        data.append(shortcut)
        for ctor in derivedFrom.ctors:
            # copy ctor (without zip())
            members = []
            for i, field in enumerate(extrinsic(FormSpec, ctor).fields):
                newType = derive_copied_ctor_type(field.type, derivedFrom, t,
                        derivedSubsts or {}, tvars)
                members.append((ctor.__slots__[i], newType))

            ctor_nm = ctor.__name__
            d = setup_ctor(ctor_nm, members)
            CTORS['%s.%s' % (tname, ctor_nm)] = [d]
            ctor_ix += 1
            setattr(shortcut, ctor_nm, d)

        # restore name->tv mapping
        tvars = dict((extrinsic(Name, tv), tv) for tv in tvars.itervalues())

    while ctors:
        ctor = ctors.pop(0)
        members = []
        while ctors and not isinstance(ctors[0], basestring):
            members.append(ctors.pop(0))
        d = setup_ctor(ctor, members)
        ctor_ix += 1
        data.append(d)
    _dt_form(t, tvars)
    DATATYPES[tname] = t
    return tuple(data)

def _dt_form(dt, deriveeTVars):
    assert not deriveeTVars

# Envs

EnvInfo = DT('EnvInfo', ('envName', str), ('envType', 'Type'),
                        ('envStack', '[a]'))

_ENVS = set()

def new_env(name, t):
    assert isinstance(name, basestring)
    if t is not None:
        tvars = {}
        t = parse_new_type(t, tvars)
    e = EnvInfo(name, t, [])
    _ENVS.add(e)
    return e

def in_env(e, initial, func):
    stack = e.envStack
    stack.append(initial)
    count = len(stack)
    ret = func()
    assert len(stack) == count, 'Imbalanced env %s stack' % e.envName
    stack.pop()
    return ret

def env(e):
    assert len(e.envStack), 'Not in env %s at present' % e.envName
    return e.envStack[-1]

def have_env(e):
    return bool(e.envStack)

def display_envs(verbose=False):
    for e in _ENVS:
        if e.envStack:
            print col('Purple', e.envName + ':')
            if verbose:
                for s in e.envStack:
                    print repr(s)
            else:
                print repr(e.envStack[-1])

# stupid debugger shortcut
class DumpEnvs(object):
    def __repr__(self):
        display_envs()
        return '<DumpEnvs>'
dumpenvs = DumpEnvs()

# for more readable stack dumps etc.
class DumpList(list):
    def __repr__(self):
        return ''.join('%r\n' % (e,) for e in self)

TVARS = new_env('TVARS', None)
NEWTYPEVARS = new_env('NEWTYPEVARS', None)

# Extrinsics

ExtInfo = DT('ExtInfo', ('label', str), ('t', 'Type'), ('stack', [{'a': 't'}]),
                        ('captures', [{'a': 't'}]))

def new_extrinsic(label, t, omni=False):
    if t is not None:
        tvars = {}
        t = parse_new_type(t, tvars)
    return ExtInfo(label, t, [{}] if omni else [], [])

def extrinsic(ext, obj):
    assert ext.stack, "Not in extrinsic %s" % (ext.label,)
    record = ext.stack[-1]
    assert obj in record, '%r has no %s' % (obj, ext.label)
    return record[obj]

def scope_extrinsic(ext, func):
    new = ext.stack[-1].copy() if len(ext.stack) else {}
    ext.stack.append(new)
    ret = func()
    n = ext.stack.pop()
    assert n is new, "Extrinsic stack imbalance"
    return ret

def capture_extrinsic(ext, cap, func):
    assert isinstance(cap, dict)
    ext.captures.append(cap)
    ret = func()
    off = ext.captures.pop()
    assert off is cap, "Imbalanced capture"
    return ret

def capture_scoped(exts, captures, func):
    # Inlined to avoid polluting stack trace
    check = []
    for ext in exts:
        assert ext not in captures
        cap = captures[ext] = {}
        ext.captures.append(cap)
        new = ext.stack[-1].copy() if len(ext.stack) else {}
        ext.stack.append(new)
        check.append((cap, new))

    ret = func()

    for ext, (offcap, offnew) in ezip(exts[::-1], check[::-1]):
        cap = ext.captures.pop()
        assert offcap is cap, "Imbalanced capture"
        n = ext.stack.pop()
        assert offnew is n, "Extrinsic stack imbalance"

    return ret

def in_extrinsic_scope(ext):
    return bool(ext.stack)

def add_extrinsic(ext, obj, val):
    assert not isinstance(obj, value_types), "%s on value %r" % (ext.label,obj)
    assert ext.stack, "Not in extrinsic %s" % (ext.label,)
    map = ext.stack[-1]
    assert obj not in map, "%r already has %s extrinsic" % (obj, ext.label)
    map[obj] = val
    if len(ext.captures) > 0:
        cap = ext.captures[-1]
        assert obj not in cap
        cap[obj] = val

def update_extrinsic(ext, obj, val):
    assert not isinstance(obj, value_types), "%s on value %r" % (ext.label,obj)
    assert ext.stack, "Not in extrinsic %s" % (ext.label,)
    map = ext.stack[-1]
    assert obj in map, "%r doesn't have %s extrinsic yet" % (obj, ext.label)
    map[obj] = val
    if len(ext.captures) > 0:
        cap = ext.captures[-1]
        assert obj in cap
        cap[obj] = val

def remove_extrinsic(ext, obj):
    assert not isinstance(obj, value_types), "%s on value %r" % (ext.label,obj)
    assert ext.stack, "Not in extrinsic %s" % (ext.label,)
    map = ext.stack[-1]
    assert obj in map, "%r doesn't have %s extrinsic" % (obj, ext.label)
    del map[obj]
    if len(ext.captures) > 0:
        cap = ext.captures[-1]
        assert obj in cap
        del cap[obj]

def has_extrinsic(ext, obj):
    assert not isinstance(obj, value_types), "%s on value %r" % (ext.label,obj)
    assert ext.stack, "Not in extrinsic %s" % (ext.label,)
    return obj in ext.stack[-1]

Name = new_extrinsic('Name', None, omni=True)
FormSpec = new_extrinsic('FormSpec', None, omni=True)
TrueRepresentation = new_extrinsic('TrueRepresentation', None, omni=True)

value_types = (basestring, bool, int, float, tuple, type(None))

# Forms

Field = DT('Field', ('type', 'Type'))
Ctor = DT('Ctor', ('fields', [Field]))
DTOpts = DT('DTOpts', ('valueType', bool))
DataType = DT('DataType', ('ctors', [Ctor]),
                          ('tvars', ['TypeVar']),
                          ('opts', DTOpts))

del _dt_form

def _ctor_form(ctor):
    fields = []
    for i in xrange(len(ctor.__types__)):
        nm = ctor.__slots__[i]
        t = ctor.__types__[i]
        if _deferred_type_parses is None \
                    and not isinstance(t, (Type, TForward)):
            t = parse_type(t)
        field = Field(t)
        add_extrinsic(Name, field, nm)
        fields.append(field)
    form = Ctor(fields)
    add_extrinsic(Name, form, ctor.__name__)
    add_extrinsic(TrueRepresentation, form, ctor)
    add_extrinsic(FormSpec, ctor, form)
    del ctor.__types__
    if _deferred_type_parses is not None:
        _deferred_type_parses.append(form)
    return form

def _dt_form(dt, tvs):
    if tvs is None:
        tvs = {}
    ctors = in_env(TVARS, tvs,
            lambda: in_env(NEWTYPEVARS, None,
            lambda: map(_ctor_form, dt.ctors)))
    opts = DTOpts(dt._opts.get('value', False))
    del dt._opts
    form = DataType(ctors, tvs.values(), opts)
    add_extrinsic(Name, form, dt.__name__)
    add_extrinsic(TrueRepresentation, form, dt)
    add_extrinsic(FormSpec, dt, form)
    return form

def _restore_forms():
    for ctors in CTORS.itervalues():
        assert len(ctors) == 1 # should be no overloads as of yet
        _dt_form(DATATYPES[ctors[0].__name__], None)
_restore_forms()

# Type representations

TypeVar = DT('TypeVar')

PrimType, PInt, PFloat, PStr, PChar, PBool = ADT('PrimType',
        'PInt', 'PFloat', 'PStr', 'PChar', 'PBool')

FuncMeta = DT('FuncMeta', ('takesEnv', bool))

def plain_meta():
    return FuncMeta(True)
def basic_meta():
    return FuncMeta(False)
def copy_meta(meta):
    return FuncMeta(meta.takesEnv)
def metas_equal(m1, m2):
    return m1.takesEnv == m2.takesEnv

Type, TVar, TPrim, TVoid, \
    TTuple, TFunc, TData, TArray, TWeak \
    = ADT('Type',
        'TVar', ('typeVar', '*TypeVar'),
        'TPrim', ('primType', PrimType),
        'TVoid',
        'TTuple', ('tupleTypes', ['Type']),
        'TFunc', ('paramTypes', ['Type']), ('retType', 'Type'),
                 ('meta', FuncMeta),
        'TData', ('data', '*DataType'), ('appTypes', ['Type']),
        'TArray', ('elemType', 'Type'),
        'TWeak', ('refType', 'Type'))

def TInt():
    return TPrim(PInt())
def TFloat():
    return TPrim(PFloat())
def TBool():
    return TPrim(PBool())
def TStr():
    return TPrim(PStr())
def TChar():
    return TPrim(PChar())

def TPlainFunc(params, ret):
    return TFunc(params, ret, plain_meta())

def parse_new_type(t, tvars):
    return in_env(NEWTYPEVARS, None, lambda:
            in_env(TVARS, tvars, lambda: parse_type(t)))

def vanilla_tdata(form):
    return TData(form, map(TVar, form.tvars))

def parse_type(t):
    if type(t) is type and issubclass(t, Structured):
        form = extrinsic(FormSpec, t)
        if isinstance(form, Ctor):
            form = extrinsic(FormSpec, SUPERS[t])
        return vanilla_tdata(form)
    elif isinstance(t, basestring):
        toks = list(tokenize_type(t))
        try:
            ct = consume_type(toks)
            assert not toks, "%s remaining" % (toks,)
        except AssertionError, e:
            raise AssertionError("%s while parsing %r" % (e, t))
        return ct
    elif t is int:
        return TInt()
    elif t is float:
        return TFloat()
    elif t is str:
        return TStr()
    elif t is bool:
        return TBool()
    elif t is None:
        return TVoid()
    elif isinstance(t, tuple):
        return TTuple(map(parse_type, t))
    elif isinstance(t, list):
        assert len(t) == 1
        return TArray(parse_type(t[0]))
    elif isinstance(t, set):
        assert len(t) == 1
        return _apply_set_type(parse_type(list(t)[0]))
    elif isinstance(t, dict):
        assert len(t) == 1
        [(key, val)] = t.iteritems()
        return _apply_dict_type(parse_type(key), parse_type(val))
    elif t is type or t is object or t is file:
        # MAGIC!
        return t
    assert False, "Unknown type repr of type %r: %r" % (type(t), t)

types_by_name = dict(str=TStr, int=TInt, float=TFloat, bool=TBool, void=TVoid)

def _type_by_name(t):
    if len(t) == 1:
        tvars = env(TVARS)
        tvar = tvars.get(t)
        if tvar is None:
            assert have_env(NEWTYPEVARS), "Tried to create TypeVar %s" % t
            tvar = TypeVar()
            add_extrinsic(Name, tvar, t)
            tvars[t] = tvar
        return TVar(tvar)
    elif t in DATATYPES:
        return vanilla_tdata(extrinsic(FormSpec, DATATYPES[t]))
    elif t in types_by_name:
        return types_by_name[t]()
    else:
        return TForward(t, [])

def consume_type(toks):
    wasParens = False
    tok = toks.pop(0)
    if tok == '*':
        t = TWeak(consume_type(toks))
    elif tok == 't(' or tok == '(':
        # tuple literal
        wasParens = (tok == '(')
        ts = []
        while toks[0] != ')':
            ts.append(consume_type(toks))
            if toks[0] == ',':
                toks.pop(0)
            else:
                assert toks[0] == ')', "Expected comma or ), not " + toks[0]
        toks.pop(0)
        t = TTuple(ts)
    elif tok == '[':
        t = TArray(consume_type(toks))
        assert toks.pop(0) == ']', 'Unbalanced []'
    elif tok[0] in slashW:
        t = _type_by_name(tok)
        if toks and toks[0] == '(':
            # application
            apps = []
            toks.pop(0)
            while toks[0] != ')':
                apps.append(consume_type(toks))
                if toks[0] == ',':
                    toks.pop(0)
                else:
                    assert toks[0]==')', "Expected comma or ), not " + toks[0]
            toks.pop(0)
            assert not t.appTypes or len(t.appTypes)==len(apps),"Bad app count"
            t.appTypes = apps
    else:
        assert False, "Unexpected " + tok
    # might be followed by infix arrow
    if toks and toks[0] == '->':
        toks.pop(0)
        params = t.tupleTypes if wasParens else [t]
        if len(params) == 1 and matches(params[0], 'TVoid()'):
            params = []
        t = TPlainFunc(params, consume_type(toks))
    return t

slashW = 'abcdefghjijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'

def tokenize_type(s):
    word = ''
    lastDash = False
    for i, c in enumerate(s):
        if lastDash:
            assert c == '>', "Broken arrow"
            yield '->'
            lastDash = False
        elif c in slashW:
            word += c
        elif c == '(' and word == 't':
            yield 't('
            word = ''
        else:
            if word:
                yield word
                word = ''
            if c in '*,:(){}[]':
                yield c
            elif c == '-':
                lastDash = True
            elif c != ' ':
                assert False, "Unexpected char in " + s
    assert not lastDash
    if word:
        yield word


TForward = DT('TForward', ('name', str), ('appTypes', [Type]))

def t_DT(dt):
    return vanilla_tdata(extrinsic(FormSpec, SUPERS[dt]))

def _apply_list_type(t):
    listT = parse_type('List')
    return TData(listT, [t])

def _apply_set_type(t):
    setT = parse_type('Set')
    return TData(setT, [t])

def _apply_dict_type(k, v):
    dictT = parse_type('Dict')
    return TData(dictT, [k, v])

# Parse the types in TypeVar, Type fields
def _parse_deferred():
    global _deferred_type_parses
    for ctor in _deferred_type_parses:
        def parse():
            for field in ctor.fields:
                field.type = parse_type(field.type)
        tvars = {}
        in_env(NEWTYPEVARS, None, lambda: in_env(TVARS, tvars, parse))
        SUPERS[type(ctor)].tvars = tvars.values()
    _deferred_type_parses = None
_parse_deferred()

def derive_copied_ctor_type(t, old_dt, new_dt, dtSubsts, tvars):
    substNames = dict((extrinsic(Name, dt), repl)
                      for dt, repl in dtSubsts.iteritems())
    def _derive_tvar(tv):
        if tv not in tvars:
            orig = tv
            tv = TypeVar()
            add_extrinsic(Name, tv, extrinsic(Name, orig))
            tvars[orig] = tv
        else:
            tv = tvars[tv]
        return TVar(tv)
    def _derive_data(dt, ts):
        if dt is old_dt:
            dt = new_dt
        elif dt in dtSubsts:
            dt = dtSubsts[dt]
        return TData(dt, map(copy, ts))
    def copy(t):
        if isinstance(t, TForward):
            nm = t.name
            if nm == old_dt.__name__:
                nm = new_dt.__name__
            elif nm in substNames:
                nm = substNames[dt].__name__
            return TForward(nm, map(copy, t.appTypes))
        return match(t,
            ('TVar(tv)', _derive_tvar),
            ('TPrim(PInt())', TInt),
            ('TPrim(PFloat())', TFloat),
            ('TPrim(PBool())', TBool),
            ('TPrim(PStr())', TStr),
            ('TPrim(PChar())', TChar),
            ('TVoid()', TVoid),
            ('TTuple(ts)', lambda ts: TTuple(map(copy, ts))),
            ('TFunc(args, ret, meta)', lambda args, ret:
                TFunc(map(copy, args), copy(ret), copy_meta(meta))),
            ('TData(data, apps)', _derive_data),
            ('TArray(t)', lambda t: TArray(copy(t))),
            ('TWeak(t)', lambda t: TWeak(copy(t))))
    return copy(t)

# Typeclasses

TypeClassInfo = DT('TypeClassInfo', ('name', str),
                                    ('spec', {str: (int, Type)}),
                                    ('impls', {'*DataType': ['a']}))

def new_typeclass(name, *args):
    spec = {}
    impls = {}
    info = TypeClassInfo(name, spec, impls)
    def make_impl(i, specT, nm):
        # Limitation: First argument :: 'a to do the lookup
        # Really ought to use specT to figure it out
        def lookup(*args):
            assert len(args) == len(specT.paramTypes)
            t = type(args[0])
            if t not in impls:
                t = SUPERS[t]
            tnm = t.__name__
            assert t in impls, "%s is not a part of %s" % (tnm, name)
            func = impls[t][i]
            assert func is not None, "%s.%s.%s has no impl" % (name, tnm, nm)
            return func(*args)
        lookup.__name__ = '_' + nm + '_typeclass_lookup'
        return lookup
    for i, entry in enumerate(args):
        if len(entry) == 3:
            nm, t, default = entry
        else:
            nm, t = entry
            default = None
        assert nm not in spec
        tvars = {}
        t = parse_new_type(t, tvars)
        assert match(t.paramTypes[0], ("TVar(tv)",lambda tv: tv is tvars['a']))
        spec[nm] = (i, t, default)
        setattr(info, nm, make_impl(i, t, nm))
    return info

def impl(cls, targetT):
    def decorator(func):
        fnm = func.__name__
        suffix = '_' + targetT.__name__
        assert fnm.endswith(suffix), "%s impl for %s must be named *%s" % (
                cls.name, targetT, suffix)
        fnm = fnm[:-len(suffix)]
        assert fnm in cls.spec, "Unknown impl method: %s" % (fnm,)
        if targetT not in cls.impls:
            default_impl(cls, targetT)
        i, specT, default = cls.spec[fnm]
        cls.impls[targetT][i] = func
        return None
    return decorator

def default_impl(cls, targetT):
    assert targetT not in cls.impls, "default_impl() would clobber existing"
    vtable = [None] * len(cls.spec)
    for i, t, default in cls.spec.itervalues():
        vtable[i] = default
    cls.impls[targetT] = vtable

# Global options

GenOpts = DT('GenOpts', ('quiet', bool),
                        ('color', None),
                        ('dumpTypes', bool),
                        ('dumpInsts', bool))
GENOPTS = new_env('GENOPTS', GenOpts)

import re
_col_re = re.compile(r'\^(\w+)\^?')
del re
_col_shorts = {'N': 'Normal', 'DG': 'DarkGray'}

def col(c, s):
    colors = have_env(GENOPTS) and env(GENOPTS).color
    if colors:
        c = _col_shorts.get(c, c)
        s = '%s%s%s' % (getattr(colors, c), s, colors.Normal)
    return s

def fmtcol(s, *args):
    colors = have_env(GENOPTS) and env(GENOPTS).color
    if colors:
        def colorize(m):
            c = m.group(1)
            c = _col_shorts.get(c, c)
            return getattr(colors, c)
        s = _col_re.sub(colorize, s)
    else:
        s = _col_re.sub('', s)
    return s.format(*args)

def mark(s):
    return col('Red', s)

# Pretty printing
# (naive quadratic version)

PrettyPrinted = new_extrinsic('PrettyPrinted', None)

def pretty_brief(name, o):
    if name == 'Bind':
        o = o.target
        name = type(o).__name__
        if name == 'Builtin':
            return col('Yellow', extrinsic(Name, o))
        elif name == 'Ctor':
            return fmtcol('^Brown{0}^N', extrinsic(Name, o))
        elif name == 'Var':
            return "'%r" % (o,)
    elif name == 'Lit':
        o = o.literal
        name = type(o).__name__
        if name == 'IntLit':
            return col('Cyan', 'i%d' % (o.val,))
        elif name == 'FloatLit':
            return col('Cyan', 'i%f' % (o.val,))
        elif name == 'StrLit':
            return fmtcol('^Cyan^s{0!r}^N', o.val)
        else:
            assert False
    elif name == 'TPrim' or name == 'CPrim':
        c = 'Cyan' if name == 'TPrim' else 'LightCyan'
        return col(c, repr(o.primType))
    elif name == 'TupleLit':
        return 't%r' % (tuple(o.vals),)
    elif name == 'DataType':
        return col('Brown', extrinsic(Name, o))
    return None

def _id(o):
    return fmtcol('^DG@x{0:x}^N', id(o) % 0xfffff)

def __repr__(o):
    if not in_extrinsic_scope(PrettyPrinted):
        return scope_extrinsic(PrettyPrinted, lambda: repr(o))
    t = type(o)
    name = t.__name__
    if has_extrinsic(PrettyPrinted, o):
        if has_extrinsic(Name, o):
            name = fmtcol('{0} ^Green"{1}"^N', name, extrinsic(Name, o))
        return '<%s %s>' % (name, _id(o))
    add_extrinsic(PrettyPrinted, o, None)

    brief = pretty_brief(name, o)
    if brief is not None:
        return brief
    if has_extrinsic(Name, o):
        name = fmtcol('{0} ^Green"{1}"^N {2}', name, extrinsic(Name,o), _id(o))
    if len(t.__slots__) > 1:
        params = (repr(getattr(o, s)) for s in t.__slots__[:-1])
        comma = col('Blue', ', ')
        name = fmtcol('{0}^Blue(^N{1}^Blue)^N', name, comma.join(params))
    return name

Structured.__repr__ = __repr__

# Type annotations

def annot(t, **opts):
    return lambda func: func

# Matching

named_match_dispatch = {}

def match_try(atom, ast):
    if isinstance(ast, compiler.ast.CallFunc
                ) and isinstance(ast.node, compiler.ast.Name):
        if ast.node.name in CTORS:
            candidates = CTORS[ast.node.name]
            for dt in candidates:
                if atom.__class__ is dt:
                    break
            else:
                return None
            slots = filter(lambda s: s != '_ix', dt.__slots__)
            assert len(ast.args) == len(slots), \
                    "Ctor %s takes %d args: %s" % (ast.node.name,
                            len(slots), ', '.join(slots))
            # Found a matching constructor; now match its args recursively
            # Unlike the main match loop, if any fail here everything fails
            ctor_args = []
            for arg_ast, attrname in ezip(ast.args, slots):
                sub_args = match_try(getattr(atom, attrname), arg_ast)
                if sub_args is None:
                    return None
                ctor_args += sub_args
            return ctor_args
        named_matcher = named_match_dispatch.get(ast.node.name)
        if named_matcher is not None:
            return named_matcher(atom, ast)
        assert False, "Unknown match: %s (%s)" % (ast.node.name, ast.args)
    elif isinstance(ast, compiler.ast.Name):
        if ast.name == 'True':
            assert isinstance(atom, bool)
            return [] if atom else None
        elif ast.name == 'False':
            assert isinstance(atom, bool)
            return None if atom else []
        # Just a simple variable name match; always succeeds
        return [] if ast.name == '_' else [atom]
    elif isinstance(ast, compiler.ast.Const):
        # Literal match
        return [] if ast.value == atom else None
    elif isinstance(ast, (compiler.ast.Tuple, compiler.ast.List)):
        t = tuple if isinstance(ast, compiler.ast.Tuple) else list
        if not isinstance(atom, t) or len(atom) != len(ast.nodes):
            return None
        tuple_args = []
        for a, node in ezip(atom, ast.nodes):
            args = match_try(a, node)
            if args is None:
                return None
            tuple_args += args
        return tuple_args
    elif isinstance(ast, compiler.ast.Or):
        # First that doesn't fail
        for case in ast.nodes:
            or_args = match_try(atom, case)
            if or_args is not None:
                return or_args
        return None
    elif isinstance(ast, compiler.ast.And):
        and_args = []
        for case in ast.nodes:
            case_args = match_try(atom, case)
            if case_args is None:
                return None
            and_args += case_args
        return and_args
    elif isinstance(ast, compiler.ast.Compare) and ast.ops[0][0] == '==':
        # capture right side
        assert isinstance(ast.expr, compiler.ast.Name) and ast.expr.name != '_'
        capture_args = match_try(atom, ast.ops[0][1])
        return [atom] + capture_args if capture_args is not None else None
    assert False, "Unknown match case: %s" % ast

match_asts = {}

def match(atom, *cases):
    # Block form
    if len(cases) == 0:
        return match_blocks(atom)
    elif len(cases) == 1 and isinstance(cases[0], basestring):
        # shortcut for single-case
        m = match_blocks(atom)
        if m(cases[0]):
            m.ret(m.arg if hasattr(m, 'arg') else m.args)
        return m.result()

    # Try all the cases, find the first that doesn't fail
    for (case, f) in cases:
        call_args = match_try(atom, _get_match_case(case))
        if call_args is not None:
            return f(*call_args)
    case_list = ''.join('* %s -> %s\n' % (p, f) for p, f in cases)
    assert False, "Match failed.\nVALUE:\n%r\nCASES:\n%s" % (atom, case_list)

def match_blocks(atom):
    cases = []
    def case(pat):
        cases.append(pat)
        args = match_try(atom, _get_match_case(pat))
        if args is None:
            return False
        if len(args) == 1:
            case.arg = args[0]
        else:
            case.args = args
        return True
    def ret(result):
        case.success = result
    case.ret = ret
    def result():
        if hasattr(case, 'success'):
            return case.success
        else:
            case_list = ''.join('* %s\n' % p for p in cases)
            assert False, "Match failed.\nVALUE:\n%r\nCASES:\n%s" % (atom,
                    case_list)
    case.result = result
    return case

def matches(atom, case):
    return match_try(atom, _get_match_case(case)) is not None

def _get_match_case(case):
    ast = match_asts.get(case)
    if ast is None:
        ast = compiler.parse(case, mode='eval').node
        match_asts[case] = ast
    return ast

# decorator
def matcher(name):
    def takes_func(func):
        named_match_dispatch[name] = func
        return func
    return takes_func

@matcher('contains')
def _match_contains(atom, ast):
    # Do any members of the list match?
    assert len(ast.args) == 1
    assert isinstance(atom, list), "Expected list for 'contains"
    for item in atom:
        item_args = match_try(item, ast.args[0])
        if item_args is not None:
            return item_args
    return None

@matcher('cons')
def _match_cons(atom, ast):
    # Matches args to (head, tail)
    assert len(ast.args) == 2
    assert isinstance(atom, list), "Expected list for 'cons"
    if len(atom):
        car = match_try(atom[0], ast.args[0])
        if car is not None:
            cdr = match_try(atom[1:], ast.args[1])
            if cdr is not None:
                return car + cdr
    return None

@matcher('all')
def _match_all(atom, ast):
    assert len(ast.args) == 2
    assert isinstance(ast.args[0], compiler.ast.Name)
    assert isinstance(atom, list)
    results = []
    all_singular = True
    for i in atom:
        r = match_try(i, ast.args[1])
        if r is not None:
            if len(r) != 1:
                all_singular = False
            results.append(r)
    if ast.args[0].name == '_':
        return []
    return [[r[0] for r in results] if all_singular else results]

@matcher('every')
def _match_every(atom, ast):
    assert len(ast.args) == 2
    assert isinstance(ast.args[0], compiler.ast.Name)
    assert isinstance(atom, list)
    results = []
    all_singular = True
    for i in atom:
        r = match_try(i, ast.args[1])
        if r is None:
            return None
        if len(r) != 1:
            all_singular = False
        results.append(r)
    if ast.args[0].name == '_':
        return []
    return [[r[0] for r in results] if all_singular else results]

def maybe(no, yes, val):
    return match(val, ('Just(j)', yes), ('Nothing()', lambda: no))
def mapMaybe(f, val):
    return match(val, ('Just(j)', lambda j: Just(f(j))),
                      ('Nothing()', Nothing))

def hint(e, **kwargs):
    return e

# Will be replaced by bedrock.List equivalents

def cons(car, cdr):
    return [car] + cdr

def concat(lists):
    return reduce(list.__add__, lists, [])

def concat_map(f, xs):
    result = []
    for x in xs:
        result += f(x)
    return result

def map_(f, xs):
    for x in xs:
        f(x)

orig_zip = zip
zip = None
def ezip(first, second):
    assert len(first) == len(second), "Length mismatch between:\n%s\n%s" % (
            first, second)
    return orig_zip(first, second)

def unzip(list):
    first = []
    second = []
    for (f, s) in list:
        first.append(f)
        second.append(s)
    return (first, second)

def nop():
    pass

def cdecl(name, type):
    return None

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
