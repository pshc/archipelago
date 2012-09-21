from base import *
from globs import *
from types_builtin import subst

# Sure could use graphs here!

VatContents = DT('VatContents', ('copiedExtrinsics', ['*Extrinsic']),
                                ('replacements', {'a': 'a'}))

VAT = new_env('VAT', VatContents)

Original = new_extrinsic('Original', 'a')

def set_orig(clone, orig):
    # Don't need to recurse since there's only one level of clones
    if has_extrinsic(Original, orig):
        orig = extrinsic(Original, orig)
    add_extrinsic(Original, clone, orig)

def orig_loc(obj):
    # Ugh, I don't like the conditional check...
    if has_extrinsic(Original, obj):
        obj = extrinsic(Original, obj)
    return extrinsic(Location, obj)

def in_vat(func):
    return in_env(VAT, VatContents([], {}), func)

# Clone structured data, recording information about its clone in the vat
def clone(src, extrinsics):
    env(VAT).copiedExtrinsics = extrinsics
    return clone_structured(src)

def clone_structured(src, apps=None):
    ctor = instance_ctor(src)
    fs = []
    for field in ctor.fields:
        fnm = extrinsic(Name, field)
        ft = field.type
        if apps:
            ft = subst(apps, ft)
        fs.append(clone_by_type(getattr(src, fnm), ft))
    ctor_cls = extrinsic(TrueRepresentation, ctor)
    o = ctor_cls(*fs)

    vat = env(VAT)
    for extr in vat.copiedExtrinsics:
        if has_extrinsic(extr, src):
            add_extrinsic(extr, o, extrinsic(extr, src))

    if in_extrinsic_scope(Original):
        set_orig(o, src)
    vat.replacements[src] = o

    return o

def clone_by_type(src, t):
    m = match(t)
    if m('TVar(tv)'):
        assert isinstance(Structured, src), \
                "Can't clone unstructured %r without type info" % (src,)
        return clone_structured(src)
    elif m('TPrim(_)'):
        return src
    elif m('TVoid()'):
        assert False, "No void values!"
    elif m('TTuple(tts)'):
        tts = m.arg
        assert isinstance(src, tuple)
        return tuple(clone_by_type(v, tt) for v, tt in ezip(src, tts))
    elif m('TFunc(_, _)'):
        return src
    elif m('TData(data, appTs)'):
        data, appTs = m.args
        assert isinstance(src, extrinsic(TrueRepresentation, data)), \
                "Expected %s, got: %r" % (data, obj)
        apps = appTs and type_app_list_to_map(data.tvars, appTs)
        return clone_structured(src, apps)
    elif m('TArray(et)'):
        et = m.arg
        assert isinstance(src, list)
        return [clone_by_type(s, et) for s in src]
    elif m('TWeak(_)'):
        return src
    else:
        assert False, "Bad type to clone: %r" % (t,)

def instance_ctor(obj):
    ctors = t_DT(type(obj)).data.ctors
    return ctors[obj._ctor_ix if len(ctors) > 1 else 0]

def type_app_list_to_map(tvars, appTs):
    apps = {}
    for tv, at in ezip(tvars, appTs):
        if isinstance(at, TVar) and at.typeVar is tv:
            continue
        apps[tv] = at
    return apps

# Update an object's weak references to point at new clones from this vat
def rewrite(obj):
    return rewrite_by_type(obj, t_DT(type(obj)))

def rewrite_by_type(obj, t):
    m = match(t)
    if m('TVar(tv)'):
        assert isinstance(Structured, obj), \
                "Can't rewrite unstructured %r without type info" % (obj,)
        rewrite_by_type(obj, t_DT(type(obj)))
    elif m('TPrim(_)'):
        pass
    elif m('TVoid()'):
        assert False, "No void values!"
    elif m('TTuple(tts)'):
        tts = m.arg
        assert isinstance(obj, tuple)
        for v, tt in ezip(obj, tts):
            assert not isinstance(tt, TWeak), "TODO"
            rewrite_by_type(v, tt)
    elif m('TFunc(_, _)'):
        pass
    elif m('TData(data, appTs)'):
        data, appTs = m.args
        assert isinstance(obj, extrinsic(TrueRepresentation, data))
        apps = appTs and type_app_list_to_map(data.tvars, appTs)
        ctor = instance_ctor(obj)
        repls = env(VAT).replacements
        for field in ctor.fields:
            fnm = extrinsic(Name, field)
            ft = field.type
            if apps:
                ft = subst(apps, ft)
            val = getattr(obj, fnm)
            if isinstance(ft, TWeak):
                if val in repls:
                    setattr(obj, fnm, repls[val])
            else:
                rewrite_by_type(val, ft)
    elif m('TArray(et)'):
        et = m.arg
        assert isinstance(obj, list)
        if isinstance(et, TWeak):
            repls = env(VAT).replacements
            for i, w in enumerate(obj):
                if w in repls:
                    obj[i] = repls[w]
        else:
            for s in obj:
                rewrite_by_type(s, et)
    elif m('TWeak(_)'):
        assert False, "Shouldn't get here (should be rewritten in other cases)"
    else:
        assert False, "Bad type to rewrite: %r" % (t,)

# AST visitor&mutator (not really vat)

# Env+class is redundant; could just put this all in the class.
# But this is plumbing anyway
VISIT = new_env('VISIT', None)

def visit(visitor, obj, t):
    inst = visitor()
    inst.obj = inst.t = inst.fts = None
    in_env(VISIT, inst, lambda: visit_by_type(obj, t))

class Visitor(object):
    def visit(self, *path):
        obj, t = self.obj, self.t
        for field in path:
            if isinstance(field, int):
                assert isinstance(t, TArray), "Can't index %s" % (t,)
                obj = obj[field]
                t = t.elemType
                continue
            assert field in self.fts, \
                    "%s is not a field {%s}" % (field, ', '.join(self.fts))
            t = self.fts[field]

            # Catch some stupidity
            if len(path) == 1:
                assert t is not None, "Already visited this field!"
                self.fts[field] = None

            assert not isinstance(t, TWeak), \
                    "%s is weak and won't be visited" % (field,)
            obj = getattr(obj, field)
        return visit_by_type(obj, t, bool(path))

def visit_by_type(obj, t, customVisitors=True):
    m = match(t)
    if m('TVar(_) or TPrim(_) or TFunc(_, _)'):
        pass
    elif m('TTuple(tts)'):
        tts = m.arg
        assert isinstance(obj, tuple)
        for v, tt in ezip(obj, tts):
            visit_by_type(v, tt)
    elif m('TData(data, appTs)'):
        data, appTs = m.args
        assert isinstance(obj, extrinsic(TrueRepresentation, data)), \
                "Expected %s, got %s" % (data, obj)
        apps = appTs and type_app_list_to_map(data.tvars, appTs)
        visitor = env(VISIT)

        ctor = extrinsic(FormSpec, type(obj))
        fts = dict((extrinsic(Name, f), subst(apps,f.type) if apps else f.type)
                   for f in ctor.fields)

        if customVisitors:
            ctorNm = extrinsic(Name, ctor)
            if hasattr(visitor, ctorNm):
                # Scope field types for recursive visiting
                old = visitor.obj, visitor.t, visitor.fts
                visitor.obj, visitor.t, visitor.fts = obj, t, fts
                getattr(visitor, ctorNm)(obj)
                visitor.obj, visitor.t, visitor.fts = old
                return

        # Default to recursive visits
        for field in ctor.fields:
            fnm = extrinsic(Name, field)
            ft = fts[fnm]
            if not isinstance(ft, TWeak):
                visit_by_type(getattr(obj, fnm), ft)
    elif m('TArray(et)'):
        et = m.arg
        assert isinstance(obj, list)
        if not isinstance(et, TWeak):
            for o in obj:
                visit_by_type(o, et)
    elif m('TWeak(_)'):
        pass
    elif m('TVoid()'):
        assert False, "No void values!"
    else:
        assert False, "Bad type to visit: %r" % (t,)

MUTATE = new_env('MUTATE', None)

def mutate(mutator, obj):
    inst = mutator()
    return in_env(MUTATE, inst, lambda: inst.mutate(obj))

class Mutator(object):
    def mutate(self, obj):
        return mutate_by_type(obj, t_DT(type(obj)))
    def defaultMutate(self, obj):
        return mutate_by_type(obj, t_DT(type(obj)), False)

def mutate_by_type(obj, t, customMutators=True):
    m = match(t)
    if m('TVar(_) or TPrim(_) or TFunc(_, _)'):
        return obj
    elif m('TTuple(tts)'):
        tts = m.arg
        assert isinstance(obj, tuple)
        return tuple(rewrite_by_type(v, tt) for v, tt in ezip(obj, tts))
    elif m('TData(data, appTs)'):
        data, appTs = m.args
        assert isinstance(obj, extrinsic(TrueRepresentation, data)), \
                "Expected %s, got: %r" % (data, obj)
        mutator = env(MUTATE)
        ctor = extrinsic(FormSpec, type(obj))
        if customMutators:
            ctorNm = extrinsic(Name, ctor)
            if hasattr(mutator, ctorNm):
                return getattr(mutator, ctorNm)(obj)
        # Default to recursive mutation
        apps = appTs and type_app_list_to_map(data.tvars, appTs)
        for field in ctor.fields:
            fnm = extrinsic(Name, field)
            ft = field.type
            if apps:
                ft = subst(apps, ft)
            if not isinstance(ft, TWeak):
                val = getattr(obj, fnm)
                setattr(obj, fnm, mutate_by_type(val, ft))
        return obj
    elif m('TArray(et)'):
        et = m.arg
        assert isinstance(obj, list)
        if isinstance(et, TWeak):
            return obj
        return [mutate_by_type(o, et) for o in obj]
    elif m('TWeak(_)'):
        return obj
    elif m('TVoid()'):
        assert False, "No void values!"
    else:
        assert False, "Bad type to mutate: %r" % (t,)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent: