from base import *
from globs import *
from types_builtin import subst

VAT = new_env('VAT', ['*Extrinsic'])

def clone(src, extrinsics):
    return in_env(VAT, extrinsics, lambda:
            clone_structured(src, t_DT(type(src)).data, []))

def clone_structured(src, data, appTs):
    apps = {}
    if appTs:
        for tv, at in ezip(data.tvars, appTs):
            if isinstance(at, TVar) and at.typeVar is tv:
                continue
            apps[tv] = at
    ctors = data.ctors
    ctor = ctors[src._ctor_ix if len(ctors) > 1 else 0]
    ctor_cls = extrinsic(TrueRepresentation, ctor)
    fs = []
    for field, name in ezip(ctor.fields, ctor_cls.__slots__[:-1]):
        ft = field.type
        if apps:
            ft = subst(apps, ft)
        fs.append(clone_by_type(getattr(src, name), ft))
    o = ctor_cls(*fs)

    for extr in env(VAT):
        if has_extrinsic(extr, src):
            add_extrinsic(extr, o, extrinsic(extr, src))

    return o

def clone_by_type(src, t):
    m = match(t)
    if m('TVar(tv)'):
        assert isinstance(Structured, src), \
                "Can't clone unstructured %r without type info" % (src,)
        return clone_structured(src, t_DT(type(src)).data, [])
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
    elif m('TData(data, types)'):
        data, appTs = m.args
        return clone_structured(src, data, appTs)
    elif m('TArray(et)'):
        assert isinstance(src, list)
        et = m.arg
        return [clone_by_type(s, et) for s in src]
    elif m('TWeak(_)'):
        return src
    else:
        assert False, "Bad type to clone: %r" % (t,)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
