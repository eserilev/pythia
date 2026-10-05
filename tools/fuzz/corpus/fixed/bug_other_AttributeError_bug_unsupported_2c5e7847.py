# signature: bug:other.AttributeError / bug:unsupported
# python: err bug:other.AttributeError
# lean:   err bug:unsupported

def mk():
    o0 = Box()
    return [o0, []]

def tr(log, k, v):
    log.append(k)
    return v


def grow(xs, v):
    if len(xs) < 5:
        xs.append(v)
    return v


def each(xs, fn):
    for x in xs:
        fn(x)

def f(a0: Box, log):
    v1 = [len(ssz_serialize(0))]