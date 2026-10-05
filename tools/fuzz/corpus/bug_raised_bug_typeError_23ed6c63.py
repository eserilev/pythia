# signature: bug:raised / bug:typeError
# python: err bug:raised
# lean:   err bug:typeError

def mk():
    o0 = Flags(data=[Boolean(False), Boolean(False), Boolean(False), Boolean(False)])
    o1 = Box(i=ValidatorIndex(0), k=Uint8(0))
    return [o0, o1, []]

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

def f(a0: Flags, a1: Box, log):
    a0[0] = (Gwei(0) + Gwei(0))
    if True:
        raise FuzzError()