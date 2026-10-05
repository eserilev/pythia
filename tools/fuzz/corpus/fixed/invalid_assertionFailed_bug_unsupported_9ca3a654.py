# signature: invalid:assertionFailed / bug:unsupported
# python: err invalid:assertionFailed
# lean:   err bug:unsupported

def mk():
    o0 = U64s(data=[Uint64(0), Uint64(0), Uint64(0)])
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

def f(a0: U64s, log):
    v3 = Gwei(0)
    s4 = (set() if True else set([v3]))
    s5 = s4.difference(set([v3]))
    assert False