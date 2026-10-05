# signature: bug:sszValue / bug:unsupported
# python: err bug:sszValue
# lean:   err bug:unsupported

def mk():
    o0 = Epochs(data=[Epoch(0)])
    return [o0, Slot(0), Uint64(0), []]

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

def f(a0, a1, a2, log):
    for x2 in range(3, 0, -1):
        pass
    return Slot(18446744073709551616)

