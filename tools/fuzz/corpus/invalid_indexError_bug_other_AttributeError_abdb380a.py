# signature: invalid:indexError / bug:other.AttributeError
# python: err invalid:indexError
# lean:   err bug:other.AttributeError

def mk():
    o0 = []
    o1 = Flags(data=[Boolean(False), Boolean(False), Boolean(False), Boolean(False)])
    return [Gwei(0), o0, o1, []]

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

def f(a0: Gwei, a1: list, a2: Flags, log):
    a1[0].a = Uint64((Gwei(0)).bit_length())