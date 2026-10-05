# signature: bug:other.AttributeError / bug:unsupported
# python: err bug:other.AttributeError
# lean:   err bug:unsupported

def mk():
    o0 = Pt()
    o1 = [o0]
    return [o1, []]

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

def f(a0: list, log):
    a0[0] = Bytes32(b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00')
    a0[0].a += 0