# signature: bug:validation / bug:other.AttributeError
# python: err bug:validation
# lean:   err bug:other.AttributeError

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
    v1 = v2 = Blob(data=[0, (0 if True else 0), (Gwei(0)).bit_length(), -1])