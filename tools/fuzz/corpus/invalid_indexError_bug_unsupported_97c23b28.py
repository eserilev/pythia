# signature: invalid:indexError / bug:unsupported
# python: err invalid:indexError
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

def f(a0, log):
    for x1 in range(3, 0, -1):
        pass
    a0.ns[0] += 0