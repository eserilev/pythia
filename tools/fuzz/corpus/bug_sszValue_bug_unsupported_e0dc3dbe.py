# signature: bug:sszValue / bug:unsupported
# python: err bug:sszValue
# lean:   err bug:unsupported

def mk():
    o0 = Gweis(data=[Gwei(0), Gwei(0)])
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

def f(a0: Gweis, log):
    a0[0:1] = [a0[0], a0[0]]
    s6 = set()
    s7 = s6.difference(set([(Slot(0) + Slot(0))]))
    a0.append(Gwei(0))