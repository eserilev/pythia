# signature: invalid:indexError / bug:sszValue
# python: err invalid:indexError
# lean:   err bug:sszValue

def mk():
    o0 = Gweis(data=[Gwei(0)])
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
    for x1 in a0:
        v2 = PBox()
        d3 = {Slot(0): v2.pp[0], Slot(18446744073709551616): v2.pp[0]}