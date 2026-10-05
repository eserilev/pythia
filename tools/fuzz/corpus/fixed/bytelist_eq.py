# signature: bug:typeError (hand-written bytelist_eq)
# python: err bug:typeError
# lean:   err bug:typeError

def mk():
    o0 = Misc(bl=Blob(data=[1, 2, 3]))
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

def f(a0: Misc, log):
    b = a0.bl
    assert (Gweis() == b) == False
    return b == [1, 2, 3]
