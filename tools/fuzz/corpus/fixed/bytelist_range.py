# signature: bug:valueError (hand-written bytelist_range)
# python: err bug:valueError
# lean:   err bug:valueError

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
    a0.bl[0:1] = [7, 8]
    a0.bl[0] = 256
