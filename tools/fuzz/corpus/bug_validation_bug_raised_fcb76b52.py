# signature: bug:validation / bug:raised
# python: err bug:validation
# lean:   err bug:raised

def mk():
    o0 = Box()
    return [o0, Gwei(0), o0, []]

def tr(log, k, v):
    log.append(k)
    return v

def g1(log, p0):
    if True:
        raise FuzzError()
def f(a0, a1, a2, log):
    v2 = Box(bs=[])
    return g1(log, a0)

