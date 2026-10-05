# signature: bug:typeError / bug:unsupported
# python: err bug:typeError
# lean:   err bug:unsupported

def mk():
    o0 = Pt()
    o1 = Pt()
    o2 = PtPair(data=[o0, o1])
    return [o2, []]

def tr(log, k, v):
    log.append(k)
    return v

def f(a0, log):
    a0[0] = a0[0].f