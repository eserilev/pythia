# signature: bug:validation / bug:typeError
# python: err bug:validation
# lean:   err bug:typeError

def mk():
    o0 = Pt()
    o1 = Pts(data=[o0])
    return [o1, []]

def tr(log, k, v):
    log.append(k)
    return v

def f(a0, log):
    v2 = (PBox() if (True == Gwei(0)) else PBox(pair=Box()))