# signature: invalid:assertionFailed / bug:typeError
# python: err invalid:assertionFailed
# lean:   err bug:typeError

def mk():
    o0 = Pt()
    o1 = Pt()
    o2 = PtPair(data=[o0, o1])
    o3 = Box()
    o4 = Epochs(data=[Epoch(0)])
    return [o2, o3, o4, []]

def tr(log, k, v):
    log.append(k)
    return v

def f(a0, a1, a2, log):
    if (True if (True == Gwei(0)) else True):
        assert False