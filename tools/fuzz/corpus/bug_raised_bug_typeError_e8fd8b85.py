# signature: bug:raised / bug:typeError
# python: err bug:raised
# lean:   err bug:typeError

def mk():
    o0 = Box()
    return [o0, []]

def tr(log, k, v):
    log.append(k)
    return v

def f(a0, log):
    if (not (True == Gwei(0))):
        raise FuzzError()