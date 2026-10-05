# signature: bug:validation / bug:sszValue
# python: err bug:validation
# lean:   err bug:sszValue

def mk():

    return [Gwei(0), []]

def tr(log, k, v):
    log.append(k)
    return v

def f(a0, log):
    v1 = U64s(data=[])