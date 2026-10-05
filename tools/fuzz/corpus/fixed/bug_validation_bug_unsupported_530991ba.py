# signature: bug:validation / bug:unsupported
# python: err bug:validation
# lean:   err bug:unsupported

def mk():

    return [Gwei(0), []]

def tr(log, k, v):
    log.append(k)
    return v

def f(a0, log):
    v1 = Box(ps=Gwei(0))