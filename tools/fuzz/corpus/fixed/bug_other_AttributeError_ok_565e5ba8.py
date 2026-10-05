# signature: bug:other.AttributeError / ok
# python: err bug:other.AttributeError
# lean:   ok ret=None | a0=#0=list[Uint8:0] | a1=#1=list[]

def mk():
    o0 = []
    return [o0, []]

def tr(log, k, v):
    log.append(k)
    return v

def f(a0, log):
    if len(a0) < 5:
        a0.append(Uint8(0))
    v1 = sorted(a0, key=lambda x: x.a)