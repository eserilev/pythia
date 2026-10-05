# signature: ok-ok /int
# python: ok ret=None | a0=#0=list[Gwei:0,Gwei:1,Gwei:0] | a1=#1=list[int:1,int:1]
# lean:   ok ret=None | a0=#0=list[Gwei:0,Gwei:1,Gwei:0] | a1=#1=list[int:1,int:1,int:1]

def mk():
    o0 = [Gwei(0), Gwei(1), Gwei(0)]
    return [o0, []]

def tr(log, k, v):
    log.append(k)
    return v


def grow(xs, v):
    if len(xs) < 5:
        xs.append(v)
    return v

def f(a0, log):
    assert any(tr(log, 1, x) > 0 for x in a0)