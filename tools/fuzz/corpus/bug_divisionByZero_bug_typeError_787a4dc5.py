# signature: bug:divisionByZero / bug:typeError
# python: err bug:divisionByZero
# lean:   err bug:typeError

def mk():
    o0 = Pt()
    o1 = PPts(data=[o0])
    o2 = Checkpoint(root=Root(bytes([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    o3 = Pt()
    return [o1, o2, o3, []]

def tr(log, k, v):
    log.append(k)
    return v

def f(a0, a1, a2, log):
    v1 = Box()
    v1.i += (True // v1.i)