# signature: ok / bug:unsupported
# python: ok ret=None | a0=#0=List[Gwei,3][Gwei:0] | a1=#1=List[Pt,3][#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#3=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#4=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}] | a2=#5=list[]
# lean:   err bug:unsupported

def mk():
    o0 = Gweis(data=[Gwei(0)])
    o1 = Pt()
    o2 = Pt()
    o3 = Pt()
    o4 = Pts(data=[o1, o2, o3])
    return [o0, o4, []]

def tr(log, k, v):
    log.append(k)
    return v


def f(a0, a1, log):
    for x2 in range(3, 0, -1):
        pass