# signature: ok / bug:unsupported
# python: ok ret=None | a0=#0=Box{p=#1=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#3=List[Pt,3][],ns=#4=List[Gwei,3][],es=#5=ProgressiveList[Epoch][],bs=#6=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a1=#7=Box{p=#8=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#9=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#10=List[Pt,3][],ns=#11=List[Gwei,3][],es=#12=ProgressiveList[Epoch][],bs=#13=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a2=#14=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000} | a3=#15=list[#16=list[Root:0000000000000000000000000000000000000000000000000000000000000000,Root:0101010101010101010101010101010101010101010101010101010101010101]]
# lean:   err bug:unsupported

def mk():
    o0 = Box()
    o1 = Box()
    o2 = Pt()
    return [o0, o1, o2, []]

def tr(log, k, v):
    log.append(k)
    return v


def grow(xs, v):
    if len(xs) < 5:
        xs.append(v)
    return v


def each(xs, fn):
    for x in xs:
        fn(x)

def g1(log, p0: Box, p1: Slot):
    return Root(b'\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01')


def f(a0: Box, a1: Box, a2: Pt, log):
    s6 = set([Root(b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00')])
    s7 = s6.union(set([g1(log, Box(), a0.p.s)]))
    log.append(sorted(s7))