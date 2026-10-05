# signature: ok / bug:other.AttributeError
# python: ok ret=None | a0=#0=List[Pt,3][#1=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}] | a1=#2=list[int:0] | a2=#3=Box{p=#4=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#5=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#6=List[Pt,3][],ns=#7=List[Gwei,3][],es=#8=ProgressiveList[Epoch][],bs=#9=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a3=#10=list[]
# lean:   err bug:other.AttributeError

def mk():
    o0 = Pt()
    o1 = Pts(data=[o0])
    o2 = []
    o3 = Box()
    return [o1, o2, o3, []]

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

def f(a0: Pts, a1: list, a2: Box, log):
    a1[0:1] = [(a2.k).bit_length()]