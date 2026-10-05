# signature: bug:sszValue / ok
# python: err bug:sszValue
# lean:   ok ret=None | a0=#0=ProgressiveList[Pt][#1=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#3=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#4=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}] | a1=#5=Box{p=#6=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#7=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#8=List[Pt,3][#9=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#9],ns=#10=List[Gwei,3][],es=#11=ProgressiveList[Epoch][],bs=#12=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a2=#13=list[]

def mk():
    o0 = Pt()
    o1 = Pt()
    o2 = Pt()
    o3 = Pt()
    o4 = PPts(data=[o0, o1, o2, o3])
    o5 = Pt()
    o6 = Pts(data=[o5])
    o7 = Box(ps=o6)
    return [o4, o7, []]

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

def f(a0, a1, log):
    v2 = [grow(a1.ps, x) for x in a1.ps]