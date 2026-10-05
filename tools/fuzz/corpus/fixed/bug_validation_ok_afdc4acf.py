# signature: bug:validation / ok
# python: err bug:validation
# lean:   ok ret=None | a0=#0=Box{p=#1=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#3=List[Pt,3][],ns=#4=List[Gwei,3][],es=#5=ProgressiveList[Epoch][],bs=#6=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a1=#7=list[]

def mk():
    o0 = Box()
    return [o0, []]

def tr(log, k, v):
    log.append(k)
    return v

def f(a0, log):
    v1 = Box(bs=[])