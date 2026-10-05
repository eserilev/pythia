# signature: bug:other.AttributeError / ok (hand-written)
# python: err bug:other.AttributeError
# lean:   ok ret=None | a0=#0=Box{p=#1=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#3=List[Pt,3][],ns=#4=List[Gwei,3][Gwei:1],es=#5=ProgressiveList[Epoch][],bs=#6=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a1=#7=list[]

def mk():
    return [Box(), []]


def f(a0, log):
    a0.ns.extend([Gwei(1)])
