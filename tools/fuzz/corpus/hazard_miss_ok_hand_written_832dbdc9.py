# signature: hazard-miss ok (hand-written)
# python: ok ret=#0=Box{p=#1=Pt{a=Uint64:1,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#3=List[Pt,3][],ns=#4=List[Gwei,3][],es=#5=ProgressiveList[Epoch][],bs=#6=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a0=#1 | a1=#7=list[]
# lean:   ok ret=#0=Box{p=#1=Pt{a=Uint64:1,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#3=List[Pt,3][],ns=#4=List[Gwei,3][],es=#5=ProgressiveList[Epoch][],bs=#6=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a0=#1 | a1=#7=list[]
# copy-on-store model: ok ret=Box{p=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=List[Pt,3][],ns=List[Gwei,3][],es=ProgressiveList[Epoch][],bs=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a0=Pt{a=Uint64:1,s=Slot:0,f=Boolean:False,r=Bytes4:00000000} | a1=list[]

def mk():
    return [Pt(), []]


def f(a0: Pt, log):
    v1 = Box(p=a0)
    a0.a = Uint64(1)
    return v1
