# signature: ok / runner-crash
# python: ok ret=None | a0=#0=Box{p=#1=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#2=Pt{a=Uint64:18446744073709551615,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#3=List[Pt,3][],ns=#4=List[Gwei,3][],es=#5=ProgressiveList[Epoch][],bs=#6=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a1=#7=Checkpoint{epoch=Epoch:0,root=Root:0000000000000000000000000000000000000000000000000000000000000000} | a2=Gwei:0 | a3=#8=list[]
# lean:   runner-crash exit 1

def mk():
    o0 = Pt(a=Uint64(18446744073709551615))
    o1 = Box(q=o0)
    o2 = Checkpoint()
    return [o1, o2, Gwei(0), []]

def tr(log, k, v):
    log.append(k)
    return v

def f(a0, a1, a2, log):
    v1 = U64s(data=[Uint64(0), a0.p.a, (a0.p.a << a0.q.a)])