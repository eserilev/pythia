# signature: ok-ok label/label (hand-written)
# python: ok ret=(#0=list[#1=Pt{a=Uint64:1,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}]) | a0=#2=list[#1] | a1=#3=list[]
# lean:   ok ret=(#0=list[#1=Pt{a=Uint64:1,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}]) | a0=#2=list[#3=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}] | a1=#4=list[]

def mk():
    return [[Pt()], []]


def f(a0, log):
    v1 = a0.copy()
    v1[0].a = 1
    return (v1,)
