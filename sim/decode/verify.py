#!/usr/bin/env python3
"""Verify replay against hsim hashes. usage: verify.py hsimfile c_start c_end [every_print]"""
import sys,time
from replay import *
P=(1<<61)-1; R=0x1234567*1000003%P; OFF=8000000
HP={}; INV={}
for t,r in RAW.items():
    HP[t]=sum(pow(R,i,P) for i,ch in enumerate(r) if ch=='1')%P
    INV[len(r)]=pow((pow(R,len(r),P)-1)%P,P-2,P)
def hrun(t,k,x):   # hash of RAW[t]*k starting at absolute x
    L=len(RAW[t])
    return HP[t]*pow(R,x+OFF,P)%P*((pow(R,L*k,P)-1)%P)%P*INV[L]%P
def H(st,c):
    x=-(2*c-1)+5; h=0
    for b in st.bits:
        t='ab' if False else None
        if b: h+=HP['a']*pow(R,x+OFF,P)*(1+pow(R,2,P)); x+=4
        else: h+=HP['b']*pow(R,x+OFF,P); x+=3
    if st.pend: h+=HP['a']*pow(R,x+OFF,P); x+=2
    else:
        x+=1
        for t,k in st.W: h+=hrun(t,k,x); x+=len(RAW[t])*k
    for t,k in reversed(st.M): h+=hrun(t,k,x); x+=len(RAW[t])*k
    return h%P
if __name__=='__main__':
    fn=sys.argv[1]; c0=int(sys.argv[2]); c1=int(sys.argv[3]); pe=int(sys.argv[4]) if len(sys.argv)>4 else 100000
    import subprocess
    tape=subprocess.run(['./ckd',str(c0),str(c0)],capture_output=True,text=True).stdout.split()[4]
    st=parse(tape); c=c0
    f=open(fn); ok=0; t0=time.time()
    for line in f:
        a=line.split()
        if len(a)<5: break
        cc=int(a[0])
        if cc<=c0: continue
        if cc>c1: break
        try: st.step()
        except Unknown as e: print('UNKNOWN at',cc,e); sys.exit(1)
        c=cc
        if H(st,c)!=int(a[4]):
            print('MISMATCH at',c,st.log[-3:]); sys.exit(1)
        ok+=1
        if c%pe==0: print('ok through',c,'w=%d |W|runs=%d |M|runs=%d'%(len(st.bits),len(st.W),len(st.M)),'%.0fs'%(time.time()-t0),flush=True)
    print('VERIFIED %d consecutive checkpoints %d..%d'%(ok,c0+1,c)); print(st.stats); print(st.log)
