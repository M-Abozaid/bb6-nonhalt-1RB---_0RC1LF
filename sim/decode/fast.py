#!/usr/bin/env python3
"""Epoch-accelerated replay (same rules as replay.py). Translate epochs and growth runs are jumped with
trips(v->v') = F(v')-F(v), F(v)=2v-popcount(v). Contacts/overflows are stepped exactly with replay.St.step."""
import sys,subprocess
from replay import *
def F(v): return 2*v-bin(v).count('1')
def val(bits): return sum(b<<i for i,b in enumerate(bits))
def setval(st,v):
    w=len(st.bits); st.bits=[(v>>i)&1 for i in range(w)]
class Fast:
    def __init__(s,st,c): s.st=st; s.c=c
    def mode(s):
        f=s.st.mpeek(3)
        if s.st.pend: return 'P'
        if f[:2]=='11': return 'G'
        if f[:2]=='01' and s.st.M[-2][0]=='1' if len(s.st.M)>=2 else False: return 'T'
        return '?'
    def run(s,cmax,hook=None):
        st=s.st
        while s.c<cmax:
            w=len(st.bits); v=val(st.bits); top=(1<<w)-1
            m=s.mode()
            if m=='T' and v<top:
                tgt=min(top, v+(cmax-s.c))
                tr=F(tgt)-F(v); st.M[-2][1]+=tr; setval(st,tgt); s.c+=tgt-v; st.stats['T']=st.stats.get('T',0)+tr
                continue
            if m=='G' and v<top:
                n=st.M[-1][1]; budget=n//2-1   # keep >=2 ones spare so every jumped trip is a plain G
                lo_,hi_=v,min(top,v+(cmax-s.c))
                while lo_<hi_:
                    mid=(lo_+hi_+1)//2
                    if F(mid)-F(v)<=budget: lo_=mid
                    else: hi_=mid-1
                if lo_>v:
                    tr=F(lo_)-F(v); st.M[-1][1]-=2*tr; st.wpush('b',tr); setval(st,lo_); s.c+=lo_-v
                    st.stats['G']=st.stats.get('G',0)+tr; continue
            nl=len(st.log); st.step(); s.c+=1
            if hook and len(st.log)>nl: hook(s)
if __name__=='__main__':
    c0=16; tape=subprocess.run(['./ckd',str(c0),str(c0)],capture_output=True,text=True).stdout.split()[4]
    fs=Fast(parse(tape),c0); fs.run(int(sys.argv[1])); print(fs.c, fs.st.stats, fs.st.log)
