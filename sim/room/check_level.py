#!/usr/bin/env python3
# exact-sim windows from closed-form predicted tapes; compare every checkpoint crc with prediction
import sys, subprocess, random, zlib, os
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from pred import state, seq
w0=int(sys.argv[1]); tmp=sys.argv[2]; random.seed(w0)
A=2**(w0-4)
W=[('E0G',1,6),('E0G',A-3,8),('E0G',random.randint(2,A-4),3),('E0T',random.randint(A+2,4*A-6),3),('E0T',4*A-4,8),
   ('E1G',random.randint(1,7*A//4-4),3),('E1G',7*A//4-3,8),('E1T',random.randint(7*A//4+3,2**w0-6),3),('E1T',2**w0-4,8),
   ('E2',random.randint(1,2**(w0+1)-6),3),('E2',2**(w0+1)-4,8),('E3',random.randint(1,2**(w0+2)-6),3),('E3',2**(w0+2)-4,8)]
if len(sys.argv)>3: W=[W[int(i)] for i in sys.argv[3].split(',')]
tot=bad=0
for ep,u,k in W:
    fn=os.path.join(tmp,'w%d_%s_%d.bin'%(w0,ep,u)); t,w,v=state(w0,ep,u); open(fn,'wb').write(t)
    out=subprocess.run(['./exwin',fn,str(k)],capture_output=True,text=True).stdout.split('\n'); os.remove(fn)
    res=[]
    for j,(e,x) in enumerate(seq(w0,ep,u,k)):
        line=out[j] if j<len(out) else 'MISSING'
        if e=='E3' and x==0: res.append('E3@0:skip'); continue
        tt,ww,vv=state(w0+5,'E0G',x) if e=='NEXT' else state(w0,e,x)
        exp='w=%d v=%d len=%d crc=%08x'%(ww,vv,len(tt),zlib.crc32(tt))
        ok = exp in line; tot+=1; bad+= (not ok)
        res.append('%s@%d:%s'%(e,x,'OK' if ok else 'MISMATCH exp[%s] got[%s]'%(exp,line)))
    print('w0=%d window %s u=%d len=%d ->'%(w0,ep,u,len(t)),' '.join(res),flush=True)
print('w0=%d SUMMARY checked=%d mismatches=%d'%(w0,tot,bad))
