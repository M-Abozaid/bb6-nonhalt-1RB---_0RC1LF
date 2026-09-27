# cross-validate fast vs step replay: compare full state at checkpoints in list
import subprocess,random
from replay import *; from fast import *
c0=16; tape=subprocess.run(['./ckd',str(c0),str(c0)],capture_output=True,text=True).stdout.split()[4]
a=parse(tape); b=Fast(parse(tape),c0)
random.seed(1); pts=sorted(set(random.sample(range(17,1000000),300))|{430,942,943,1198,1199,1966,2416,6062,14254,30638,30639,38830,38831,63406,77744,77745,194478,456622,980910,980911,999999})
c=c0; bad=0
for p in pts:
    while c<p: a.step(); c+=1
    b.run(p)
    def norm(st):
        W=[]; 
        for t,k in st.W:
            for x in (['a','b'] if t=='ab' else [t]):
                pass
        return (tuple(st.bits),st.pend,st.tape().rstrip('0') if len(st.tape())<5e6 else None)
    if (a.bits,a.pend,a.Wstr(),a.Mstr())!=(b.st.bits,b.st.pend,b.st.Wstr(),b.st.Mstr()): print('DIFF at',p); bad+=1; break
print('xval points',len(pts),'bad',bad, 'last',p)
