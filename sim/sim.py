import sys
M="1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF"
T={}
for i,g in enumerate(M.split('_')):
    for r in range(2):
        s=g[3*r:3*r+3]
        T[(i,r)]=None if s=='---' else (int(s[0]),1 if s[1]=='R' else -1,ord(s[2])-65)
def run(n, tape=None, pos=0, st=0, cb=None):
    tape = tape if tape is not None else {}
    for t in range(n):
        r=tape.get(pos,0); tr=T[(st,r)]
        if tr is None: return ('halt',t,tape,pos,st)
        if cb: cb(t,tape,pos,st)
        w,d,ns=tr; tape[pos]=w; pos+=d; st=ns
    return ('run',n,tape,pos,st)
def show(tape,pos,st):
    ks=[k for k,v in tape.items() if v]; lo=min(ks+[pos]); hi=max(ks+[pos])
    s=''
    for i in range(lo,hi+1):
        c=str(tape.get(i,0))
        s+= ('['+'ABCDEF'[st]+c+']') if i==pos else c
    return s
