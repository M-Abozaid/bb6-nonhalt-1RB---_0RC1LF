#!/usr/bin/env python3
"""Token-level replay of m7 (1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF) checkpoints.
Checkpoint c: head D at lo=-(2c-1), tape = 0^5 C S.  C = counter (LSB first; 1=1010, 0=100).
S = '0' W M  (normal)  or  '10' M  (PEND, right after an empty-W overflow).
W = token runs (a=10, b=100, ab=10100); M = medium (static cells right of W), runs over {0,1,a,b,ab}.
Rules (see NOTES.md):
  INC   : non-overflow: bits+1 with f=t+1 flips (t trailing ones); then f TRIPs.
  TRIP  : absorb maximal greedy tokens (b before a) from M into W; then M=11.. -> W+=b (G) else M=0.. -> 01.. (T).
  OVF   : bits all ones -> bits=0^w1 and S-prefix rewrite (O0,O1,O2,O3); trail length by conservation (+2 cells/ckpt).
  PEND  : after O0: bits -> 1 0^(w-1) 1 1 ; S '10' 1^n X -> '0' 1^(n-2) X (W empty).
"""
import sys
RAW={'0':'0','1':'1','a':'10','b':'100','ab':'10100'}
class Unknown(Exception): pass

class St:
    def __init__(s,bits,W,M,pend=False):
        s.bits=list(bits); s.W=[list(x) for x in W]; s.M=[list(x) for x in reversed(M)]; s.pend=pend
        s.stats={}; s.log=[]
    # ---------------- medium (reversed list, front = last)
    def mpush(s,tok,cnt=1):
        if cnt<=0: return
        if s.M and s.M[-1][0]==tok: s.M[-1][1]+=cnt
        else: s.M.append([tok,cnt])
    def mpeek(s,k):
        out=[];i=len(s.M)-1;n=0
        while n<k:
            if i<0: out.append('0'*(k-n)); break
            t,c=s.M[i]; r=RAW[t]; m=min(c,(k-n)//len(r)+1); out.append(r*m); n+=len(r)*m; i-=1
        return ''.join(out)[:k]
    def mpop(s,k):
        while k>0:
            if not s.M: return
            t,c=s.M[-1]; r=RAW[t]
            if len(r)==1:
                d=min(k,c); s.M[-1][1]-=d; k-=d
                if s.M[-1][1]==0: s.M.pop()
                continue
            s.M[-1][1]-=1
            if s.M[-1][1]==0: s.M.pop()
            if len(r)<=k: k-=len(r); continue
            for ch in reversed(r[k:]): s.mpush(ch)
            return
    def mpush_front_str(s,toks):   # toks: list of (tok,cnt) in front-to-back order
        for t,c in reversed(toks): s.mpush(t,c)
    # ---------------- W
    def wpush(s,tok,cnt=1):
        if cnt<=0: return
        if s.W and s.W[-1][0]==tok: s.W[-1][1]+=cnt
        else: s.W.append([tok,cnt])
    def wflat(s,limit):
        out=[]
        for t,c in s.W:
            for _ in range(c):
                out.extend(['a','b'] if t=='ab' else [t])
                if len(out)>=limit: return out[:limit]
        return out
    def wlen(s): return sum((2 if t=='ab' else 1)*c for t,c in s.W)
    def wdrop(s,n):
        W=s.W
        while n>0:
            t,c=W[0]; u=2 if t=='ab' else 1
            if u*c<=n: n-=u*c; W.pop(0); continue
            q=n//u; W[0][1]-=q; n-=q*u
            if n:   # split one 'ab' after its 'a'
                W[0][1]-=1
                if W[0][1]==0: W.pop(0)
                W.insert(0,['b',1]); n=0
    def wprepend(s,toks):
        for t in reversed(toks):
            if s.W and s.W[0][0]==t: s.W[0][1]+=1
            else: s.W.insert(0,[t,1])
    def lead_ab(s,skip):
        """after skipping `skip` flat tokens: (#leading ab pairs, next 3 flat tokens) using runs only"""
        segs=[]
        for t,c in s.W:
            if t=='ab': segs.append(['ab',c])
            elif segs and segs[-1][0]==t: segs[-1][1]+=c
            else: segs.append([t,c])
        # skip flat tokens
        i=0
        while skip>0:
            t,c=segs[i]; u=2 if t=='ab' else 1
            if u*c<=skip: skip-=u*c; i+=1; continue
            q=skip//u; segs[i][1]-=q; skip-=q*u
            if skip: segs[i][1]-=1; segs.insert(i+1,['b',1]); 
            if segs[i][1]==0: i+=1
            if skip: skip=0
        segs=[list(x) for x in segs[i:] if x[1]>0]
        k=0; exp='a'; j=0; left=[]
        while j<len(segs):
            t,c=segs[j]
            if exp=='a' and t=='ab': k+=c; j+=1; continue
            if exp=='a' and t=='a' and c==1: exp='b'; j+=1; continue
            if exp=='b' and t=='b':
                k+=1; exp='a'
                if c>1: left=[['b',c-1]]+segs[j+1:]; break
                j+=1; continue
            left=segs[j:]; break
        if exp=='b': left=[['a',1]]+left
        nxt=[]
        for t,c in left:
            for _ in range(min(c,3)): nxt.extend(['a','b'] if t=='ab' else [t])
            if len(nxt)>=3: break
        return k,nxt[:3]
    # ---------------- rules
    def trip(s):
        while True:
            if s.M and s.M[-1][0] in ('a','b','ab') and s.M[-1][1]>=2:
                t,c=s.M[-1]; s.wpush(t,c-1); s.M[-1][1]=1; continue
            f=s.mpeek(3)
            if f=='100': s.mpop(3); s.wpush('b'); s.cnt('absorb'); continue
            if f[:2]=='10': s.mpop(2); s.wpush('a'); s.cnt('absorb'); continue
            break
        if s.mpeek(2)=='11': s.mpop(2); s.wpush('b'); s.cnt('G')
        else: s.mpop(1); s.mpush('1'); s.mpush('0'); s.cnt('T')
    def cnt(s,k): s.stats[k]=s.stats.get(k,0)+1
    def trail_front_ones(s):   # index (in reversed list) of first '1' run in medium front region
        for i in range(len(s.M)-1,-1,-1):
            if s.M[i][0]=='1' and s.M[i][1]>=2: return i
        raise Unknown('no trail')
    def prefix_len(s):   # cells from lo to start of the (first long) trail run
        i=s.trail_front_ones()
        L=5+len(s.Cstr())+(2 if s.pend else 1+len(s.Wstr()))
        for j in range(len(s.M)-1,i,-1): L+=len(RAW[s.M[j][0]])*s.M[j][1]
        return L,i
    def step(s):
        w=len(s.bits)
        if s.pend:
            assert s.bits==[0]*(w-1)+[1]
            L0,i0=s.prefix_len()
            s.bits=[1]+[0]*(w-2)+[1,1]; s.pend=False; s.W=[]
            s.mpop(2); s.cnt('PEND'); s.log.append('PEND w->%d'%len(s.bits)); return
        if all(s.bits): return s.overflow()
        t=0
        while s.bits[t]: s.bits[t]=0; t+=1
        s.bits[t]=1
        for _ in range(t+1): s.trip()
    def overflow(s):
        w=len(s.bits)
        L0,i0=s.prefix_len(); n0=s.M[i0][1]
        front=s.mpeek(2)
        fl=s.wflat(8)
        kind=None
        if not s.W and front=='01':
            kind='O0'; s.mpop(1); s.pend=True
        elif len(s.W)==1 and s.W[0][0]=='b' and s.W[0][1]>=2 and front=='01':
            j=s.W[0][1]; s.W=[]; k=(j+1)//2-1
            if k: s.W.append(['ab',k])
            s.W.append(['a',3]); s.mpop(1); kind='O1'
        elif fl[:5]==list('ababa') and front=='01':
            # (ab)^k a^3 Y, k>=2 -> a a b (ab)^(k-2) a^3 Y  (= delete first b)
            k,nxt=s.lead_ab(0)
            if not (k>=2 and nxt[:3]==['a','a','a']): raise Unknown('O2 shape')
            s.wdrop(2); s.wprepend(['a']); kind='O2'
        elif fl[:3]==list('aab') and front=='01':
            k,nxt=s.lead_ab(3); Z=s.wflat(12)[3:]
            if k>=2 and nxt[:3]==['a','a','a']:
                s.wdrop(5); s.wprepend(['a'])        # W := del-first-b(Z) = a (ab)^(k-1) a^3 Y
                newM=[('0',1),('a',1),('b',1)]
            elif Z[:4]==['a','a','a','b']:
                s.wdrop(7); s.wprepend(['a','a'])    # Z=a^3 b Z' -> 0 a a Z'
                newM=[('0',1),('a',1),('b',1),('0',1)]
            else: raise Unknown('O3 shape '+''.join(Z[:12]))
            # everything of W becomes fossil: M = 0 a b [0] Wrest ; W empty
            fos=[(t,c) for t,c in s.W]; s.W=[]
            s.mpush_front_str(newM+fos)
            kind='O3'
        else:
            raise Unknown('overflow W=%s front=%s'%(''.join(s.wflat(20)),front))
        s.bits=[0]*w+[1]
        L1,i1=s.prefix_len()
        s.M[i1][1]+=2+L0-L1
        s.cnt(kind); s.log.append('%s w=%d'%(kind,w))
    # ---------------- strings
    def Wstr(s): return ''.join(RAW[t]*c for t,c in s.W)
    def Mstr(s): return ''.join(RAW[t]*c for t,c in reversed(s.M))
    def Cstr(s): return ''.join('1010' if b else '100' for b in s.bits)
    def tape(s):
        body='00000'+s.Cstr()
        if s.pend: return body+'10'+s.Mstr()
        return body+'0'+s.Wstr()+s.Mstr()

def parse(tape):
    """initial state from a normal checkpoint tape (W = maximal greedy tokens after sep)."""
    assert tape.startswith('00000'); i=5; bits=[]
    while True:
        if tape.startswith('1010',i): bits.append(1); i+=4
        elif tape.startswith('100',i): bits.append(0); i+=3
        else: break
    assert tape[i]=='0'; i+=1
    W=[]
    while True:
        if tape.startswith('100',i): tok='b'; i+=3
        elif tape.startswith('10',i): tok='a'; i+=2
        else: break
        if W and W[-1][0]==tok: W[-1][1]+=1
        else: W.append([tok,1])
    M=[]
    for ch in tape[i:].rstrip('0'):
        if M and M[-1][0]==ch: M[-1][1]+=1
        else: M.append([ch,1])
    return St(bits,W,M)
