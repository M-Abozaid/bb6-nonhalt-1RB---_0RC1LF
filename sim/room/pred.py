#!/usr/bin/env python3
"""Closed-form predictor of M7 checkpoint tapes for level w0 (>=17, w0 = 17 mod 5) — see NOTES.md."""
import sys, zlib
def F(x): return 2*x - bin(x).count('1')
TOK={'a':b'10','b':b'100','0':b'0','1':b'1'}
def level(w0):
    """return (X0,Y0,S,Z) for level w0; S = list of (X,Y) older blocks, each 'a (ab)^X (a)^3 b^Y'"""
    X0,Y0,S,Z=2**8-5,7*2**7,[],23683; w=17
    while w<w0:
        A=2**(w-4)
        Z2=Z+1+F(2**w-1)-F(7*A//4+2)+w+2
        Z3=Z2+F(2**(w+1)-1)+w+4
        S=[(X0,Y0)]+S; X0,Y0,Z=A-5,7*A//2,Z3; w+=5
    return X0,Y0,S,Z
def blk(X,Y): return b'10'+b'10100'*X+b'10'*3+b'100'*Y
def Sbytes(S): return b''.join(blk(X,Y) for X,Y in S)
def tail_end(Z): return b'0'+b'1'*Z+b'0'+b'10'+b'100'*28+b'0'+b'1'*741
def counter(w,v): return b''.join(b'1010' if (v>>j)&1 else b'100' for j in range(w))
def state(w0,ep,u):
    X0,Y0,S,Z=level(w0); A=2**(w0-4); H=2**(w0-2)+2**(w0-1); SB=Sbytes(S)
    F0=b'10'+b'10100'*X0+b'10'*3+b'100'*Y0   # 'a (ab)^X0 (a)^3 b^Y0'
    if ep=='E0G':
        assert 1<=u<=A; B=F(u)-1; w,v=w0,H+u
        body=b'0'+b'100'*B+b'1'*(4*A-4-2*B)+b'0'+b'100'+F0+SB+tail_end(Z)
    elif ep=='E0T':
        assert A+1<=u<=4*A-1; w,v=w0,H+u
        body=b'0'+b'100'*(2*A-2)+b'0'+b'1'*(2+F(u)-F(A+1))+b'00'+F0+SB+tail_end(Z)
    elif ep=='E1G':
        assert 0<=u<=7*A//4+1; w,v=w0+1,2**w0+u; B=F(u)
        body=b'0'+b'10100'*(A-2)+b'10'*3+b'100'*B+b'1'*(7*A-1-2*B)+b'00'+F0+SB+tail_end(Z)
    elif ep=='E1T':
        assert 7*A//4+2<=u<=2**w0-1; w,v=w0+1,2**w0+u
        body=b'0'+b'10100'*(A-2)+b'10'*3+b'100'*(7*A//2)+F0+SB+tail_end(Z+1+F(u)-F(7*A//4+2))
    elif ep=='E2':
        assert 0<=u<=2**(w0+1)-1; w,v=w0+2,2**(w0+1)+u
        Z2=Z+1+F(2**w0-1)-F(7*A//4+2)+w0+2
        body=b'0'+b'10'+b'10100'*(A-3)+b'10'*3+b'100'*(7*A//2)+F0+SB+tail_end(Z2+F(u))
    elif ep=='E3':
        assert 1<=u<=2**(w0+2)-1; w,v=w0+3,2**(w0+2)+u
        Z2=Z+1+F(2**w0-1)-F(7*A//4+2)+w0+2; Z3=Z2+F(2**(w0+1)-1)+w0+4
        body=b'00'+b'1'*(F(u)+1)+b'0'+b'100'+b'10'+b'10100'*(A-5)+b'10'*3+b'100'*(7*A//2)+F0+SB+tail_end(Z3)
    elif ep=='E4':
        w,v=w0+4,2**(w0+3)
        Z2=Z+1+F(2**w0-1)-F(7*A//4+2)+w0+2; Z3=Z2+F(2**(w0+1)-1)+w0+4
        body=b'10'+b'1'*(2**(w0+3)-2)+b'0'+b'100'+b'10'+b'10100'*(A-5)+b'10'*3+b'100'*(7*A//2)+F0+SB+tail_end(Z3)
    else: raise ValueError(ep)
    t=b'00000'+counter(w,v)+body
    return t.rstrip(b'0'),w,v
def seq(w0,ep,u,k):
    """predicted (ep,u) for the k checkpoints after (ep,u); None where no formula (transients)"""
    A=2**(w0-4); out=[]; e,x=ep,u
    for _ in range(k):
        x+=1
        if e=='E0G' and x>A: e='E0T'
        if e=='E0T' and x>4*A-1: e,x='E1G',0
        if e=='E1G' and x>7*A//4+1: e='E1T'
        if e=='E1T' and x>2**w0-1: e,x='E2',0
        if e=='E2' and x>2**(w0+1)-1: e,x='E3',0
        if e=='E3' and x>2**(w0+2)-1: e,x='E4',0
        elif e=='E4': e,x='NEXT',1
        out.append((e,x))
    return out
if __name__=='__main__':
    w0=int(sys.argv[1]); ep=sys.argv[2]; u=int(sys.argv[3]); k=int(sys.argv[4]); out=sys.argv[5]
    t,w,v=state(w0,ep,u); open(out,'wb').write(t)
    print('START',ep,u,'w=%d v=%d len=%d crc=%08x'%(w,v,len(t),zlib.crc32(t)))
    for j,(e,x) in enumerate(seq(w0,ep,u,k),1):
        if e=='E3' and x==0: print(j,e,x,'-'); continue
        if e=='NEXT': tt,ww,vv=state(w0+5,'E0G',x)
        else: tt,ww,vv=state(w0,e,x)
        print(j,e,x,'w=%d v=%d len=%d crc=%08x'%(ww,vv,len(tt),zlib.crc32(tt)))
