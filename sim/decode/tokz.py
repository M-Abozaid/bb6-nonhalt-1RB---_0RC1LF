import sys,re
# tokenize checkpoint tape: returns (prefix_ok, bits(LSB first), token list of rest)
def tokens(s):
    assert s.startswith('00000'),s[:10]
    i=5;bits=''
    while True:
        if s.startswith('1010',i): bits+='1';i+=4
        elif s.startswith('100',i): bits+='0';i+=3
        else: break
    rest=s[i:]
    toks=[]
    for m in re.finditer(r'1{2,}|100|10|0|1',rest):
        g=m.group()
        if len(g)>=2 and set(g)=={'1'}: toks.append(('1',len(g)))
        else: toks.append(g)
    return bits,toks
def tokname(t):
    if isinstance(t,tuple): return '1^%d'%t[1]
    return {'10':'a','100':'b','0':'0','1':'1'}[t]
def rle(names):
    out=[];i=0;n=len(names)
    while i<n:
        best=(1,1)
        for L in range(1,5):
            if i+L>n: break
            pat=names[i:i+L]; k=1
            while names[i+k*L:i+(k+1)*L]==pat: k+=1
            if k>=3 and k*L>best[0]*best[1]: best=(L,k)
        L,k=best
        if k>=3: out.append('('+' '.join(names[i:i+L])+')^%d'%k); i+=L*k
        else: out.append(names[i]); i+=1
    return out
def shape(x): return re.sub(r'\^\d+','^n',' '.join(x))
if __name__=='__main__':
    mode=sys.argv[1] if len(sys.argv)>1 else 'all'
    prev=None;pl=None
    for line in sys.stdin:
        if not line[0].isdigit() or int(line.split()[0])<6: continue
        f=line.split(); c=int(f[0]); s=f[4]
        bits,toks=tokens(s)
        r=rle([tokname(t) for t in toks])
        sh=shape(r)
        if mode=='all' or sh!=prev:
            if mode!='all' and pl: print('   ',pl)
            print('%7d w=%2d %s | %s'%(c,len(bits),bits,' '.join(r)))
            pl=None
        else: pl='%7d w=%2d %s | %s'%(c,len(bits),bits,' '.join(r))
        prev=sh
