// exact TM sim from blank tape; at every checkpoint (D at new leftmost cell) print "c t lo hi H"
// H = sum_{tape[x]=1} R^(x+OFF) mod 2^61-1 (x absolute, start cell 0). Also snapshot full tape at checkpoints listed in SNAP file.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
static const u64 P=(1ULL<<61)-1;
static inline u64 mulm(u64 a,u64 b){u128 z=(u128)a*b; u64 lo=(u64)(z&P), hi=(u64)(z>>61); u64 s=lo+hi; if(s>=P)s-=P; return s;}
static const int W_[6][2]={{1,0},{0,1},{1,1},{1,0},{0,1},{0,0}};
static const int D_[6][2]={{1,0},{1,-1},{-1,-1},{1,1},{1,1},{-1,-1}};
static const int N_[6][2]={{1,-1},{2,5},{2,3},{4,0},{3,5},{3,5}};
#define OFF 8000000L
int main(int argc,char**argv){
  long long cmax=atoll(argv[1]); u64 R=0x1234567ULL*1000003ULL%P;
  long SZ=2*OFF+100; unsigned char*tp=calloc(SZ,1); u64*pw=malloc(sizeof(u64)*SZ);
  pw[0]=1; for(long i=1;i<SZ;i++) pw[i]=mulm(pw[i-1],R);
  long long *snap=0; int ns_=0; if(argc>2){FILE*f=fopen(argv[2],"r"); snap=malloc(8*100000); while(fscanf(f,"%lld",&snap[ns_])==1) ns_++; fclose(f);}
  long p=OFF, lo=p, hi=p; int s=0; long long cnt=0; u64 H=0; int si=0;
  for(long long t=0;;t++){
    int r=tp[p]; int nx=N_[s][r]; if(nx<0){printf("HALT %lld\n",t);return 0;}
    int w=W_[s][r]; if(w!=r){ tp[p]=w; H = w? (H+pw[p]>=P?H+pw[p]-P:H+pw[p]) : (H>=pw[p]?H-pw[p]:H+P-pw[p]); }
    p+=D_[s][r]; s=nx; if(p>hi)hi=p;
    if(p<lo){ lo=p; if(p<10){printf("OOB\n");return 1;} if(s==3){ ++cnt;
        printf("%lld %lld %ld %ld %llu\n",cnt,t+1,lo-OFF,hi-OFF,(unsigned long long)H);
        if(si<ns_ && snap[si]==cnt){ char fn[64]; sprintf(fn,"snap/c%lld.txt",cnt); FILE*f=fopen(fn,"w"); fprintf(f,"%lld %ld ",cnt,lo-OFF); for(long q=lo;q<=hi;q++) fputc('0'+tp[q],f); fputc('\n',f); fclose(f); si++; }
        if(cnt>=cmax){ fflush(stdout); return 0;} }}
  }
}
