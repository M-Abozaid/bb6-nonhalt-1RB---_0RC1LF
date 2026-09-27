#include "../tm.h"
// dump checkpoints c in [c0,c1] every K: "c t lo hi tape(lo..hi)"
int main(int argc,char**argv){
  long long c0=atoll(argv[1]),c1=atoll(argv[2]),K=argc>3?atoll(argv[3]):1;
  long SZ=1L<<28; unsigned char*tp=calloc(SZ,1); long p=SZ/2, lo=p, hi=p; int s=0; long long cnt=0;
  for(long long t=0;;t++){
    int r=tp[p]; int ns=N_[s][r]; if(ns<0){printf("HALT %lld\n",t);return 0;}
    tp[p]=W_[s][r]; p+=D_[s][r]; s=ns; if(p>hi)hi=p;
    if(p<lo){lo=p; if(s==3){ ++cnt; if(cnt>c1) return 0; if(cnt>=c0 && (cnt-c0)%K==0){
      printf("%lld %lld %ld %ld ",cnt,t+1,lo-SZ/2,hi-SZ/2);
      for(long q=lo;q<=hi;q++)putchar(48+tp[q]); putchar('\n');}}}
  }
}
