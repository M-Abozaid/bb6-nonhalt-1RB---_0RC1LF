#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <zlib.h>
#include "../tm.h"
// exact run from checkpoint-form tape file (head at cell 0, state D) for K checkpoints; print w,v,len,crc per checkpoint
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"rb"); int K=atoi(argv[2]); fseek(f,0,SEEK_END); long n=ftell(f); fseek(f,0,SEEK_SET);
  long SZ=n+ (n/2) + (1L<<22); long base=(1L<<21); unsigned char*tp=calloc(SZ,1); unsigned char*buf=malloc(n);
  if(fread(buf,1,n,f)!=(size_t)n) return 1; for(long i=0;i<n;i++) tp[base+i]=buf[i]-'0'; free(buf);
  long p=base,lo=p,hi=base+n-1; int s=3; int ck=0; long long t=0; unsigned char*ob=malloc(SZ);
  while(ck<K){
    int r=tp[p]; int ns=N_[s][r]; if(ns<0){printf("HALT t=%lld\n",t);return 0;}
    tp[p]=W_[s][r]; p+=D_[s][r]; s=ns; t++; if(p>hi)hi=p; if(p<16||p>SZ-16){printf("OOB\n");return 1;}
    if(p<lo){lo=p; if(s==3){ ck++;
      long e=hi; while(e>lo&&tp[e]==0)e--; long L=e-lo+1;
      for(long i=0;i<L;i++) ob[i]='0'+tp[lo+i];
      long i=lo+5; int w=0; unsigned long long v=0;
      while(tp[i]==1){ if(tp[i+1]==0&&tp[i+2]==1&&tp[i+3]==0){v|=1ull<<w;i+=4;} else if(tp[i+1]==0&&tp[i+2]==0){i+=3;} else break; w++;}
      printf("%d w=%d v=%llu len=%ld crc=%08lx t=%lld\n",ck,w,v,L,crc32(0,ob,L),t); fflush(stdout);
      if(getenv("DUMPAT")&&atoi(getenv("DUMPAT"))==ck){FILE*g=fopen("dump.bin","wb");fwrite(ob,1,L,g);fclose(g);} }}
  }
}
