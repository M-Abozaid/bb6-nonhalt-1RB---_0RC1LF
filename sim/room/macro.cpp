// Macro (block K=30) + chain-rule accelerated simulator for M7, with exact checkpoint detection.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <unordered_map>
#include <string>
using namespace std;
static const int W_[6][2]={{1,0},{0,1},{1,1},{1,0},{0,1},{0,0}};
static const int D_[6][2]={{1,0},{1,-1},{-1,-1},{1,1},{1,1},{-1,-1}};
static const int N_[6][2]={{1,-1},{2,5},{2,3},{4,0},{3,5},{3,5}};
const int K=30;
struct Run{uint32_t b; uint64_t n;};
vector<Run> Ls,Rs; // top = back, nearest head
typedef unsigned __int128 u128;
u128 T=0; long long hb=0; // head block absolute index (block being entered)
long long minpos=0; // min visited cell (absolute)
long long cnt=0;
struct Tr{uint32_t y; uint8_t q, exitR; uint32_t steps; bool halt;};
unordered_map<uint64_t,Tr> cache;
static inline void push(vector<Run>&S,uint32_t b,uint64_t n){ if(!n)return; if(!S.empty()&&S.back().b==b) S.back().n+=n; else S.push_back({b,n}); }
static inline uint32_t pop(vector<Run>&S){ if(S.empty()) return 0; uint32_t b=S.back().b; if(--S.back().n==0) S.pop_back(); return b; }
Tr sim(int q,int fromR,uint32_t x){
  int p=fromR?K-1:0; uint32_t steps=0;
  while(p>=0&&p<K){ int r=(x>>p)&1; int ns=N_[q][r]; if(ns<0) return {x,(uint8_t)q,(uint8_t)p,steps,true};
    if(W_[q][r]) x|=1u<<p; else x&=~(1u<<p); p+=D_[q][r]; q=ns; if(++steps>100000){fprintf(stderr,"loop\n");exit(2);} }
  return {x,(uint8_t)q,(uint8_t)(p>=K),steps,false};
}
int lastw=-1; long long lastbig=-1; long long every=0; vector<pair<long long,long long>> win;
bool inwin(long long c){for(auto&w:win) if(c>=w.first&&c<=w.second) return true; return false;}

void expand(vector<uint8_t>&v, const uint32_t cur, int from, size_t limit){ // cells right of head
  v.clear(); for(int i=from;i<K;i++) v.push_back((cur>>i)&1);
  for(long long k=(long long)Rs.size()-1;k>=0&&v.size()<limit;k--){ uint64_t n=Rs[k].n; for(uint64_t j=0;j<n&&v.size()<limit;j++) for(int i=0;i<K;i++) v.push_back((Rs[k].b>>i)&1);} }
void tokenize(const vector<uint8_t>&tp, size_t i, string &out){
  size_t hi=tp.size(); while(hi>0&&tp[hi-1]==0) hi--; 
  vector<char> tk; vector<long> tv; char buf[64];
  while(i<hi){
    if(tp[i]==1){ size_t j=i; while(j<hi&&tp[j]==1)j++;
      if(j-i>=4){tk.push_back('N');tv.push_back(j-i);i=j;continue;}
      if(j-i==1&&i+2<hi+3&&tp[i+1]==0&&(i+2<hi?tp[i+2]==0:true)){tk.push_back('b');tv.push_back(0);i+=3;continue;}
      if(j-i==1){tk.push_back('a');tv.push_back(0);i+=2;continue;}
      for(size_t q=i;q<j;q++){tk.push_back('1');tv.push_back(0);} i=j; continue;}
    tk.push_back('0');tv.push_back(0);i++; }
  size_t n=tk.size(),k=0;
  while(k<n){ int bL=0; long bR=0;
    for(int L=1;L<=3;L++){ if(k+L>n)break; bool ok=true; for(int q=0;q<L;q++) if(tk[k+q]=='N') ok=false; if(!ok)continue;
      long R=1; while(k+(R+1)*L<=n && !memcmp(&tk[k],&tk[k+R*L],L)) R++;
      if(R>=3&&R*L>bR*bL){bL=L;bR=R;} }
    if(bL){ out+="("; out.append(&tk[k],bL); snprintf(buf,64,")^%ld ",bR); out+=buf; k+=bL*bR; }
    else if(tk[k]=='N'){ snprintf(buf,64,"1^%ld ",tv[k]); out+=buf; k++; }
    else { out+=tk[k]; out+=' '; k++; } }
}
void checkpoint(uint32_t cur,int p){ // head at cell p of current block, state D, leftmost
  cnt++;
  vector<uint8_t> v; expand(v,cur,p,400);
  size_t i=5; int nb=0; char bits[256]; unsigned long long val=0;
  while(i+3<v.size()&&v[i]==1){ if(v[i+1]==0&&v[i+2]==1&&v[i+3]==0){bits[nb]='1';val|=1ull<<nb;i+=4;} else if(v[i+1]==0&&v[i+2]==0){bits[nb]='0';i+=3;} else break; nb++; }
  bits[nb]=0;
  long long big=0; for(auto&r:Rs) if(r.n>=4) big++;
  if(nb!=lastw || big!=lastbig || (every&&cnt%every==0)||inwin(cnt)){
    // full expansion
    vector<uint8_t> f; expand(f,cur,p,(size_t)-1);
    string tok; tokenize(f,i,tok);
    unsigned long long tl=(unsigned long long)(T%10000000000000000000ull), th=(unsigned long long)(T/10000000000000000000ull);
    printf("c=%lld t=",cnt); if(th) printf("%llu%019llu",th,tl); else printf("%llu",tl);
    printf(" w=%d v=%llu room=%llu %s | %s\n",nb,val,(nb<64?(1ull<<nb):0)-val,bits,tok.c_str()); fflush(stdout);
    lastw=nb; lastbig=big; }
}
int main(int argc,char**argv){
  long long cmax=atoll(argv[1]); if(argc>2) every=atoll(argv[2]); for(int a=3;a+1<argc;a+=2) win.push_back({atoll(argv[a]),atoll(argv[a+1])});
  int q=0; int dirR=1; // facing right entering block hb from left
  // start: head at cell 0 in state A; treat as entering block 0 from left (cell 0)
  hb=0; minpos=0;
  while(cnt<cmax){
    uint32_t x = dirR? pop(Rs): pop(Ls);
    long long base=hb*K;
    if(base < minpos){ // frontier block: micro-sim with checkpoint detection
      int p=dirR?0:K-1;
      if(base+p<minpos){ minpos=base+p; if(q==3) checkpoint(x,p);}
      while(p>=0&&p<K){ int r=(x>>p)&1; int ns=N_[q][r]; if(ns<0){printf("HALT c=%lld\n",cnt);return 0;}
        if(W_[q][r]) x|=1u<<p; else x&=~(1u<<p); p+=D_[q][r]; q=ns; T++;
        if(p>=0&&p<K&&base+p<minpos){ minpos=base+p; if(q==3) checkpoint(x,p);} }
      if(p>=K){ push(Ls,x,1); hb++; dirR=1; } else { push(Rs,x,1); hb--; dirR=0; }
      continue; }
    uint64_t key=((uint64_t)q<<32)|((uint64_t)(!dirR)<<31)|x;
    auto it=cache.find(key); Tr tr;
    if(it==cache.end()){ tr=sim(q,!dirR,x); cache[key]=tr; } else tr=it->second;
    if(tr.halt){printf("HALT c=%lld\n",cnt);return 0;}
    uint64_t n=1;
    // chain: pass through same direction, same state, next block in facing stack identical
    vector<Run>&F = dirR?Rs:Ls;
    if(tr.q==q && (bool)tr.exitR==(bool)dirR && !F.empty() && F.back().b==x){ n+=F.back().n; F.pop_back(); }
    T += (u128)tr.steps*n;
    if(tr.exitR){ push(Ls,tr.y,n); hb+=n; dirR=1; } else { push(Rs,tr.y,n); hb-=n; dirR=0; }
    q=tr.q;
  }
  fprintf(stderr,"cache=%zu\n",cache.size());
}
