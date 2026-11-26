// Second, independently written counter for cyclic 312-avoiding permutations.
// Position sweep from the pattern definition: pi(i) is either the largest unused value below the
// current maximum m, or any unused value above m. State after p positions: mask of used values
// above p (path ends B) and bijection f: A-rank -> B-rank, A = unused values <= p (path starts).
// Once the value n has been used every later step is forced, so those states are completed on the spot.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned __int128 u128; typedef unsigned long long u64;
static int n;
static inline u64 enc(const int*g,int h){ u64 r=0; unsigned used=0;
  for(int i=0;i<h;i++){ int x=g[i]; int less=__builtin_popcount(used&((1u<<x)-1)); r=r*(u64)(h-i)+(u64)(x-less); used|=1u<<x;} return r;}
static inline void dec(u64 r,int h,int*g){ int dig[40]; for(int i=h-1;i>=0;i--){ dig[i]=(int)(r%(u64)(h-i)); r/=(u64)(h-i);} unsigned used=0;
  for(int i=0;i<h;i++){ int k=dig[i]; for(int x=0;x<h;x++){ if(!(used>>x&1)){ if(k==0){g[i]=x;used|=1u<<x;break;} k--; } } } }
// apply edge q=p+1 -> y. kind 0: y = A[i]; kind 1: y = value p+o (unused, o>=2).
// returns -1 dead, 1 completed (final closure), 0 ok (state updated in place)
static int step(u64&mask,int*f,int&h,int p,int kind,int arg){
  int q=p+1; bool qinB=mask&1; int s=-1; if(qinB){ for(int a=0;a<h;a++) if(f[a]==0){s=a;break;} }
  if(kind==0){ int i=arg;
    if(qinB){ if(s==i) return (q==n && h==1)?1:-1;
      int nf[40],k=0; for(int a=0;a<h;a++){ if(a==i) continue; int v=(a==s)?f[i]:f[a]; nf[k++]=v-1; } h=k; memcpy(f,nf,sizeof(int)*k); }
    else { int fi=f[i]; int k=0; for(int a=0;a<h;a++){ if(a==i) continue; f[k++]=f[a]; } f[k++]=fi; h=k; }
    mask>>=1; return 0; }
  int o=arg; int rank=__builtin_popcountll(mask&((1ULL<<(o-1))-1));
  if(qinB){ for(int a=0;a<h;a++){ if(a==s) f[a]=rank-1; else { int v=f[a]-1; if(v>=rank-1) v++; f[a]=v; } } }
  else { for(int a=0;a<h;a++) if(f[a]>=rank) f[a]++; f[h]=rank; h++; }
  mask=(mask|(1ULL<<(o-1)))>>1; return 0; }
// forced candidate "largest unused below the maximum": returns kind/arg, or -1 if none
static int below(u64 mask,int h,int&kind,int&arg){ int mo=64-(mask?__builtin_clzll(mask):64);
  for(int o=mo-1;o>=1;o--) if(!(mask>>(o-1)&1)){ kind=1; arg=o; return 0; }
  if(h>0){ kind=0; arg=h-1; return 0; } return -1; }
static u64 tail(u64 mask,const int*f0,int h,int p){ int f[40]; memcpy(f,f0,sizeof(int)*h);
  for(;p<n;p++){ int kind,arg; if(below(mask,h,kind,arg)<0) return 0; if(kind==1 && arg==1) return 0;
    int r=step(mask,f,h,p,kind,arg); if(r<0) return 0; if(r==1) return 1; }
  return 0; }
struct Hh_unused{ size_t operator()(u128 x)const{ u64 a=(u64)x^((u64)(x>>64)*0x9E3779B97F4A7C15ULL); a^=a>>31; a*=0xBF58476D1CE4E5B9ULL; return a^(a>>29);} };
struct HT { vector<u64> k, c; size_t n=0, cap=0;
  void init(size_t cp){ cap=1; while(cap*7<cp*10) cap<<=1; k.assign(cap,0); c.assign(cap,0); n=0; }
  void clear(){ vector<u64>().swap(k); vector<u64>().swap(c); n=cap=0; }
  static inline size_t hs(u64 a){ a^=a>>31; a*=0xBF58476D1CE4E5B9ULL; a^=a>>29; a*=0x94D049BB133111EBULL; return a^(a>>32); }
  void grow(){ vector<u64> ok,oc; ok.swap(k); oc.swap(c); size_t o=cap; init(cap*2); for(size_t i=0;i<o;i++) if(ok[i]) add1(ok[i],oc[i]); }
  inline void add1(u64 kk,u64 v){ size_t m=cap-1,i=hs(kk)&m; while(k[i]){ if(k[i]==kk){c[i]+=v;return;} i=(i+1)&m; } k[i]=kk; c[i]=v; n++; }
  void add(u64 key,u64 v){ if(cap==0) init(1024); if((n+1)*10>cap*8) grow(); add1(key+1,v); } };
static u64 fact[40];
int main(int argc,char**argv){ n=atoi(argv[1]); fact[0]=1; for(int i=1;i<40;i++) fact[i]=fact[i-1]*i; HT C,N; C.add(0,1); u64 total=0; size_t mx=0;
  for(int p=0;p<n;p++){ mx=max(mx,C.n); N.clear(); N.init(C.n+C.n/4+1024);
    for(size_t ii=0;ii<C.cap;ii++){ if(!C.k[ii]) continue; u64 key=C.k[ii]-1; u64 c=C.c[ii]; int h0=0; u64 mask0; { /* key = mask*h!+lehmer, h=popcount(mask) unknown: store h in low 5 bits */ h0=(int)(key&31); u64 r=key>>5; mask0=r/fact[h0]; } int f0[40]; dec((key>>5)%fact[h0],h0,f0);
      int mo=64-(mask0?__builtin_clzll(mask0):64);
      auto go=[&](int kind,int arg,bool isn){ u64 mask=mask0; int h=h0; int f[40]; memcpy(f,f0,sizeof(int)*h0);
        if(kind==1 && arg==1) return; int r=step(mask,f,h,p,kind,arg); if(r<0) return; if(r==1){ total+=c; return; }
        if(isn){ total+=c*tail(mask,f,h,p+1); return; }
        N.add(((mask*fact[h]+enc(f,h))<<5)|(u64)h,c); };
      int kind,arg; if(below(mask0,h0,kind,arg)==0) go(kind,arg,false);
      for(int o=max(mo,0)+1;o<=n-p;o++) go(1,o,o==n-p);
    }
    C.clear(); swap(C,N); }
  printf("n=%d c312p=%llu maxlayer=%zu\n",n,total,mx); return 0; }
