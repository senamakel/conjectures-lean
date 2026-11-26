// Count cyclic 321-avoiding permutations of [n], exact. Position sweep: pi(i) is either the
// smallest unused value or a new left-to-right maximum. State: mask of used values above the
// current position (B), and bijection f: A-rank -> B-rank, A = unused values <= p (path starts).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned __int128 u128; typedef unsigned long long u64;
static inline u128 enc(const int*g,int h){ u128 r=0; unsigned used=0;
  for(int i=0;i<h;i++){ int x=g[i]; int less=__builtin_popcount(used&((1u<<x)-1)); r=r*(u128)(h-i)+(u128)(x-less); used|=1u<<x;} return r;}
static inline void dec(u128 r,int h,int*g){ int dig[40]; for(int i=h-1;i>=0;i--){ dig[i]=(int)(r%(u128)(h-i)); r/=(u128)(h-i);} unsigned used=0;
  for(int i=0;i<h;i++){ int k=dig[i]; for(int x=0;x<h;x++){ if(!(used>>x&1)){ if(k==0){g[i]=x;used|=1u<<x;break;} k--; } } } }
struct HT_old { vector<u128> k; vector<u64> c; vector<char> o; size_t n=0, cap=0;
  void init(size_t cp){ cap=1; while(cap<cp*2) cap<<=1; k.assign(cap,0); c.assign(cap,0); o.assign(cap,0); n=0;}
  void clear(){ vector<u128>().swap(k); vector<u64>().swap(c); vector<char>().swap(o); n=cap=0;}
  static inline size_t h(u128 x){ u64 a=(u64)x, b=(u64)(x>>64); a^=b*0x9E3779B97F4A7C15ULL; a^=a>>29; a*=0xBF58476D1CE4E5B9ULL; a^=a>>32; return a;}
  void grow(){ vector<u128> ok; vector<u64> oc; vector<char> oo; ok.swap(k); oc.swap(c); oo.swap(o); size_t oc2=cap; init(cap); for(size_t i=0;i<oc2;i++) if(oo[i]) add(ok[i],oc[i]); }
  void add(u128 key,u64 v){ if(cap==0) init(1024); if((n+1)*10>cap*7) grow(); size_t m=cap-1, i=h(key)&m; while(o[i]){ if(k[i]==key){c[i]+=v;return;} i=(i+1)&m;} o[i]=1;k[i]=key;c[i]=v;n++; }
};
struct HT { vector<u64> k, c; size_t n=0, cap=0;
  void init(size_t cp){ cap=1; while(cap*7<cp*10) cap<<=1; k.assign(cap,0); c.assign(cap,0); n=0; }
  void clear(){ vector<u64>().swap(k); vector<u64>().swap(c); n=cap=0; }
  static inline size_t hs(u64 a){ a^=a>>31; a*=0xBF58476D1CE4E5B9ULL; a^=a>>29; a*=0x94D049BB133111EBULL; return a^(a>>32); }
  void grow(){ vector<u64> ok,oc; ok.swap(k); oc.swap(c); size_t o=cap; init(cap*2); for(size_t i=0;i<o;i++) if(ok[i]) add1(ok[i],oc[i]); }
  inline void add1(u64 kk,u64 v){ size_t m=cap-1,i=hs(kk)&m; while(k[i]){ if(k[i]==kk){c[i]+=v;return;} i=(i+1)&m; } k[i]=kk; c[i]=v; n++; }
  void add(u64 key,u64 v){ if(cap==0) init(1024); if((n+1)*10>cap*8) grow(); add1(key+1,v); } };
static u64 fact[40];
// key = ((mask*h!+lehmer)<<5)|h  (h<=20 so lehmer < 2^62)
int main(int argc,char**argv){ int n=atoi(argv[1]); fact[0]=1; for(int i=1;i<40;i++) fact[i]=fact[i-1]*i;
  HT cur, nxt; cur.add(0,1); u64 total=0; size_t maxl=0; int f[40], nf[40];
  for(int p=0;p<n;p++){ int q=p+1; maxl=max(maxl,cur.n); nxt.init(cur.n+cur.n/4+1024);
    for(size_t i=0;i<cur.cap;i++) if(cur.k[i]){ u64 c=cur.c[i]; u64 key=cur.k[i]-1; int h=(int)(key&31); u64 mask=(key>>5)/fact[h];
      dec((key>>5)%fact[h],h,f); int moff=64-(mask?__builtin_clzll(mask):64);
      if(mask&1){ int s=0; while(f[s]!=0) s++;
        if(s==0){ if(q==n && h==1) total+=c; }
        else { for(int a=1;a<h;a++) nf[a-1]=f[a]-1; nf[s-1]=f[0]-1; nxt.add((((mask>>1)*fact[h-1]+(u64)enc(nf,h-1))<<5)|(u64)(h-1),c); }
        for(int w=moff+1; w<=n-p; w++){ u64 nm=(mask|(1ULL<<(w-1)))>>1; for(int a=0;a<h;a++) nf[a]=f[a]-1; nf[s]=h-1; nxt.add(((nm*fact[h]+(u64)enc(nf,h))<<5)|(u64)(h),c); }
      } else {
        if(h>0){ int fu=f[0]; for(int a=1;a<h;a++) nf[a-1]=f[a]; nf[h-1]=fu; nxt.add((((mask>>1)*fact[h]+(u64)enc(nf,h))<<5)|(u64)(h),c); }
        for(int w=max(moff,0)+1; w<=n-p; w++){ if(w==1) continue; u64 nm=(mask|(1ULL<<(w-1)))>>1; for(int a=0;a<h;a++) nf[a]=f[a]; nf[h]=h; nxt.add(((nm*fact[h+1]+(u64)enc(nf,h+1))<<5)|(u64)(h+1),c); }
      }
    }
    cur.clear(); swap(cur,nxt);
  }
  printf("n=%d c321=%llu maxlayer=%zu\n",n,total,maxl); return 0; }
