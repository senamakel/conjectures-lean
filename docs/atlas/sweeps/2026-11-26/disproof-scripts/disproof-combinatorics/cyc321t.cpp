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
struct HT { vector<u128> k; vector<u64> c; vector<char> o; size_t n=0, cap=0;
  void init(size_t cp){ cap=1; while(cap<cp*2) cap<<=1; k.assign(cap,0); c.assign(cap,0); o.assign(cap,0); n=0;}
  void clear(){ vector<u128>().swap(k); vector<u64>().swap(c); vector<char>().swap(o); n=cap=0;}
  static inline size_t h(u128 x){ u64 a=(u64)x, b=(u64)(x>>64); a^=b*0x9E3779B97F4A7C15ULL; a^=a>>29; a*=0xBF58476D1CE4E5B9ULL; a^=a>>32; return a;}
  void grow(){ vector<u128> ok; vector<u64> oc; vector<char> oo; ok.swap(k); oc.swap(c); oo.swap(o); size_t oc2=cap; init(cap); for(size_t i=0;i<oc2;i++) if(oo[i]) add(ok[i],oc[i]); }
  void add(u128 key,u64 v){ if(cap==0) init(1024); if((n+1)*10>cap*7) grow(); size_t m=cap-1, i=h(key)&m; while(o[i]){ if(k[i]==key){c[i]+=v;return;} i=(i+1)&m;} o[i]=1;k[i]=key;c[i]=v;n++; }
};
// key = mask<<64 | lehmer  (h<=20 so lehmer < 2^62)

// deterministic completion once the maximum n has been used: every later entry is the
// smallest unused value. Returns 1 if the permutation ends up a single n-cycle.
static int n_glob;
static u64 tail321(u64 mask,int*f0,int h,int p){ int f[40]; memcpy(f,f0,sizeof(int)*h); int n=n_glob;
  for(;p<n;p++){ int q=p+1;
    if(mask&1){ int s=0; while(f[s]!=0) s++;
      if(h==0) return 0;
      if(s==0){ return (q==n && h==1)?1:0; }
      int nf[40]; for(int a=1;a<h;a++) nf[a-1]=f[a]-1; nf[s-1]=f[0]-1; h--; memcpy(f,nf,sizeof(int)*h); mask>>=1;
    } else {
      if(h==0) return 0; // smallest unused is q itself: fixed point
      int fu=f[0]; for(int a=1;a<h;a++) f[a-1]=f[a]; f[h-1]=fu; mask>>=1;
    } }
  return 0; }
int main(int argc,char**argv){ int n=atoi(argv[1]); n_glob=n;
  HT cur, nxt; cur.add(0,1); u64 total=0; size_t maxl=0; int f[40], nf[40];
  for(int p=0;p<n;p++){ int q=p+1; maxl=max(maxl,cur.n);
    for(size_t i=0;i<cur.cap;i++) if(cur.o[i]){ u64 c=cur.c[i]; u64 mask=(u64)(cur.k[i]>>64); int h=__builtin_popcountll(mask);
      dec(cur.k[i]&(((u128)1<<64)-1),h,f); int moff=64-(mask?__builtin_clzll(mask):64);
      if(mask&1){ int s=0; while(f[s]!=0) s++;
        if(s==0){ if(q==n && h==1) total+=c; }
        else { for(int a=1;a<h;a++) nf[a-1]=f[a]-1; nf[s-1]=f[0]-1; nxt.add(((u128)(mask>>1)<<64)|enc(nf,h-1),c); }
        for(int w=moff+1; w<=n-p; w++){ u64 nm=(mask|(1ULL<<(w-1)))>>1; for(int a=0;a<h;a++) nf[a]=f[a]-1; nf[s]=h-1; if(w==n-p) total+=c*tail321(nm,nf,h,p+1); else nxt.add(((u128)nm<<64)|enc(nf,h),c); }
      } else {
        if(h>0){ int fu=f[0]; for(int a=1;a<h;a++) nf[a-1]=f[a]; nf[h-1]=fu; nxt.add(((u128)(mask>>1)<<64)|enc(nf,h),c); }
        for(int w=max(moff,0)+1; w<=n-p; w++){ if(w==1) continue; u64 nm=(mask|(1ULL<<(w-1)))>>1; for(int a=0;a<h;a++) nf[a]=f[a]; nf[h]=h; if(w==n-p) total+=c*tail321(nm,nf,h+1,p+1); else nxt.add(((u128)nm<<64)|enc(nf,h+1),c); }
      }
    }
    cur.clear(); swap(cur,nxt);
  }
  printf("n=%d c321=%llu maxlayer=%zu\n",n,total,maxl); return 0; }
