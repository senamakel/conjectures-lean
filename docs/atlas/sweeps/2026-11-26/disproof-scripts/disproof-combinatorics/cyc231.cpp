// Independent check: cyclic 231-avoiders (= cyclic 312-avoiders, by inversion) via a
// position sweep. Rule (from the definition of 231): pi(i) must lie in the lowest run of
// consecutive unused values. State: A = unused values <= p (path starts) with separator
// flags (a used value lies between consecutive A's / after the last A), mask of used values
// above p (path ends B), bijection f: A-rank -> B-rank.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned __int128 u128; typedef unsigned long long u64;
static inline u64 enc(const int*g,int h){ u64 r=0; unsigned used=0;
  for(int i=0;i<h;i++){ int x=g[i]; int less=__builtin_popcount(used&((1u<<x)-1)); r=r*(u64)(h-i)+(u64)(x-less); used|=1u<<x;} return r;}
static inline void dec(u64 r,int h,int*g){ int dig[40]; for(int i=h-1;i>=0;i--){ dig[i]=(int)(r%(u64)(h-i)); r/=(u64)(h-i);} unsigned used=0;
  for(int i=0;i<h;i++){ int k=dig[i]; for(int x=0;x<h;x++){ if(!(used>>x&1)){ if(k==0){g[i]=x;used|=1u<<x;break;} k--; } } } }
struct St { u64 sep; int gend; u64 mask; int h; int f[32]; };
static inline u128 pack(const St&s){ // h from popcount(mask); sep has h-1 bits
  u128 k=(u128)s.mask; k=(k<<1)|(u128)s.gend; k=(k<<20)|(u128)s.sep; k=(k<<64)|(u128)enc(s.f,s.h); return k; }
static inline void unpack(u128 k,St&s){ u64 le=(u64)k; k>>=64; s.sep=(u64)(k&((1u<<20)-1)); k>>=20; s.gend=(int)(k&1); k>>=1; s.mask=(u64)k; s.h=__builtin_popcountll(s.mask); dec(le,s.h,s.f); }
int main(int argc,char**argv){ int n=atoi(argv[1]);
  unordered_map<u128,u64> *cur=new unordered_map<u128,u64>(), *nxt=new unordered_map<u128,u64>();
  struct H{ size_t operator()(u128 x)const{ u64 a=(u64)x^((u64)(x>>64)*0x9E3779B97F4A7C15ULL); a^=a>>31; a*=0xBF58476D1CE4E5B9ULL; return a^(a>>29);} };
  unordered_map<u128,u64,H> C,Nx; St s0{}; C[pack(s0)]=1; u64 total=0; size_t mx=0;
  for(int p=0;p<n;p++){ int q=p+1; Nx.clear(); mx=max(mx,C.size());
    for(auto&kv:C){ St s; unpack(kv.first,s); u64 c=kv.second; int h=s.h;
      // candidates in the lowest run
      int candA=0; bool cont;
      if(h>0){ candA=1; int j=0; while(j<h-1 && !(s.sep>>j&1)){ j++; candA++; } cont=(j==h-1 && !s.gend); } else cont=true;
      vector<int> candV; if(cont){ int off=1; if(h==0) while(s.mask>>(off-1)&1) off++; while(off<=n-p && !(s.mask>>(off-1)&1)){ candV.push_back(off); off++; } }
      bool qinB=s.mask&1; int sidx=-1; if(qinB){ for(int a=0;a<h;a++) if(s.f[a]==0) sidx=a; }
      auto addA_remove=[&](St&t,int i){ // remove A[i] (it becomes used) from t (f already handled by caller)
        // separators
        u64 sep=t.sep; int hh=h; // old h
        vector<int> sp; for(int j=0;j<hh-1;j++) sp.push_back(sep>>j&1);
        int g=t.gend;
        if(hh==1){ sp.clear(); g=1; } else if(i==hh-1){ sp.pop_back(); g=1; } else { if(i==0) sp.erase(sp.begin()); else { sp[i-1]=1; sp.erase(sp.begin()+i);} }
        return make_pair(sp,g); };
      for(int i=0;i<candA;i++){
        if(qinB){ if(sidx==i){ if(q==n && h==1) total+=c; continue; }
          St t=s; int nf[32],k=0; for(int a=0;a<h;a++){ if(a==i) continue; int v=(a==sidx)?s.f[i]:s.f[a]; nf[k++]=v-1; }
          auto pr=addA_remove(t,i); St u; u.h=h-1; memcpy(u.f,nf,sizeof(int)*u.h); u.sep=0; for(size_t j=0;j<pr.first.size();j++) if(pr.first[j]) u.sep|=1ULL<<j; u.gend=1; u.mask=s.mask>>1; Nx[pack(u)]+=c;
        } else {
          St t=s; int nf[32],k=0; for(int a=0;a<h;a++){ if(a==i) continue; nf[k++]=s.f[a]; } nf[k++]=s.f[i];
          auto pr=addA_remove(t,i); vector<int> sp=pr.first; if(k>1) sp.push_back(pr.second);
          St u; u.h=k; memcpy(u.f,nf,sizeof(int)*k); u.sep=0; for(size_t j=0;j<sp.size();j++) if(sp[j]) u.sep|=1ULL<<j; u.gend=0; u.mask=s.mask>>1; Nx[pack(u)]+=c; }
      }
      for(int y:candV){ if(y==1) continue; int rank=__builtin_popcountll(s.mask&((1ULL<<(y-1))-1));
        if(qinB){ St u=s; for(int a=0;a<h;a++){ if(a==sidx) u.f[a]=rank-1; else { int nv=s.f[a]-1; if(nv>=rank-1) nv++; u.f[a]=nv; } }
          u.gend=1; u.mask=(s.mask|(1ULL<<(y-1)))>>1; u.h=h; Nx[pack(u)]+=c;
        } else { St u=s; for(int a=0;a<h;a++) u.f[a]=s.f[a]>=rank? s.f[a]+1 : s.f[a]; u.f[h]=rank; u.h=h+1;
          u.sep=s.sep; if(h>0) u.sep|=(u64)s.gend<<(h-1); u.gend=0; u.mask=(s.mask|(1ULL<<(y-1)))>>1; Nx[pack(u)]+=c; }
      }
    }
    swap(C,Nx);
  }
  printf("n=%d c231=%llu maxlayer=%zu\n",n,total,mx); return 0; }
