// Count cyclic 312-avoiding permutations of [n], exact (u64 counts).
// Same DP as cyc312.cpp (stack realisation, state = bijection stack position -> end rank),
// but layers are stored as sorted arrays grouped by number of pushes v, to save memory.
// Small heights (h<=20) use 64-bit Lehmer keys; larger heights use std::map with 128-bit keys.
#include <bits/stdc++.h>
#include <parallel/algorithm>
using namespace std;
typedef unsigned __int128 u128; typedef unsigned long long u64;
static inline u128 enc(const int*g,int h){ u128 r=0; unsigned used=0;
  for(int i=0;i<h;i++){ int x=g[i]; int less=__builtin_popcount(used&((1u<<x)-1)); r=r*(u128)(h-i)+(u128)(x-less); used|=1u<<x;} return r;}
static inline void dec(u128 r,int h,int*g){ int dig[40]; for(int i=h-1;i>=0;i--){ dig[i]=(int)(r%(u128)(h-i)); r/=(u128)(h-i);} unsigned used=0;
  for(int i=0;i<h;i++){ int k=dig[i]; for(int x=0;x<h;x++){ if(!(used>>x&1)){ if(k==0){g[i]=x;used|=1u<<x;break;} k--; } } } }
struct E { u64 k, c; bool operator<(const E&o)const{return k<o.k;} };
struct Group { int h=-1; vector<E> a; map<u128,u64> big; size_t size()const{return a.size()+big.size();}
  void clear(){ vector<E>().swap(a); big.clear(); } };
static const int SMALL=20;
static void compress(vector<E>&t){ if(t.empty())return; std::sort(t.begin(),t.end()); size_t w=0; for(size_t i=1;i<t.size();i++){ if(t[i].k==t[w].k) t[w].c+=t[i].c; else t[++w]=t[i]; } t.resize(w+1); t.shrink_to_fit(); }
int main(int argc,char**argv){ int N=atoi(argv[1]);
  vector<Group> cur(N+2), nxt(N+2);
  cur[0].h=0; cur[0].a.push_back({0,1});
  u64 total=0; size_t maxl=0; int g[40], ng[40];
  for(int t=0;t<2*N;t++){
    size_t lay=0; for(int v=0;v<=N;v++) lay+=cur[v].size(); maxl=max(maxl,lay);
    for(int v=0;v<=N;v++){ // build nxt[v] from pops of cur[v] and pushes of cur[v-1]
      int hn=2*v-(t+1); if(hn<0||hn>N){ if(v>0) cur[v-1].clear(); continue; }
      vector<E> tmp; map<u128,u64> tb; bool small=(hn<=SMALL); if(small) tmp.reserve(cur[v].a.size()+cur[v].big.size()+(v>=1?cur[v-1].a.size()+cur[v-1].big.size():0));
      auto emit=[&](const int*arr,int hh,u64 c){ u128 key=enc(arr,hh); if(small) tmp.push_back({(u64)key,c}); else tb[key]+=c; };
      // pops from cur[v]
      { Group &G=cur[v]; int h=2*v-t; int p=t-v;
        auto proc=[&](u128 key,u64 c){ dec(key,h,g); int a=0; while(g[a]!=0) a++;
          if(a==h-1){ if(v==N && p==N-1) total+=c; return; }
          int gt=g[h-1]; for(int j=0;j<h-1;j++) ng[j]=g[j]-1; ng[a]=gt-1; emit(ng,h-1,c); };
        if(h>0){ for(auto&e:G.a) proc(e.k,e.c); for(auto&kv:G.big) proc(kv.first,kv.second); } }
      // pushes from cur[v-1]
      if(v>=1 && v-1<N){ Group &G=cur[v-1]; int h=2*(v-1)-t;
        auto proc=[&](u128 key,u64 c){ dec(key,h,g); g[h]=h; emit(g,h+1,c); };
        if(h>=0){ for(auto&e:G.a) proc(e.k,e.c); for(auto&kv:G.big) proc(kv.first,kv.second); }
        G.clear(); }
      compress(tmp); nxt[v].h=hn; nxt[v].a.swap(tmp); nxt[v].big.swap(tb);
    }
    for(int v=0;v<=N;v++) cur[v].clear();
    swap(cur,nxt);
  }
  printf("n=%d c312=%llu maxlayer=%zu\n",N,total,maxl); return 0; }
