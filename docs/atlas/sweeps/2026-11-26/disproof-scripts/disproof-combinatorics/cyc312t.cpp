// Count cyclic 312-avoiding permutations of [n], exact (u64 counts).
// DP over stack-realisation states (v pushes, p pops, bijection g: stack position -> end rank).
// Only states with v <= n-2 are stored. A push to v = n-1 is completed on the spot:
// the remaining suffix is (j pops, push n, pop everything), j = 0..h-1, and for each j the
// outcome is decided by whether s -> (h-1) - g(s) is a single h-cycle.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned __int128 u128; typedef unsigned long long u64;
static inline u128 enc(const int*g,int h){ u128 r=0; unsigned used=0;
  for(int i=0;i<h;i++){ int x=g[i]; int less=__builtin_popcount(used&((1u<<x)-1)); r=r*(u128)(h-i)+(u128)(x-less); used|=1u<<x;} return r;}
static inline void dec(u128 r,int h,int*g){ int dig[40]; for(int i=h-1;i>=0;i--){ dig[i]=(int)(r%(u128)(h-i)); r/=(u128)(h-i);} unsigned used=0;
  for(int i=0;i<h;i++){ int k=dig[i]; for(int x=0;x<h;x++){ if(!(used>>x&1)){ if(k==0){g[i]=x;used|=1u<<x;break;} k--; } } } }
struct E { u64 k, c; bool operator<(const E&o)const{return k<o.k;} };
struct Group { vector<E> a; map<u128,u64> big; size_t size()const{return a.size()+big.size();} void clear(){ vector<E>().swap(a); big.clear(); } };
static const int SMALL=20;
static void compress(vector<E>&t){ if(t.empty())return; std::sort(t.begin(),t.end()); size_t w=0; for(size_t i=1;i<t.size();i++){ if(t[i].k==t[w].k) t[w].c+=t[i].c; else t[++w]=t[i]; } t.resize(w+1); t.shrink_to_fit(); }
// pop in place; returns false if a cycle closes
static inline bool popop(int*g,int&h){ int a=0; while(g[a]!=0) a++; if(a==h-1) return false; int gt=g[h-1]; for(int j=0;j<h-1;j++) g[j]--; g[a]=gt-1; h--; return true; }
static inline bool final_ok(const int*g,int h){ // single cycle of s -> h-1-g(s)
  int s=0, len=0; do { s=h-1-g[s]; len++; } while(s!=0 && len<=h); return len==h; }
// state at v=n-1 with height h (already includes the push); count completions
static u64 tail(const int*g0,int h0){ int g[40]; int h=h0; memcpy(g,g0,sizeof(int)*h); u64 cnt=0;
  for(int j=0;;j++){ // push n now
    g[h]=h; if(final_ok(g,h+1)) cnt++;
    if(h<=1) break; if(!popop(g,h)) break; }
  return cnt; }
int main(int argc,char**argv){ int N=atoi(argv[1]); int V=N-2;
  if(N<3){ printf("n=%d c312=%d\n",N,N==0?1:1); return 0; }
  vector<Group> cur(N+2), nxt(N+2);
  cur[0].a.push_back({0,1});
  u64 total=0; size_t maxl=0; int g[40], ng[40];
  for(int t=0;t<2*N;t++){
    size_t lay=0; for(int v=0;v<=V;v++) lay+=cur[v].size(); maxl=max(maxl,lay); if(lay==0) break;
    for(int v=0;v<=V+1;v++){
      // tail events: pushes from cur[V] -> v=N-1, evaluate immediately
      if(v==V+1){ Group &G=cur[V]; int h=2*V-t; if(h>=0){ auto proc=[&](u128 key,u64 c){ dec(key,h,g); g[h]=h; total+=c*tail(g,h+1); };
          for(auto&e:G.a) proc(e.k,e.c); for(auto&kv:G.big) proc(kv.first,kv.second);} G.clear(); continue; }
      int hn=2*v-(t+1); if(hn<0){ if(v>0) cur[v-1].clear(); continue; }
      vector<E> tmp; map<u128,u64> tb; bool small=(hn<=SMALL);
      if(small) tmp.reserve(cur[v].size()+(v>=1?cur[v-1].size():0));
      auto emit=[&](const int*arr,int hh,u64 c){ u128 key=enc(arr,hh); if(small) tmp.push_back({(u64)key,c}); else tb[key]+=c; };
      { Group &G=cur[v]; int h=2*v-t;
        auto proc=[&](u128 key,u64 c){ dec(key,h,g); int a=0; while(g[a]!=0) a++; if(a==h-1) return;
          int gt=g[h-1]; for(int j=0;j<h-1;j++) ng[j]=g[j]-1; ng[a]=gt-1; emit(ng,h-1,c); };
        if(h>0){ for(auto&e:G.a) proc(e.k,e.c); for(auto&kv:G.big) proc(kv.first,kv.second); } }
      if(v>=1){ Group &G=cur[v-1]; int h=2*(v-1)-t;
        auto proc=[&](u128 key,u64 c){ dec(key,h,g); g[h]=h; emit(g,h+1,c); };
        if(h>=0){ for(auto&e:G.a) proc(e.k,e.c); for(auto&kv:G.big) proc(kv.first,kv.second); }
        G.clear(); }
      compress(tmp); nxt[v].a.swap(tmp); nxt[v].big.swap(tb);
    }
    for(int v=0;v<=N;v++) cur[v].clear();
    swap(cur,nxt);
  }
  printf("n=%d c312=%llu maxlayer_stored=%zu\n",N,total,maxl); return 0; }
