// Fiscus-Hurlbert-Myzelev-Pence dominating set game (normal play): players alternately choose an unchosen vertex;
// the player whose choice first makes the chosen set dominating wins. Retrograde over all subsets.
// stdin: n, then n closed-neighbourhood bitmasks. Output: N (first player wins) or P, plus winning first moves.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(){
  int n; if(scanf("%d",&n)!=1) return 1; uint64_t NB[64]; for(int i=0;i<n;i++){ unsigned long long x; scanf("%llu",&x); NB[i]=x; }
  uint64_t FULL=(n==64)?~0ULL:((1ULL<<n)-1);
  uint64_t total=1ULL<<n; uint8_t *win=calloc(total/8+1,1); // win bit: player to move at S wins
  for(uint64_t S=total; S-- > 0;){
    uint64_t dom=0; uint64_t T=S; while(T){ int v=__builtin_ctzll(T); T&=T-1; dom|=NB[v]; }
    if(dom==FULL) continue; // terminal: player to move has lost (previous player made it dominating) -> win=0
    uint64_t U=FULL&~S; int w=0;
    while(U){ int v=__builtin_ctzll(U); U&=U-1; uint64_t S2=S|(1ULL<<v); if(!((win[S2>>3]>>(S2&7))&1)){ w=1; break; } }
    if(w) win[S>>3]|=1<<(S&7);
  }
  int r=win[0]&1; printf("%s", r?"N":"P");
  if(r){ printf(" winning first moves:"); for(int v=0;v<n;v++){ uint64_t S2=1ULL<<v; if(!((win[S2>>3]>>(S2&7))&1)) printf(" %d",v);} }
  printf("\n"); return 0; }
