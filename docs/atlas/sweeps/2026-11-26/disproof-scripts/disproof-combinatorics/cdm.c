/* Costa-Luu-Wood Conjecture 10 (CDM): every connected graph G with alpha(G)=2 has a
   non-empty connected dominating matching. Input: graph6 lines of H = complement of G
   (H triangle-free). Matching M (edges of G): connected = every two edges e,f of M have
   an edge of G between V(e) and V(f); dominating = every vertex outside V(M) is adjacent
   (in G) to an endpoint of every edge of M. Prints any H for which no such M exists. */
#include <stdio.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t U;
static int n; static U adjH[32];
static int Me[32][2], mlen;
static long nodes;
static int gconn(int a,int b,int c,int d){ /* some G-edge between {a,b} and {c,d} */
  if(!(adjH[a]>>c&1)) return 1; if(!(adjH[a]>>d&1)) return 1; if(!(adjH[b]>>c&1)) return 1; if(!(adjH[b]>>d&1)) return 1; return 0; }
static int dfs(U used,U req){ nodes++;
  if(!req) return 1;
  int r=__builtin_ctz(req);
  for(int s=0;s<n;s++){ if(s==r || (used>>s&1) || (adjH[r]>>s&1)) continue;
    int ok=1; for(int i=0;i<mlen&&ok;i++) ok=gconn(r,s,Me[i][0],Me[i][1]); if(!ok) continue;
    U nu=used|(1u<<r)|(1u<<s); U bad=adjH[r]&adjH[s];
    Me[mlen][0]=r; Me[mlen][1]=s; mlen++;
    int res=dfs(nu,(req|bad)&~nu); mlen--; if(res) return 1; }
  return 0; }
int main(){ char line[256]; long cnt=0, skipped=0, bad=0;
  while(fgets(line,sizeof line,stdin)){ int L=strlen(line); while(L&&(line[L-1]=='\n'||line[L-1]=='\r')) line[--L]=0; if(!L) continue;
    n=line[0]-63; memset(adjH,0,sizeof adjH); int k=0; const char*p=line+1; int bits=0,val=0;
    for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(bits==0){ val=(*p++)-63; bits=6;} bits--; if(val>>bits&1){ adjH[i]|=1u<<j; adjH[j]|=1u<<i; } k++; }
    /* skip if G = complement disconnected: BFS in G */
    U all=(n==32)?0xffffffffu:((1u<<n)-1), seen=1, fr=1;
    while(fr){ int v=__builtin_ctz(fr); fr&=fr-1; U nb=all&~adjH[v]&~(1u<<v)&~seen; seen|=nb; fr|=nb; }
    if(seen!=all){ skipped++; continue; }
    cnt++; int found=0;
    for(int x=0;x<n&&!found;x++) for(int y=x+1;y<n&&!found;y++){ if(adjH[x]>>y&1) continue;
      U used=(1u<<x)|(1u<<y); mlen=0; Me[0][0]=x; Me[0][1]=y; mlen=1;
      if(dfs(used,(adjH[x]&adjH[y])&~used)) found=1; }
    if(!found){ bad++; printf("NO CDM: %s\n",line); fflush(stdout); }
  }
  fprintf(stderr,"checked %ld (skipped %ld disconnected-complement), counterexamples %ld, nodes %ld\n",cnt,skipped,bad,nodes); return 0; }
