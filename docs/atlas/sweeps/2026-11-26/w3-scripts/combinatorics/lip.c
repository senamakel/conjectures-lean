// longest induced path: randomized DFS restarts with node budget; reports best length (vertices) found
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MX 512
int n,m,target; unsigned char A[MX][MX]; int deg[MX], nb[MX][MX];
int path[MX], best=0, bestp[MX]; int cntadj[MX]; // cntadj[v] = #path vertices adjacent to v
int onp[MX]; long long budget;
void dfs(int len){
  if(len>best){best=len; memcpy(bestp,path,len*sizeof(int));}
  if(best>=target && target>0) return;
  if(--budget<0) return;
  int e=path[len-1]; int cand[MX],c=0;
  for(int i=0;i<deg[e];i++){int u=nb[e][i]; if(!onp[u] && cntadj[u]==1) cand[c++]=u;}
  for(int i=c-1;i>0;i--){int j=rand()%(i+1); int t=cand[i];cand[i]=cand[j];cand[j]=t;}
  for(int i=0;i<c;i++){int u=cand[i]; path[len]=u; onp[u]=1; for(int k=0;k<deg[u];k++) cntadj[nb[u][k]]++;
    dfs(len+1); for(int k=0;k<deg[u];k++) cntadj[nb[u][k]]--; onp[u]=0; if(budget<0||(target>0&&best>=target)) return;}
}
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); fscanf(f,"%d %d %d",&n,&m,&target); if(argc>3) target=atoi(argv[3]);
  for(int i=0;i<m;i++){int a,b; fscanf(f,"%d %d",&a,&b); A[a][b]=A[b][a]=1; nb[a][deg[a]++]=b; nb[b][deg[b]++]=a;}
  long long per=atoll(argv[2]); srand(12345);
  for(int r=0;r<2000 && best<target;r++){ int s=rand()%n; memset(onp,0,sizeof onp); memset(cntadj,0,sizeof cntadj);
    path[0]=s; onp[s]=1; for(int k=0;k<deg[s];k++) cntadj[nb[s][k]]++; budget=per; dfs(1); }
  // verify
  for(int i=0;i<best;i++) for(int j=i+1;j<best;j++){ if(A[bestp[i]][bestp[j]] != (j==i+1)) {printf("VERIFY FAIL\n");return 1;} }
  printf("%s best=%d target=%d %s path:",argv[1],best,target,best>=target?"HOLDS":"NOTFOUND");
  for(int i=0;i<best;i++) printf(" %d",bestp[i]); printf("\n"); return 0;
}
