import sys,urllib.request,re
ids=','.join(sys.argv[1:])
t=urllib.request.urlopen("https://export.arxiv.org/api/query?id_list="+ids+"&max_results=50",timeout=90).read().decode()
for e in t.split('<entry>')[1:]:
    g=lambda p:' '.join(re.search(p,e,re.S).group(1).split())
    print(g(r'<id>(.*?)</id>'),'|',g(r'<title>(.*?)</title>'),'|',', '.join(re.findall(r'<name>(.*?)</name>',e)));print('  ',g(r'<summary>(.*?)</summary>'));print()
