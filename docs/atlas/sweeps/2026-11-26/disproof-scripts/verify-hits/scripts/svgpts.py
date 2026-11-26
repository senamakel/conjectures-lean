import re, sys
t = open(sys.argv[1]).read()
for m in re.finditer(r'transform="([^"]+)"', t):
    print(m.group(1))
