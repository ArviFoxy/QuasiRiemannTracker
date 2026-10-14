import re,sys,os
from pathlib import Path
root=Path('openai-math/lean')
cand=Path('/home/user/QuasiRiemannTracker/submissions/cycle61-c0125139/src')
imp=re.compile(r'^\s*(?:public\s+)?import\s+(.+)$')
def imports(path):
    out=[]
    for line in open(path,encoding='utf8'):
        m=imp.match(line)
        if m:
            for d in m.group(1).split('--')[0].split(): out.append(d)
    return out
start=set()
for p in cand.rglob('*.lean'):
    for d in imports(p):
        if d.startswith('OAI.'): start.add(d)
seen=set(); stack=list(start); lines=0
while stack:
    m=stack.pop()
    if m in seen: continue
    f=root/(m.replace('.','/')+'.lean')
    if not f.exists(): continue
    seen.add(m); lines+=sum(1 for _ in open(f,encoding='utf8'))
    for d in imports(f):
        if d.startswith('OAI.') and d not in seen: stack.append(d)
print('direct OAI imports',len(start),'closure modules',len(seen),'lines',lines)
