"""Compile Candidate modules in dependency order with lc.sh, N parallel jobs.
Skips modules whose olean is newer than the source and all Candidate deps' oleans.
Usage: cbuild.py JOBS [TARGET ...]   (default target Candidate.Main)"""
import os,sys,subprocess,time,re
sys.path.insert(0,os.path.dirname(__file__))
from ready import imports,closure,SRC,OL
LOG=os.environ.get('QRH_LOGS','logs')
os.makedirs(LOG,exist_ok=True)
jobs=int(sys.argv[1]); targets=sys.argv[2:] or ['Candidate.Main']
mods=set()
for t in targets: mods|={m for m in closure(t) if m.startswith('Candidate.')}|{t}
deps={m:{d for d in imports(m) if d.startswith('Candidate.')} for m in mods}
def src(m): return os.path.join(SRC,m.replace('.','/')+'.lean')
def ol(m): return OL+m.replace('.','/')+'.olean'
def fresh(m):
    if not os.path.exists(ol(m)): return False
    t=os.path.getmtime(ol(m))
    if os.path.getmtime(src(m))>t: return False
    return all(os.path.exists(ol(d)) and os.path.getmtime(ol(d))<=t for d in deps[m])
done=set(); failed=set(); running={}
# mark fresh modules done in topo order
changed=True
while changed:
    changed=False
    for m in mods-done:
        if deps[m]<=done and fresh(m): done.add(m); changed=True
print(f'{len(done)} fresh, {len(mods)-len(done)} to build',flush=True)
start=time.time()
while True:
    for m,(p,t0) in list(running.items()):
        if p.poll() is not None:
            del running[m]
            out=open(f'{LOG}/{m}.log').read()
            ok = 'exit 0' in out
            (done if ok else failed).add(m)
            print(f'{"OK " if ok else "ERR"} {m} {time.time()-t0:.0f}s [{len(done)}/{len(mods)}]',flush=True)
    blocked={m for m in mods-done-failed if deps[m]&failed}
    ready=[m for m in sorted(mods-done-failed-blocked-set(running)) if deps[m]<=done]
    while ready and len(running)<jobs:
        m=ready.pop(0)
        f=open(f'{LOG}/{m}.log','w')
        p=subprocess.Popen([os.environ.get('QRH_LC',os.path.join(os.path.dirname(os.path.abspath(__file__)),'lc.sh')),m],stdout=f,stderr=subprocess.STDOUT)
        running[m]=(p,time.time())
    if not running:
        break
    time.sleep(2)
print('done',len(done),'failed',sorted(failed),'blocked',len(blocked),f'{time.time()-start:.0f}s',flush=True)
