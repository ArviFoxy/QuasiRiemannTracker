"""Import-closure helpers for compile_candidate.py (paths via QRH_PROJECT / QRH_SRC)."""
import os,re,sys,functools
PROJ=os.environ.get('QRH_PROJECT','/home/user/leanbuild/project')
SRC=os.environ.get('QRH_SRC',os.path.join(os.path.dirname(os.path.abspath(__file__)),'../../../submissions/detector-affine-c0125154/src'))
OL=PROJ+'/.lake/build/lib/lean/'
def path(mod):
    rel=mod.replace('.','/')+'.lean'
    for root in (SRC,PROJ):
        p=os.path.join(root,rel)
        if os.path.exists(p): return p
    return None
@functools.lru_cache(None)
def imports(mod):
    p=path(mod)
    if p is None: return ()
    out=[]
    for line in open(p,encoding='utf-8'):
        m=re.match(r'\s*import\s+(\S+)',line)
        if m: out.append(m.group(1))
    return tuple(out)
@functools.lru_cache(None)
def closure(mod):
    s=set()
    for i in imports(mod):
        if i.startswith(('OAI.','Candidate.')):
            s.add(i); s|=closure(i)
    return frozenset(s)
def built(mod): return os.path.exists(OL+mod.replace('.','/')+'.olean')
if __name__=='__main__':
    mods=sys.argv[1:]
    for m in mods:
        miss=[x for x in closure(m) if x.startswith('OAI.') and not built(x)]
        print(m, 'missingOAI', len(miss))
