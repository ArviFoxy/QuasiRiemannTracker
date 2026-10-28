import sys
sys.path.insert(0,'.')
from theta_floor import *
rows=parse('chain_floor_-1.0.log')
for (k,L,B,s0) in rows:
    if k in (26,28,30,32,34,36):
        th,bad=theta((B,L),PFACE)
        print('no-floor step %d L=%.4f B=%.6f s0=%.5f theta(role split)=%.9f bad=%s'%(k,L,B,s0,th,[b[0] for b in bad]),flush=True)
