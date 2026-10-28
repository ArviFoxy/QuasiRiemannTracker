"""For chosen (A,D) along the no-floor greedy chain, compute for EACH gate separately the smallest crossing slope s0
for which that gate alone has reserve >= eps (bisection), to see which gate binds first and by what margin."""
import sys, json, numpy as np
sys.path.insert(0,'.')
from floor_chain import *
def gate_s0(gate,B0,L0,c0,dL,c,A,D,floor,eps,N=400):
    L=L0-dL
    def ok(s):
        m,_,vm=gmin(B0,L0,c0,B0-s*dL,L,c,A,D,floor,N=N)
        if m is None: return False
        x=m[gate]
        return (x>0) if gate in SCALEFREE else (x>=eps)
    xs=np.linspace(1e-5,c-1e-4,400)
    oks=[ok(s) for s in xs]
    # smallest s such that ok holds for ALL larger s up to c-1e-4 (monotone in practice)
    if not any(oks): return None
    # find first index from which all True
    last_false=max([i for i,o in enumerate(oks) if not o],default=-1)
    if last_false==len(xs)-1: return None
    i=last_false+1
    if i==0: return xs[0]
    a,b=xs[i-1],xs[i]
    for _ in range(40):
        mid=0.5*(a+b)
        if ok(mid): b=mid
        else: a=mid
    return b
if __name__=='__main__':
    floor=float(sys.argv[1]); dL=float(sys.argv[2]); Lend=float(sys.argv[3])
    sel=set(int(x) for x in sys.argv[4].split(','))
    rows=run(floor,dL,Lend)
    for r in rows:
        if r.get('infeasible') or r['k'] not in sel: continue
        d={}
        for g in GATES:
            if g in ('low','sel_deriv'): continue
            d[g]=gate_s0(g,r['B0'],r['L0'],0.1 if r['k']>1 else 0.1,dL,0.1,r['A'],r['D'],floor,1e-6)
        print('k=%d L=%.4f s0*=%.5f (A=%.3f D=%.1f) per-gate minimal s0: %s'%(r['k'],r['L'],r['s0'],r['A'],r['D'],
              ' '.join('%s=%s'%(g,('%.5f'%v if v is not None else 'none')) for g,v in sorted(d.items(),key=lambda kv:-(kv[1] if kv[1] is not None else 9)))),flush=True)
