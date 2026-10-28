"""theta from the return replica (analysis/model/common.py, fast.py) for the end faces of the greedy floor chains.
Role split = count face C at the chain face, physical/capP face fixed at PR86 step-40 child (0.9907142, 2.3715);
single = one face for both roles.  Float replica, NOT a Lean check."""
import sys, re, copy
sys.path.insert(0,'$SCRATCH/analysis/model')
from fast import *
DL,P=grids()
base=mk86()
PFACE=(0.9907142,2.3715)
def parse(fn):
    rows=[]
    for l in open(fn):
        m=re.match(r'k=\s*(\d+) L=([0-9.]+) B=([0-9.]+) s0=([0-9.]+)',l)
        if m: rows.append((int(m.group(1)),float(m.group(2)),float(m.group(3)),float(m.group(4))))
    return rows
def theta(fc,fp):
    r=copy.deepcopy(base)
    r.faces={'C':Face(fc[0],fc[1],0.09999,False),'capP':Face(fp[0],fp[1],0.062,True)}
    r.physB,r.physL=fp
    c,h,s,rr=solve_c_fast(r,iters=18,DL=DL,P=P,hspan=0.03,clo=0.12,chi=0.13)
    cw=rr.check_windows(n=31)
    bad=[(i+1,w[0]) for i,(w,m,j) in enumerate(cw) if m<=0]
    return 1-c,bad
if __name__=='__main__':
    floors=sys.argv[1].split(',')
    nlast=int(sys.argv[2])
    for f in floors:
        rows=parse(('chain_%s.log'%f if f.startswith('dL') else 'chain_floor_%s.log'%f))
        for (k,L,B,s0) in rows[-nlast:]:
            th,bad=theta((B,L),PFACE)
            ths,_=theta((B,L),(B,L))
            print('floor %s step %d  L=%.4f B=%.6f s0=%.5f  theta(role split)=%.9f bad=%s | theta(single)=%.9f'%(f,k,L,B,s0,th,bad,ths),flush=True)
