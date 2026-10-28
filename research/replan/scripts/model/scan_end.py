import sys,time,json
sys.path.insert(0,'$SCRATCH/analysis/model')
from fast import *
DL,P=grids()
base=mk86()
fn=sys.argv[1]
ks=[int(x) for x in sys.argv[2].split(',')]
rows=[json.loads(l) for l in open(fn)]
rows=[r for r in rows if not r.get('infeasible')]
for r in rows:
    if r['k'] in ks:
        rr=mkface(r['B'],r['L'],r0=base)
        c,h,s,r2=solve_c_fast(rr,iters=22,DL=DL,P=P,hspan=0.02)
        cw=r2.check_windows(n=41)
        bad=[(w[0],round(w[1],3),j) for (w,m,j) in cw if m<=0]
        print('k=%d  L=%.4f B=%.7f s0=%.5f -> theta=%.9f h=%.4f bad=%s'%(r['k'],r['L'],r['B'],r['s0'],1-c,h,bad),flush=True)
