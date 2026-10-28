import sys
from fractions import Fraction as Fr
import pr86, cert_return as CR
cfg = pr86.Cfg(th=Fr(8739557,10**7))
for depth in (10, 14):
    fb = pr86.failing_boxes(cfg, 'newTop', maxdepth=depth)
    print('depth', depth, 'failing boxes on newTop:', len(fb))
    for b in fb[:6]:
        (d0,d1),(p0,p1)=b
        print('   delta in [%.5f,%.5f]  p in [%.5f,%.5f]' % (float(d0),float(d1),float(p0),float(p1)))
# analysis at the point (delta=0.4415,p=0.5): value of each branch count and margin
pr86.apply_globals(cfg)
G = pr86.geometry(cfg)
edges = {nm:(d,C) for nm,d,C in pr86.edge_list(cfg,G)}
d,C = edges['newTop']
print('geometry: ell=%.6f x=%.6f y=%.6f kappa=%.6f dplus=%.6f C_newTop=%.6f' % (tuple(float(G[k]) for k in ('ell','x','y','kap','dplus')) + (float(C),)))
cands = pr86.candidate_list(cfg, G)
def evalpoly(a, dl, p):
    return sum(float(c)*dl**i*p**j for (i,j),c in a.items())
for dl in (0.43, 0.44, 0.4415, 0.443, 0.45):
    p = 0.5
    row=[]
    for name, br, meta in cands:
        J = evalpoly(br['J'], dl, p); N = evalpoly(br['N'], dl, p)
        Eb = float(Fr(1,2) + 13*G['h']/75 - G['y']/2 - G['ell']/2 - Fr(9,100)*d) + dl/2 + dl*p*float(G['ell'] - C/2)
        cnt = N/J
        marg = float(cfg.th) - float(cfg.reserve) - (Eb + 0.75*float(d)*cnt)
        row.append('%s: count=%.6f margin=%+.3e' % (name, cnt, marg))
    print('delta=%.4f p=0.5  ' % dl + ' | '.join(row))
