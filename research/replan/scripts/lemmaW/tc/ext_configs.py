import json, sys, time, math
from multiprocessing import Pool
from fractions import Fraction as Fr
import pr86, best, ode_faces as OF
chain = json.load(open('chain86.json'))
base = pr86.Cfg()
def ch(k): return (Fr(chain[k]['B']), Fr(chain[k]['L']))
def ode(L): return (OF.frac(OF.B_ode(L)), OF.frac(L))
def flow(fn, k):
    for l in open('../../model/' + fn):
        r = json.loads(l)
        if r['k'] == k and not r.get('infeasible'): return (OF.frac(r['B']), OF.frac(r['L']))
Lw = OF.wall()
CONFIGS = [
 # (label, kind, count face, physical face)
 ('PR86 as submitted: single face k=46', 'exact', ch(46), ch(46)),
 ('PR86 chain, role split C=46, P=38', 'exact', ch(46), ch(38)),
 ('PR86 chain, role split C=46, P=39', 'exact', ch(46), ch(39)),
 ('PR86 chain, role split C=46, P=37', 'exact', ch(46), ch(37)),
 ('greedy dL=0.005 step 47 (s0=0.0853) single face', 'float-face', flow('flow_dL0.005_eps1e-06.jsonl', 47), flow('flow_dL0.005_eps1e-06.jsonl', 47)),
 ('greedy dL=0.005 step 47 as count, k=38 as physical', 'float-face', flow('flow_dL0.005_eps1e-06.jsonl', 47), ch(38)),
 ('greedy dL=0.0025 (92 steps): single face at L=2.3415', 'float-face', flow('flow_dL0.0025_eps1e-06.jsonl', 92), flow('flow_dL0.0025_eps1e-06.jsonl', 92)),
 ('greedy dL=0.0025: count L=2.3415 (k=92), physical L=2.3865 (k=76)', 'float-face', flow('flow_dL0.0025_eps1e-06.jsonl', 92), flow('flow_dL0.0025_eps1e-06.jsonl', 76)),
 ('greedy dL=0.0025: count k=93 (L=2.339, s0=0.0716), physical k=76', 'float-face', flow('flow_dL0.0025_eps1e-06.jsonl', 93), flow('flow_dL0.0025_eps1e-06.jsonl', 76)),
 ('greedy dL=0.00125 (184 steps): count L=2.3415 (k=184), physical k=152 (L=2.3865)', 'float-face', flow('flow_dL0.00125_eps1e-06.jsonl', 184), flow('flow_dL0.00125_eps1e-06.jsonl', 152)),
 ('greedy dL=0.00125: count k=186 (L=2.339), physical k=152', 'float-face', flow('flow_dL0.00125_eps1e-06.jsonl', 186), flow('flow_dL0.00125_eps1e-06.jsonl', 152)),
 ('greedy dL=0.00125: count k=187 (L=2.33775, s0=0.0872), physical k=152', 'float-face', flow('flow_dL0.00125_eps1e-06.jsonl', 187), flow('flow_dL0.00125_eps1e-06.jsonl', 152)),
 ('ODE continuum: single face at L=2.3415', 'ode', ode(2.3415), ode(2.3415)),
 ('ODE continuum: single face at the wall L=%.5f' % Lw, 'ode', ode(Lw), ode(Lw)),
 ('ODE continuum: role split C=wall, P at L=2.3865 (k~38)', 'ode', ode(Lw), ode(2.3865)),
 ('ODE continuum: role split C=wall, P at L=2.371', 'ode', ode(Lw), ode(2.371)),
 ('ODE continuum: role split C=2.3415, P at L=2.3865', 'ode', ode(2.3415), ode(2.3865)),
]
def job(a):
    i, win = a
    label, kind, fc, fp = CONFIGS[i]
    cfg = base.copy(windows=win, BC=fc[0], LC=fc[1], BP=fp[0], LP=fp[1])
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873930000, step=1000)
    if r is None: return (i, win, None, None, None)
    return (i, win, r[0], float(r[1]), best.why(cfg, r[0]-1, unit=10**9))
if __name__ == '__main__':
    jobs = [(i, w) for i in range(len(CONFIGS)) for w in ('collet', 'lemmaW')]
    out = {}
    with Pool(4) as pool:
        for i, win, t, h, why in pool.imap_unordered(job, jobs):
            out[(i, win)] = (t, h, why)
    for i, (label, kind, fc, fp) in enumerate(CONFIGS):
        c, w = out[(i, 'collet')], out[(i, 'lemmaW')]
        print('%-82s [%-10s] count(B=%.7f,L=%.5f) phys(B=%.7f,L=%.5f)  Collet %.9f  LemmaW %.9f  h=%.6f  %s' % (
            label, kind, float(fc[0]), float(fc[1]), float(fp[0]), float(fp[1]), c[0]/1e9, w[0]/1e9, c[1], c[2]))
