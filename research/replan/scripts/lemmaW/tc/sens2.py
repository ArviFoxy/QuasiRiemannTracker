import json, sys, time
from fractions import Fraction as Fr
import pr86, best
chain = json.load(open('chain86.json'))
B46, L46 = Fr(chain[46]['B']), Fr(chain[46]['L'])
def th(cfg):
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873940000, step=1000)
    return r[0]/1e9
for sP in (Fr(7,100), Fr(9,100)):
    base = pr86.Cfg(BC=B46, LC=L46, BP=B46, LP=L46, sP=sP, capP=max(sP+Fr(1,1000), Fr(31,500)))
    t0 = th(base)
    out = ['sP=%.2f base %.9f' % (float(sP), t0)]
    for role, (kB, kL) in (('count', ('BC','LC')), ('physical', ('BP','LP'))):
        for d in (Fr(1,10000), Fr(1,2000)):
            tp = th(base.copy(**{kB: getattr(base,kB)+d})); tm = th(base.copy(**{kB: getattr(base,kB)-d}))
            out.append('%s dB=%g: d/dB=%+.5f (fwd %+.5f bwd %+.5f)' % (role, float(d), (tp-tm)/(2*float(d)), (tp-t0)/float(d), (t0-tm)/float(d)))
        for d in (Fr(1,1000), Fr(1,200)):
            tp = th(base.copy(**{kL: getattr(base,kL)+d})); tm = th(base.copy(**{kL: getattr(base,kL)-d}))
            out.append('%s dL=%g: d/dL=%+.6f (fwd %+.6f bwd %+.6f)' % (role, float(d), (tp-tm)/(2*float(d)), (tp-t0)/float(d), (t0-tm)/float(d)))
    print('\n  '.join(out), flush=True)
