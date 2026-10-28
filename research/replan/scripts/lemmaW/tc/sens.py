import json, sys, time
from fractions import Fraction as Fr
import pr86, best
chain = json.load(open('chain86.json'))
B46, L46 = Fr(chain[46]['B']), Fr(chain[46]['L'])
base = pr86.Cfg(BC=B46, LC=L46, BP=B46, LP=L46)
def th(cfg, hfix=None):
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873940000, step=1000, hfix=hfix)
    return r[0]/1e9
t0 = th(base)
print('base (k=46, floor-coupled h): %.9f' % t0)
dB, dL = Fr(1,1000), Fr(1,100)
for role, keys in (('count', ('BC','LC')), ('physical', ('BP','LP'))):
    kB, kL = keys
    tp = th(base.copy(**{kB: getattr(base,kB)+dB})); tm = th(base.copy(**{kB: getattr(base,kB)-dB}))
    dthdB = (tp-tm)/(2*float(dB))
    tp = th(base.copy(**{kL: getattr(base,kL)+dL})); tm = th(base.copy(**{kL: getattr(base,kL)-dL}))
    dthdL = (tp-tm)/(2*float(dL))
    print('%-8s dtheta/dB = %+.5f   dtheta/dL = %+.6f   break-even chain slope s0* = %.4f' % (role, dthdB, dthdL, -dthdL/dthdB * -1 if False else dthdL/(-dthdB)))
tp = th(base.copy(BC=B46+dB, BP=B46+dB)) ; tm = th(base.copy(BC=B46-dB, BP=B46-dB))
dthdB = (tp-tm)/(2*float(dB))
tp = th(base.copy(LC=L46+dL, LP=L46+dL)) ; tm = th(base.copy(LC=L46-dL, LP=L46-dL))
dthdL = (tp-tm)/(2*float(dL))
print('shared   dtheta/dB = %+.5f   dtheta/dL = %+.6f   break-even chain slope s0* = %.4f' % (dthdB, dthdL, dthdL/(-dthdB)))
