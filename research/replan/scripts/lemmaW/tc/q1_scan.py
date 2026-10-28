import sys, time
from fractions import Fraction as Fr
import pr86
cfg = pr86.Cfg()
# fine bisection in units of 1e-9 at h = 8051/10000
def fine(cfg, lo_u, hi_u, unit=10**9):
    # lo fails, hi passes (units of 1/unit)
    assert not pr86.certifiable(cfg.copy(th=Fr(lo_u, unit)))
    assert pr86.certifiable(cfg.copy(th=Fr(hi_u, unit)))
    while hi_u - lo_u > 1:
        mid = (lo_u + hi_u)//2
        if pr86.certifiable(cfg.copy(th=Fr(mid, unit))): hi_u = mid
        else: lo_u = mid
    return hi_u
t = fine(cfg, 873955700, 873955800)
print('fine theta* at h=0.8051: %d/1e9 = %.9f' % (t, t/1e9))
# h scan
for hnum in [8040, 8044, 8046, 8048, 8050, 8051, 8052, 8054, 8056, 8058, 8059, 8060]:
    c2 = cfg.copy(h=Fr(hnum, 10000))
    t = pr86.theta_star(c2, anchor=8739700)
    print('h=%s  theta*=%s  (%s)' % (hnum/10000, None if t is None else '%.7f' % (t/1e7), None if t is None else pr86.report(c2, t)), flush=True)
