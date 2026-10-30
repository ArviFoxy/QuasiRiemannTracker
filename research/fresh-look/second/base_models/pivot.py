# closed-form 3-word count (p=1/2, B=1, Lambda=c=2): compare long-slope parametrizations
from scipy.optimize import brentq
def R(d, s, pivot1=True):
    F1 = lambda t: 1 - d/2 - d*t/3
    L = (lambda t: 1 - d + (s-d)*(t-1)) if pivot1 else (lambda t: 1/6 + (s-d)*t)
    t = brentq(lambda t: F1(t) - L(t), 0.5, 3); return F1(t), t
for d in (0.426, 0.453):
    r0, t0 = R(d, 5/6)
    for s in (0.8328, 0.8283, 0.8218):
        r1, _ = R(d, s, True); r2, _ = R(d, s, False)
        print('d %.3f s %.4f: dR pivot1 %+.2e   dR pivot0 %+.2e   (t* %.4f)' % (d, s, r1-r0, r2-r0, t0))
