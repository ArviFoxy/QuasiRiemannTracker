"""One column-branch saving e (Z units) used in all places where the hybrid norm / Lemma 17.1 diagonal range binds:
   probe:   x + y <= 1 - ell + e                      (Lean: compensated_reflected_exponent_with_length, hH)
   I line:  r + 2z <= 1 + e/h                         (Lean: original_source_energy, first width condition)
   L line:  Lemma 17.1 at z=0 reaches D <= H Z^e, so H = D Z^-e in Lemma 17.6:  L(t) -> L(t) - (5/6) e/h    [inference: z = 0 case]
Needed e for the bar, scenarios A and B."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pm import *
def mk(s, e, probe=1, inv=1, lng=0):
    m = scenario(s)
    m.eE = probe*e; m.eI = inv*e/0.8054; m.sL = lng*(5/6)*e/0.8054
    return m
for s in 'AB':
    print('scenario %s (gap %+.3e):' % (s, scenario(s).theta_star() - BAR))
    for label, kw in (('probe only', dict(probe=1, inv=0, lng=0)), ('inverse line only', dict(probe=0, inv=1, lng=0)),
                      ('long line only (z=0 diagonal range)', dict(probe=0, inv=0, lng=1)),
                      ('probe + inverse', dict(probe=1, inv=1, lng=0)), ('probe + inverse + long', dict(probe=1, inv=1, lng=1))):
        e = brentq(lambda e: mk(s, e, **kw).theta_star() - BAR, 0, 3e-3, xtol=1e-13)
        print('   %-38s e_Z needed = %.4e' % (label, e))
