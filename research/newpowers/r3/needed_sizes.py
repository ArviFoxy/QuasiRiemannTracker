"""Needed size of every return-side lever to reach the bar 0.8739358, scenarios A (73/38, floor 0.60) and B (46/38, PR 86 chain).
All numbers are PM (pm.py) = exact toolchain to <= 4e-9 for these sizes.  New levers: eE, eI, joint, wL, sPl."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pm import *

def row(name, lever, lo, hi, scale=1.0, **fixed):
    out = []
    for s in 'AB':
        v = needed(s, lever, lo, hi, **fixed)
        out.append(v)
    return out

if __name__ == '__main__':
    print('base: A %.9f (gap %+.3e)  B %.9f (gap %+.3e)' % (scenario('A').theta_star(), scenario('A').theta_star() - BAR,
                                                           scenario('B').theta_star(), scenario('B').theta_star() - BAR))
    print()
    print('%-34s %-14s %-14s' % ('lever (value at which theta* = bar)', 'scenario A', 'scenario B'))
    A = lambda lever, lo, hi, **f: needed('A', lever, lo, hi, **f)
    B = lambda lever, lo, hi, **f: needed('B', lever, lo, hi, **f)
    rows = [
     ('dE  additive change of E', 'dE', -2e-3, 0),
     ('dR  count lowered', 'dR', 0, 2e-3),
     ('dC  capacity added', 'dC', 0, 5e-3),
     ('cI  inverse slot cost (2)', 'cI', 1.9, 2.0),
     ('kL  long-line slope (5/6)', 'kL', 0.78, 5/6),
     ('eps  halving 1/2 -> 1/2+eps', 'eps_half', 0, 0.05),
     ('eE  probe column excess (Z units)', 'eE', 0, 2e-3),
     ('eI  inverse column excess (U units)', 'eI', 0, 5e-3),
     ('wL  fourth-power width, long line (U)', 'wL', 0, 0.03),
    ]
    for label, lever, lo, hi in rows:
        a, b = A(lever, lo, hi), B(lever, lo, hi)
        print('%-34s %-14.8g %-14.8g' % (label, a, b))
    # derived equivalents
    print()
    for s in 'AB':
        m = scenario(s)
        t = m.theta_star(); b = m.binding()
        print(s, 'binding point:', {k: round(v, 6) for k, v in b.items()})
    # joint column excess e (Z units): probe gets e, inverse line gets e/h
    def joint(s):
        def g(e):
            m = scenario(s); m.eE = e; m.eI = e / 0.8054
            return m.theta_star() - BAR
        return brentq(g, 0, 3e-3, xtol=1e-12)
    print()
    print('joint column excess e (probe: x+y=1-ell+e ; inverse: r+2z<=1+e/h):  A %.4e   B %.4e' % (joint('A'), joint('B')))
    for s in 'AB':
        eE_only = needed(s, 'eE', 0, 2e-3); eI_only = needed(s, 'eI', 0, 5e-3)
        print(s, ' single: eE %.4e ; eI %.4e (=> e_Z %.4e)' % (eE_only, eI_only, eI_only * 0.8054))
    # theta shift per unit of each lever (linear regime), both scenarios
    print()
    print('theta shift per unit lever:')
    for s in 'AB':
        t0 = scenario(s).theta_star()
        for lever, step in (('dE', -1e-5), ('dR', 1e-5), ('dC', 1e-4), ('cI', 2 - 1e-3), ('kL', 5/6 - 1e-3), ('eps_half', 1e-3),
                            ('eE', 1e-4), ('eI', 1e-4), ('wL', 1e-3)):
            m = scenario(s); setattr(m, lever, step)
            base = {'cI': 2.0, 'kL': 5/6}.get(lever, 0.0)
            print('  %s %-9s d(theta)/d(lever) = %+.4e' % (s, lever, (m.theta_star() - t0) / (step - base)))
