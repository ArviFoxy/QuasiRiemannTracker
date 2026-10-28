"""Calibrate the pointwise model (pm.py) against the EXACT Bernstein-cover toolchain (tc/, = lemmaW).
Reference numbers are the exact outputs of lemmaW.md s3.3/s4.1 and logs/levers_price.log (exact rational covers, 1e-9 bisection)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pm import *

EXACT_BASE = {'B': 0.873954831, 'A': 0.873946275}
EXACT_SHIFT = {   # theta* shift of the lever, exact (levers_price.log)
 'B': {'dE=-1e-5': -2.154e-6, 'dE=-1e-4': -2.152e-5, 'dR=1e-4': -1.300e-5, 'dC=+1e-3': -2.377e-5, 'cI=1.995': -9.080e-6,
       'cI=1.99': -1.822e-5, 'cI=1.9': -1.930e-4, 'kL=0.83': -1.740e-5, 'kL=0.82': -7.031e-5, 'kL=0.80': -1.794e-4},
 'A': {'dE=-1e-5': -2.144e-6, 'dE=-1e-4': -2.143e-5, 'dR=1e-4': -1.294e-5, 'dC=+1e-3': -2.376e-5, 'cI=1.995': -8.930e-6,
       'cI=1.99': -1.792e-5, 'cI=1.9': -1.899e-4, 'kL=0.83': -1.733e-5, 'kL=0.82': -7.002e-5, 'kL=0.80': -1.787e-4}}
LEV = {'dE=-1e-5': dict(dE=-1e-5), 'dE=-1e-4': dict(dE=-1e-4), 'dR=1e-4': dict(dR=1e-4), 'dC=+1e-3': dict(dC=1e-3),
       'cI=1.995': dict(cI=1.995), 'cI=1.99': dict(cI=1.99), 'cI=1.9': dict(cI=1.9), 'kL=0.83': dict(kL=0.83),
       'kL=0.82': dict(kL=0.82), 'kL=0.80': dict(kL=0.80)}

if __name__ == '__main__':
    worst = 0.0
    for s in 'BA':
        t0 = scenario(s).theta_star()
        print('scenario %s: PM theta* = %.9f  exact %.9f  diff %+.1e' % (s, t0, EXACT_BASE[s], t0 - EXACT_BASE[s]))
        for name, kw in LEV.items():
            t = scenario(s, **kw).theta_star()
            d = (t - t0) - EXACT_SHIFT[s][name]
            worst = max(worst, abs(d))
            print('   %-10s PM shift %+.3e   exact %+.3e   diff %+.1e' % (name, t - t0, EXACT_SHIFT[s][name], d))
    print('worst |PM - exact| over the 20 lever prices: %.1e' % worst)
