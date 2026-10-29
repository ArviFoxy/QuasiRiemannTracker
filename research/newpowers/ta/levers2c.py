"""Robust face-side and return-side lever pricing at the stored ODE optimum faces (no secant extrapolation).
usage: python3 levers2c.py GAIN FLOOR BOOT DFAC"""
import sys, os, json
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'tc'))
sys.path.insert(0, HERE)
import exact, best, pr86
import levers_pr86 as LV

TARGET = 0.8739058
gain, floor, boot, dfac = float(sys.argv[1]), float(sys.argv[2]), bool(int(sys.argv[3])), float(sys.argv[4])
r = json.load(open(os.path.join(HERE, 'results', 'e2_ode2_g%g_f%.2f_b%d_d%.3f.json' % (gain, floor, int(boot), dfac))))
C, P = r['C'], r['P']
t0 = exact.theta_exact(C['B'], C['L'], P['B'], P['L'], guess=r['theta'], unit=10**9, span=2000)[0]
g = t0 - TARGET
print('floor %.2f: theta0 = %.9f  gap %+.3e   C(L=%.4f,B=%.6f)  P(L=%.4f,B=%.6f)' % (floor, t0, g, C['L'], C['B'], P['L'], P['B']))
for nm, f in (('B_P', lambda x: exact.theta_exact(C['B'], C['L'], P['B'] + x, P['L'], guess=t0, unit=10**9, span=2000)),
              ('B_C', lambda x: exact.theta_exact(C['B'] + x, C['L'], P['B'], P['L'], guess=t0, unit=10**9, span=2000))):
    pts = []
    for x in (5e-5, 1e-4, 2.5e-4, 5e-4, 1e-3, 2e-3):
        rr = f(x)
        pts.append((x, None if rr is None else rr[0]))
    print('  raise %s by x: ' % nm + ' '.join('%g:%s' % (x, 'fail' if t is None else '%+.2e' % (t - t0)) for x, t in pts) + '   (dtheta/dB at 5e-5: %.3e)' % ((pts[0][1] - t0) / pts[0][0]))
cfg = exact.make_cfg(C['B'], C['L'], P['B'], P['L'])
def th(c):
    rr = best.theta_best(c, unit=10**9, anchor=int(round((t0 + 4e-6) * 1e9)), lo=int(round((t0 - 6e-5) * 1e9)), step=1000, maxstep=120)
    return None if rr is None else rr[0] / 1e9
LV.set_lev(); tb = th(cfg)
print('  [return-side, exact] base %.9f' % tb)
for name, key, x1 in (('E exponent', 'dE', Fr(-1, 100000)), ('return count R (all improved branches)', 'dR', Fr(1, 10000)), ('capacity C_N', 'dC', Fr(1, 1000))):
    LV.set_lev(**{key: x1}); t1 = th(cfg); LV.set_lev()
    sl = (tb - t1) / float(abs(x1))
    need = g / sl
    print('    %-38s slope %.4e per unit  -> size to move the gap to zero: %.3e   (sign: %s)' % (name, sl, need, 'improve by' if need > 0 else 'can worsen by'), flush=True)
