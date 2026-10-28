"""Price tables (PM, calibrated to the exact toolchain) used in R3_return.md."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pm import *
t0 = {s: scenario(s).theta_star() for s in 'AB'}
def row(label, mk):
    out = []
    for s in 'AB':
        m = scenario(s); mk(m); out.append(m.theta_star() - t0[s])
    print('  %-46s dtheta A %+.3e (gap %+.2e) | B %+.3e (gap %+.2e)' % (label, out[0], out[0] + t0['A'] - BAR, out[1], out[1] + t0['B'] - BAR))
print('base: A %.9f (gap %+.3e)  B %.9f (gap %+.3e)\n' % (t0['A'], t0['A'] - BAR, t0['B'], t0['B'] - BAR))
print('== long line, supply-limited fourth-power width w (units of log U; Z-units = w*h; pure fourth powers: w=(t-1)/4=0.0357)')
for w in (1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3.57e-2):
    row('w = %.1e' % w, lambda m, w=w: setattr(m, 'wL', w))
print('\n== diagonal-range extension e_Z (Lemma 17.1 at z=0 reaches D <= H Z^e):  L(t) -> L(t) - (5/6) e/h')
for e in (5e-5, 1e-4, 2e-4, 5e-4):
    row('long line only, e_Z = %.1e' % e, lambda m, e=e: setattr(m, 'sL', 5 / 6 * e / 0.8054))
print('\n== column excess in the probe (x+y = 1-ell+e), inverse line (r + 2z <= 1 + e/h), joint')
for e in (5e-5, 1e-4, 1.3e-4, 2e-4, 3e-4):
    row('probe only e_Z = %.1e' % e, lambda m, e=e: setattr(m, 'eE', e))
    row('inverse only e_Z = %.1e' % e, lambda m, e=e: setattr(m, 'eI', e / 0.8054))
    def j(m, e=e):
        m.eE = e; m.eI = e / 0.8054
    row('probe + inverse e_Z = %.1e' % e, j)
print('\n== halving: selected slots save (1/2+eps) delta p C; doubled-slot discount eta = 4 eps/(1+2 eps)')
for eps in (0.001, 0.003, 0.0046, 0.01):
    row('eps = %.4f (eta = %.4f)' % (eps, 4 * eps / (1 + 2 * eps)), lambda m, eps=eps: setattr(m, 'eps_half', eps))
print('\n== slot costs')
for ci in (1.999, 1.997, 1.995, 1.99):
    row('c_I = %.3f' % ci, lambda m, ci=ci: setattr(m, 'cI', ci))
for kl in (0.833, 0.832, 0.831, 0.83):
    row('k_L = %.3f' % kl, lambda m, kl=kl: setattr(m, 'kL', kl))
print('\n== how far can the C branch go before another edge binds?  (old-branch edges saturate near 0.87364 per lemmaW s4.3)')
