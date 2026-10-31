"""Q1 control: the dual-frame bounds of diagonal metrics against the free-probability edge of their weights.

For a diagonal row metric Q = diag(q), (1/S) E^H Q E = sum_z (q_z/S) e_z e_z^H with e_z the rows of E.  If the rows were
independent with iid entries of variance s2, this is a free sum of rank-one pieces, and its top eigenvalue sits at the
edge of the free Poisson law of the weights:
  lambda_+(q) = min_{0 < w < 1 / max a} [ 1/w + (1/S) sum_z a_z / (1 - a_z w) ],   a_z = s2 q_z.
For q = 1_W this is the Marchenko-Pastur edge (1 + sqrt(|W| s2 / S))^2.  The script prints lambda_+(q) and the
single-row lower bound max_z <a_z, E^H Q E a_z> / S at a_z = conj(e_z)/|e_z| for the metrics of theta_ampframe.py, so
the table in theta_ampframe_B10000.log (sextic E) and theta_ampframe_rand_B10000.log (random E on the same zero
pattern) can be read against them.

usage: python3 -I theta_ampfree.py B L [rho] [P0] [model]   (model: 'arith' (default) or 'rand')
"""
import os, sys
sys.dont_write_bytecode = True
import numpy as np
from scipy.optimize import minimize_scalar

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
rho = float(sys.argv[3]) if len(sys.argv) > 3 else 0.1
P0 = int(sys.argv[4]) if len(sys.argv) > 4 else 40
model = sys.argv[5] if len(sys.argv) > 5 else 'arith'
F = tc.build(B, L)
E, R, S, SN, spf = F.E, F.R, F.S, F.SN, F.spf
if model == 'rand':
    _rng = np.random.default_rng(67)                 # the same draw as theta_ampframe.py's control
    E = (np.abs(E) > 0.5) * np.exp(2j * np.pi * _rng.integers(0, 6, size=E.shape) / 6)
s2 = float((np.abs(E) ** 2).mean())                  # entry variance (fraction of nonzero symbols)
sl = np.nonzero((SN >= P0) & (SN <= 2 * P0) & np.array([int(spf[int(n)]) == int(n) for n in SN]))[0]
T0 = E[:, sl].sum(1)
n = max(2, int(rho * R))
W = np.argsort(-np.abs(T0))[:n]
inW = np.zeros(R, bool); inW[W] = True
x = np.abs(T0) ** 2 / (np.abs(T0[W]) ** 2).min()
print('model %s  B=%d  R=%d  S=%d  entry variance %.4f  |W| = %d  slot primes %d' % (model, B, R, S, s2, n, len(sl)))
print('  amplifier x = |T|^2/A: mean %.3f, mean on W %.3f, max %.3f' % (x.mean(), x[W].mean(), x.max()))


def edge(q):
    a = s2 * q[q > 0]
    amax = a.max()
    f = lambda w: 1.0 / w + np.sum(a / (1.0 - a * w)) / S
    r = minimize_scalar(f, bounds=(1e-9 / amax, (1 - 1e-9) / amax), method='bounded',
                        options=dict(xatol=1e-12 / amax))
    return float(r.fun)


def single_row(q):
    z = int(np.argmax(q * (np.abs(E) ** 2).sum(1)))
    a = np.conj(E[z]); a = a / np.linalg.norm(a)
    y = E @ a
    return float(np.sum(q * np.abs(y) ** 2)) / S


def line(q, name):
    c = 1.0 / q[W].min()
    print('  %-40s dynamic range on W %6.2f   free edge x c_W %7.3f   single row x c_W %6.3f'
          % (name, q[W].max() / q[W].min(), c * edge(q), c * single_row(q)), flush=True)


print('  %-40s %s' % ('', '(compare with the lambda column of the theta_ampframe logs)'))
line(inW.astype(float), 'truth (q = 1_W)')
line(np.ones(R), 'trivial Q = I')
line(inW + 0.1, 'oracle P_W + 0.1 I')
line(x, 'single amplifier |T|^2/A')
line(x ** 2, 'squared amplifier')
line(0.5 * x + 0.5, 'half amplifier + half identity')
for al in (0.1, 0.25, 0.75):
    line(al * x + (1 - al), 'mix: %.2f x + %.2f' % (al, 1 - al))
for be in (0.25, 0.5):
    line(x ** be, 'fractional power x^%.2f' % be)
for eta in (0.3, 0.1, 0.03):
    line(np.minimum(x, 1.0) + eta, 'clipped min(x, 1) + %.2f' % eta)
for k in (2, 4):
    line(np.minimum(x, 1.0) ** k + 0.1, 'clipped power min(x, 1)^%d + 0.1' % k)
print('done')
