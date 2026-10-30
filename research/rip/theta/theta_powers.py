"""Which row vectors carry the theta excess: Gauss-sum powers and plain rows.

For row vectors c = phi(z) chi_z(u) profile(z) with phi = 1 (plain), conj G, G, conj G^2, G^2, conj G^3 and each of
the six unit twists u, the script prints the dual energy ratio r(c) = |E^T c|^2/(S |c|^2) against random-phase rows
with the same profile.  The Kubota series of g~^j for j >= 2 carry angular Hecke twists (Davenport-Hasse:
g(chi)^2 = J(chi,chi) g(chi^2)), so only conj G is expected to show the Patterson excess.

usage: python3 -I theta_powers.py B L
"""
import os, sys
sys.dont_write_bytecode = True
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
F = tc.build(B, L)
E, R, S, rows, Grow, unit_tw = F.E, F.R, F.S, F.rows, F.Grow, F.unit_tw
prof = (rows['N'] / B) ** -0.5


def r(c):
    v = E.T @ c
    return float(np.vdot(v, v).real / (S * np.vdot(c, c).real))


rng = np.random.default_rng(3)
rb = [r(np.exp(2j * np.pi * rng.random(R)) * prof) for _ in range(12)]
print('random phases: r = %.3f +- %.3f' % (np.mean(rb), np.std(rb)))
phis = [('plain', np.ones(R)), ('conj G', np.conj(Grow)), ('G', Grow), ('conj G^2', np.conj(Grow) ** 2),
        ('G^2', Grow ** 2), ('conj G^3', np.conj(Grow) ** 3)]
print('unit  ' + ''.join('%-10s' % n for n, _ in phis))
for k in range(6):
    print('u%d    ' % k + ''.join('%-10.3f' % r(phi * unit_tw[:, k] * prof) for _, phi in phis))
