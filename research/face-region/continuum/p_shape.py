"""On the chain-relevant set: per facet, (a) max dphi/dp (decreasing iff <= 0), (b) max phi'' (concave iff <= 0),
(c) is phi_k(p) >= min(phi_k(0), phi_k(1/2)) (endpoint property per facet)."""
import numpy as np
from vec import phis_vec, sample
rng = np.random.default_rng(33)
P = np.linspace(0, 0.5, 801)[None, :]
dp = P[0, 1] - P[0, 0]
stats = {k: [-np.inf, -np.inf, -np.inf] for k in range(6)}
for batch in range(25):
    s = sample(4000, rng)
    F = phis_vec(s['nu'][:, None], P, s['B0'][:, None], s['L0'][:, None], 0.1, s['S'][:, None], s['Q'][:, None])
    d1 = np.diff(F, axis=1)/dp
    d2 = (F[:, 2:] - 2*F[:, 1:-1] + F[:, :-2])/dp**2
    endmin = np.minimum(F[:, 0, :], F[:, -1, :])
    viol = endmin - F.min(axis=1)
    for k in range(6):
        stats[k][0] = max(stats[k][0], d1[:, :, k].max())
        stats[k][1] = max(stats[k][1], d2[:, :, k].max())
        stats[k][2] = max(stats[k][2], viol[:, k].max())
for k in range(6):
    print('facet %d (i,j)=(%d,%d): max dphi/dp = %+.3e   max phi\'\' = %+.3e   max endpoint violation = %.2e' % (k, *divmod(k, 3), *stats[k]))
