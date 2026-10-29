import numpy as np
from vec import phis_vec, sample
rng = np.random.default_rng(21)
P = np.linspace(0, 0.5, 1001)[None, :]
worst = -np.inf; info = None; total = 0
for batch in range(40):
    s = sample(4000, rng)
    F = phis_vec(s['nu'][:, None], P, s['B0'][:, None], s['L0'][:, None], 0.1, s['S'][:, None], s['Q'][:, None])  # (n, P, 6)
    mins = F.min(axis=(1, 2))
    ends = np.minimum(s['S'], F[:, -1, :].min(axis=1))
    gap = ends - mins
    total += len(gap)
    j = int(np.argmax(gap))
    if gap[j] > worst:
        worst = gap[j]
        Fi = F[j]; pi, k = np.unravel_index(Fi.argmin(), Fi.shape)
        info = {key: round(float(val[j]), 6) for key, val in s.items()}; info['p*'] = float(P[0, pi]); info['k*'] = int(k)
print(total, 'samples; max[min(endpoint values) - min over p] = %.3e' % worst)
print(info)
