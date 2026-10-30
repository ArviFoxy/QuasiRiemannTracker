"""Exact check of the E5Gates (research/lean/arvi_selected_leaf/Gates.lean) along the line
c(L) = 1/10 + (3/50)(5143/2000 - L), B = 99999/100000, for an end Lend, selected fraction a, cut K, step h0.
Each gate is monotone in (L0, L) on the line, so it is checked at the worst corner (and on a grid as a cross-check)."""
from fractions import Fraction as Fr
B = Fr(99999, 100000)
cap = lambda L: Fr(1, 10) + Fr(3, 50) * (Fr(5143, 2000) - L)
def gates(L0, L, a, K):
    pc, nc = cap(L0), cap(L)
    return dict(
        retention=a - K * (L0 - L + (6 * B - L0) * a) / L0,
        cap=pc * (1 - 6 * a * nc) - (1 - a) * nc,
        principal=L - 2 - Fr(9, 2) * a,
        diagonal=L - 1 - 4 * a,
        secondRef=Fr(3, 2) * L - Fr(5, 2) - Fr(9, 2) * a,
        refPos=Fr(1, 6) - (1 + Fr(3, 2) * a) * nc,
        H=1 - 6 * a * nc,
        overshoot=1 - K * (6 * B - L0) / L0,
        cap_lt=Fr(1, 6) - pc,
        K_le=Fr(3, 4) - K)
def check(Lend, a, K, h0, n=2000):
    top = Fr(5143, 2000)
    worst = {}
    pts = [Lend + (top - Lend) * Fr(i, n) for i in range(n + 1)]
    for L0 in pts:
        for L in (max(Lend, L0 - h0), max(Lend, L0 - h0 / 2)):
            if not L < L0: continue
            for k, v in gates(L0, L, a, K).items():
                if k not in worst or v < worst[k][0]: worst[k] = (v, float(L0))
    # the binding corner exactly
    for k, v in gates(Lend + h0, Lend, a, K).items():
        if v < worst[k][0]: worst[k] = (v, float(Lend + h0))
    ok = all(v[0] > 0 for v in worst.values())
    return ok, {k: (float(v[0]), v[1]) for k, v in worst.items()}
for (Lend, a, K, h0) in [(Fr(101, 50), Fr(1, 250), Fr(501, 1000), Fr(1, 100000)),
                         (Fr(401, 200), Fr(1, 1000), Fr(501, 1000), Fr(1, 200000)),
                         (Fr(4009, 2000), Fr(1, 1000), Fr(501, 1000), Fr(1, 1000000)),
                         (Fr(20001, 10000), Fr(1, 100000), Fr(500001, 1000000), Fr(1, 250000000)),
                         (Fr(2001, 1000), Fr(1, 10000), Fr(5001, 10000), Fr(1, 10000000))]:
    ok, w = check(Lend, a, K, h0)
    print('Lend %s (%.5f) a=%s K=%s h0=%s: all gates %s' % (Lend, float(Lend), a, K, h0, 'PASS' if ok else 'FAIL'))
    print('    tightest:', sorted(((v[0], k) for k, v in w.items()))[:3])
