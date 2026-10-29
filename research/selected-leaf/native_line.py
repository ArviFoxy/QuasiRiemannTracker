"""E5. The native line with the selected-norm leaf (K = 1/2 + eta instead of 3/4).

New leaf price (derived; see JOURNAL E5): rows whose retained slots contain a subset of slope > 1/2 are priced by
PR 93's selected all-source norm, (PC + s - H)_+; all other rows delete slots at cost (1/2 + eta) per unit width.
The cube-free ledger price <= u then reduces to Sil's native gates with nativeK -> K = 1/2 + eta, plus
a <= (L - 1)/4 for the selected branch.  This script runs the native line in the continuum limit from PR 76's
fourth-power source G(99999/100000, 93/25, 3/50): B constant, the minimal selection a per step and the largest
cap allowed by the cap gate, until a gate fails.  [numerical]"""
import sys
import numpy as np

def run(K, B=0.99999, L0=3.72, c0=0.06, h=1e-5, verbose=False):
    L, c = L0, c0
    path = [(L, c, 0.0)]
    while True:
        Ln = L - h
        den = L * (1 + K) - 6 * K * B           # overshoot: positive
        if den <= 0:
            reason = 'overshoot'; break
        a = K * h / den * (1 + 1e-9)            # minimal selection fraction (retention)
        if a > (Ln - 1) / 4:
            reason = 'selected branch a <= (L-1)/4'; break
        cn = c / (1 - a + 6 * a * c) * (1 - 1e-12)   # largest cap allowed by the cap gate
        ok = {'principal': Ln - 2 - 4.5 * a > 0, 'diagonal': Ln - 1 - 4 * a > 0,
              'secondRef': 1.5 * Ln - 2.5 - 4.5 * a > 0, 'refPos': 1 / 6 - (1 + 1.5 * a) * cn > 0,
              'H': 1 - 6 * a * cn > 0, 'cap_lt': c < 1 / 6}
        bad = [k for k, v in ok.items() if not v]
        if bad:
            reason = ','.join(bad); break
        L, c = Ln, cn
        path.append((L, c, a))
    return L, c, reason, path

if __name__ == '__main__':
    for K in (0.75, 0.5 + 1e-3, 0.5 + 1e-4):
        L, c, reason, path = run(K)
        print('K=%.4f  native line ends at L=%.5f with cap c=%.5f  (stops: %s)' % (K, L, c, reason), flush=True)
        for Lq in (3.0, 2.5715, 2.4, 2.2, 2.1, 2.05):
            pts = [p for p in path if abs(p[0] - Lq) < 6e-6]
            if pts:
                print('    L=%.4f  cap=%.5f  a=%.2e' % pts[0], flush=True)
