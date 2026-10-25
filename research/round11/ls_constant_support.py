#!/usr/bin/env python3
"""Round 11 step 3: large-sieve constant of the actual sextic family for different column supports.

Delta(support) = sigma_max(Psi)^2 where Psi[u, n] = psi_u(n) = (u/n)_6, rows u primary squarefree
N(u) in [U, 2U), columns n in the support with N(n) in [N, 2N) (flat weights).
Compared with the random-matrix edge (sqrt(R) + sqrt(C))^2 and with the 'Gauss-bias' scale
(R*C)^{2/3} from the general sextic sieve.
Supports: (i) split prime ideals, (ii) squarefree ideals with all prime factors > z (rough),
(iii) all squarefree ideals.
Question: is sub-problem (A) (no Gauss bias for prime-product vectors up to length U) visibly true?
"""
import sys, os, time, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'round7', 'large-values'))
from sextic_gram import build, column_ideals, psi_matrix


def top_sv2(Psi):
    R, C = Psi.shape
    G = Psi @ Psi.conj().T if R <= C else Psi.conj().T @ Psi
    return float(np.linalg.eigvalsh(G)[-1])


def main(U, ys, zexp=0.3):
    Ns = [int(round(U**y)) for y in ys]
    rows, K, pid, pindex, P = build(U, Ns)
    R = len(rows)
    print(f"U={U} rows R={R}", flush=True)
    z = U**zexp
    for y, N in zip(ys, Ns):
        cols = column_ideals(N, pid, pindex, P)
        sq = [c for c in cols if all(e == 1 for (_, e) in c[1])]
        pr = [c for c in sq if len(c[1]) == 1 and pid[c[1][0][0]][1] >= 0]
        rough = [c for c in sq if all(pid[i][0] > z for (i, _) in c[1])]
        out = []
        for name, cc in (("prime", pr), ("rough", rough), ("sqfree", sq)):
            if len(cc) < 5:
                out.append(f"{name}: C={len(cc)} (skip)")
                continue
            Psi = psi_matrix(K, cc)
            d = top_sv2(Psi)
            C = len(cc)
            edge = (np.sqrt(R) + np.sqrt(C))**2
            bias = (R*C)**(2/3)
            out.append(f"{name}: C={C} Delta/edge={d/edge:.3f} Delta/max(R,C)={d/max(R,C):.3f} "
                       f"bias/edge={bias/edge:.2f}")
        print(f"y={y:.3f} N={N}: " + " | ".join(out), flush=True)


if __name__ == "__main__":
    U = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    ys = [float(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else [0.5, 0.7, 0.85, 1.0, 1.155]
    main(U, ys)
