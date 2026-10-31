"""The source theta's main energy against the source length L, rows fixed.

For the class-signed source theta f (theta_util.class_signed_fit, unit norm, refitted at each L) it prints |E f|^2,
the same for the masked random matrix on E's zero pattern (mean of 4 seeds), and their difference, the main energy.
The residue picture (E f = L^{1/3} conj tau6 + noise, theta_src_residue.py) predicts main energy proportional to
|f|^{-2} sum_x N(x)^{-2/3} L^{2/3} ~ L^{1/3} at fixed B; a plain L^{1/2} law is printed for comparison.

usage: python3 -I theta_src_lscale.py B L1,L2,...
"""
import os, sys, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import theta_util as tu, theta_core as tc, theta_ckernel as ck
B = int(sys.argv[1])
for L in [int(t) for t in sys.argv[2].split(',')]:
    A = tu.load_all(B, L, 2)
    F, R, S = A.F, A.R, A.S
    base, Xn = tu.class_signed_fit(A)
    EX = F.E @ Xn
    G = EX.conj().T @ EX
    w, V = np.linalg.eigh((G + G.conj().T) / 2)
    f = Xn @ V[:, -1]
    ray = w[-1]                        # |E f|^2 / |f|^2, f unit
    # noise level: the same f against the masked random matrix
    Tb = tc.build_tables(B, L, verbose=False)
    K = ck.Kernel(Tb.T, Tb.LOC, nthreads=2)
    noise = float(np.mean([np.linalg.norm(K.forward(f[:, None], mode=1, seed=s)) ** 2 for s in range(4)]))
    main = ray - noise
    print('B=%d L=%d R=%d S=%d: |Ef|^2 %.1f, masked-null |Ef|^2 %.1f, main %.1f, main/L^(1/3) %.2f, main/L^(1/2) %.2f'
          % (B, L, R, S, ray, noise, main, main / L ** (1 / 3), main / L ** 0.5), flush=True)
