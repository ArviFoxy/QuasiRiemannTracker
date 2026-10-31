"""Do the row images of the source theta on disjoint source windows point the same way?

The source theta f(x) = A(x mod 4) lam3(x) eps(x) conj g6(x) N(x)^{-1/3} (theta_util.class_signed_fit fits the twelve
class phases A on the dense matrix) is fixed in advance, so this test has no eigenvector threshold.  Split the
sources into disjoint dyadic windows W of N(x) and form the row images w_W = E (f 1_W).  If E f carries a residue --
a main term in a fixed row direction built up over every scale of x -- the w_W are correlated with each other, about
like the product of their signal fractions.  If the outlier is not built that way, |<w_W, w_W'>|^2 / (|w_W|^2 |w_W'|^2)
sits near 1/R.  The same is computed for the masked random matrix on the same zero pattern (mode 1) with the same f,
and for f with its class phases replaced by random ones.

usage: python3 -I theta_src_coherence.py B L nwin
"""
import os, sys, time
sys.dont_write_bytecode = True
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_util as tu          # noqa: E402
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2]); nwin = int(sys.argv[3])
A = tu.load_all(B, L, 4)
F, R, S = A.F, A.R, A.S
base, Xn = tu.class_signed_fit(A)
# best class phases: the top eigenvector of the compressed source Gram on the twelve class columns
EX = F.E @ Xn
G = EX.conj().T @ EX / R
w, V = np.linalg.eigh((G + G.conj().T) / 2)
coef = V[:, -1]
f = Xn @ coef
print('B=%d L=%d: class-signed source theta, Rayleigh %.3f S (top of the 12-class compression)' % (B, L, w[-1] * R / S))
Tb = tc.build_tables(B, L, verbose=False)
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=3)
SN = F.SN.astype(float)
wins = [(L / 2 ** j, L / 2 ** (j - 1)) for j in range(1, nwin + 1)]
rng = np.random.default_rng(11)
frand = Xn @ (np.exp(2j * np.pi * rng.random(Xn.shape[1])) * np.abs(coef))


def images(vec, mode):
    cols = np.stack([vec * ((SN > lo) & (SN <= hi)) for lo, hi in wins], axis=1)
    out = np.zeros((R, len(wins)), complex)
    for st in range(0, len(wins), 8):
        out[:, st:st + 8] = K.forward(cols[:, st:st + 8], mode=mode, seed=9)
    return out


def corr(Wm):
    n = Wm / np.linalg.norm(Wm, axis=0, keepdims=True)
    return np.abs(n.conj().T @ n) ** 2


for name, vec, mode in (('E, source theta', f, 0), ('masked null, source theta', f, 1),
                        ('E, random class phases', frand, 0)):
    C = corr(images(vec, mode))
    off = C[~np.eye(len(wins), dtype=bool)]
    print('%-28s mean off-diagonal |corr|^2 %.4f (random level %.1e); adjacent windows %s'
          % (name, off.mean(), 1.0 / R, np.round([C[i, i + 1] for i in range(len(wins) - 1)], 3)), flush=True)
print('windows: %s' % ', '.join('(%.0f, %.0f]' % w_ for w_ in wins))
