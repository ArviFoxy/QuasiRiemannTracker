# Spectral tests of P1 in the Z[omega] model.
# usage: python3 exp_spectral.py K N L [seed]
import sys, os, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from build import load
W = np.exp(2j * np.pi / 3)

K, N, L = map(int, sys.argv[1:4]); seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
rng = np.random.default_rng(seed)
d = load(K, N, L, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data'))
Phi = d['Phi'].astype(float); gt = d['gt']; Xe = d['Xe']; lam = d['lam']; markN = d['markN']
Kp, Np = Phi.shape; Lp = Xe.shape[1]
X = np.where(Xe < 0, 0, W ** np.where(Xe < 0, 0, Xe))          # (n/P)_3  (the slot twist chi_P(n)^{-2})
print(f'K={K} N={N} L={L}: rows K\'={Kp} cols N\'={Np} marks L\'={Lp}   K\'/N\'={Kp/Np:.4f}  N\'/K\'={Np/Kp:.1f}')
Phi2 = Phi ** 2

# orthonormal basis of V = span of the quadratic rows on the column set
QV, _ = np.linalg.qr(Phi.T)                                      # N' x K'

def report(c, name):
    v = Phi @ c
    S = np.sum(np.abs(v) ** 2)
    diag = np.sum(Phi2 @ (np.abs(c) ** 2))
    nc = np.sum(np.abs(c) ** 2)
    proj = np.sum(np.abs(QV.conj().T @ c) ** 2) / nc
    print(f'  {name:34s} |Phi c|^2/Diag={S/diag:7.3f}  ||P_V c||^2/||c||^2={proj:.4f} (=K\'/N\' x {proj/(Kp/Np):6.2f})'
          f'  LS/Diag={(Kp+Np)*nc/diag:6.1f}')

A_slot = (X / np.sqrt(markN)[None, :]).sum(1)                   # sum_P q_P^{-1/2} (n/P)_3
A_conj = (X.conj() / np.sqrt(markN)[None, :]).sum(1)
u = np.exp(2j * np.pi * rng.random(Np))
cube = W ** rng.integers(0, 3, Np)
lam13 = np.exp(1j * np.angle(lam) / 3)
print('column-vector tests (P_V = projection on span of quadratic characters):')
report(gt, 'g~')
report(gt.conj(), 'conj g~')
report(lam13 * cube, 'lam^(1/3) * random cube root')
report(u, 'random phases')
report(gt * A_slot, 'g~ * A  (A=sum_P q^-1/2 (n/P)_3)')
report(gt * A_conj, 'g~ * conj-orientation A')
report(u * A_slot, 'random * A')
report(Phi[Kp // 2], 'aligned (n/k0)_2')

# ---- the K' x L' matrix S(k,P) = sum_n g~(n) (n/k)_2 (n/P)_3 ----
def mat_stats(S, name):
    sv = np.linalg.svd(S, compute_uv=False)
    fro2 = np.sum(sv ** 2); op2 = sv[0] ** 2
    mp = Np * (math.sqrt(Kp) + math.sqrt(Lp)) ** 2              # random-matrix scale
    print(f'  {name:26s} ||S||_op^2/(N\'(sqrtK\'+sqrtL\')^2)={op2/mp:6.3f}  ||S||_F^2/(K\'L\'N\')={fro2/(Kp*Lp*Np):6.3f}'
          f'  stable rank={fro2/op2:6.2f} (L\'={Lp})  op2/Fro2={op2/fro2:.3f}')
    return sv
print('matrix S = Phi diag(beta) X  (K\' x L\'):')
sv_g = mat_stats(Phi @ (gt[:, None] * X), 'beta=g~, slot (n/P)_3')
mat_stats(Phi @ (gt[:, None] * X.conj()), 'beta=g~, conj slot')
mat_stats(Phi @ (u[:, None] * X), 'beta=random phase')
G = (rng.standard_normal((Kp, Lp)) + 1j * rng.standard_normal((Kp, Lp))) * math.sqrt(Np / 2)
mat_stats(G, 'iid Gaussian (variance N\')')
# aligned adversary: beta chosen to maximise ||S||_op: beta = conj(top direction) -- shows N-term attainable
Sal = Phi @ ((Phi[0] * np.conj(X[:, 0]))[:, None] * X)
mat_stats(Sal, 'adversarial beta=(n/k0)conj(n/P0)')

# ---- principal angles between V (dim K') and W = g~ . span{(n/P)_3} (dim L') ----
QW, _ = np.linalg.qr(gt[:, None] * X)
cos = np.linalg.svd(QV.conj().T @ QW, compute_uv=False)
pred = (math.sqrt(Kp / Np) + math.sqrt(Lp / Np)) ** 2
Qr, _ = np.linalg.qr(rng.standard_normal((Np, Lp)) + 1j * rng.standard_normal((Np, Lp)))
cosr = np.linalg.svd(QV.conj().T @ Qr, compute_uv=False)
print(f'principal angles V vs W: max cos^2={cos[0]**2:.4f}, mean cos^2={np.mean(cos**2):.4f};'
      f' random W: max {cosr[0]**2:.4f} mean {np.mean(cosr**2):.4f}; MP edge {pred:.4f}; K\'/N\'={Kp/Np:.4f}')

# ---- single-mark ratios F_P / Diag_P ----
r = []
for j in range(Lp):
    c = gt * X[:, j]
    r.append(np.sum(np.abs(Phi @ c) ** 2) / np.sum(Phi2 @ (np.abs(c) ** 2)))
r = np.array(r)
print(f'single-mark F_P/Diag_P over {Lp} marks: mean {r.mean():.3f}  min {r.min():.3f}  max {r.max():.3f}')
