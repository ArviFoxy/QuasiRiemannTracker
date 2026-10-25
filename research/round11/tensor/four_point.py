# The fully off-diagonal 4-point sector of tr((SS*)^2) against its Cauchy-Schwarz bound, and the
# 2-point sectors against their Frobenius prediction (round 11, tensor route).
#   oooo = tr((Bt_o A_o)^2),  CS bound = ||Bt_o A_o||_F^2 = tr(Bt_o^2 A_o^2).
#   2-point sectors (exactly one diagonal propagator, or two adjacent ones): predicted by
#   ||S||_F^2 - (diagonal of the second moment), weighted by K, L, N.
# usage: python3 four_point.py K N L [nrandom]
import sys, os, math, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../round7/signal-processing'))
from build import load
W = np.exp(2j * np.pi / 3)
K, N, L = map(int, sys.argv[1:4]); nr = int(sys.argv[4]) if len(sys.argv) > 4 else 2
d = load(K, N, L, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data'))
Phi = d['Phi'].astype(np.float64); gt = d['gt']; Xe = d['Xe']
X = np.where(Xe < 0, 0, W ** np.where(Xe < 0, 0, Xe)).astype(np.complex128)
Kp, Np = Phi.shape; Lp = X.shape[1]
print(f'K={K} N={N} L={L}: K\'={Kp} N\'={Np} L\'={Lp}  N\'/(K\'L\')={Np/(Kp*Lp):.3f}', flush=True)
A = Phi.T @ Phi; Ad = np.diag(A).copy(); np.fill_diagonal(A, 0.0)          # A now = A_o
B = X @ X.conj().T; Bd = np.real(np.diag(B)).copy(); np.fill_diagonal(B, 0.0)  # B now = B_o

def run(beta, name):
    Bo = (beta[:, None] * B) * beta.conj()[None, :]
    M = Bo @ A                                   # Bt_o A_o
    oooo = np.real(np.sum(M * M.T))              # tr(M^2)
    cs = np.real(np.sum(np.abs(M) ** 2))         # ||M||_F^2
    # two-point sectors: one diagonal propagator
    # d on Bt (n1=n2): tr(Bd A_o Bt_o A_o) = sum_n Bd[n] (A_o Bt_o A_o)[n,n]
    AM = A @ M.T.conj().T if False else None
    t_dooo = np.real(np.sum(Bd * np.einsum('ij,ji->i', A, M)))   # (A_o (Bt_o A_o))[n,n]
    # d on A (n2=n3): tr(Bt_o Ad Bt_o A_o) = sum_{n,m} Bo[m,n] Ad[n] (Bo A_o)[n,m]
    t_odoo = np.real(np.sum((Bo.T * Ad[None, :]).T * M.T))
    S = Phi @ (beta[:, None] * X)
    fro = np.sum(np.abs(S) ** 2)
    diag = np.sum((Phi ** 2) @ (np.abs(beta[:, None] * X) ** 2))   # sum_{k,P} sum_n |.|^2
    tot = np.sum(np.abs(S.conj().T @ S) ** 2)
    print(f'{name:10s} tr4={tot:.4e}  oooo={oooo:+.4e} ({oooo/tot:+.3f} of tr4)  CS=||BoAo||_F^2={cs:.4e}'
          f'  oooo/CS={oooo/cs:+.4f}  CS/N\'^2||S||_F^2={cs/(Np**2*fro):.3f}', flush=True)
    print(f'{"":10s} 2pt: dooo={t_dooo/tot:+.4f}  odoo={t_odoo/tot:+.4f} of tr4;  ||S||_F^2/diag={fro/diag:.4f}'
          f'  (||S||_F^2-diag)*L\'N\'/tr4={(fro-diag)*Lp*Np/tot:+.4f}  *K\'N\'/tr4={(fro-diag)*Kp*Np/tot:+.4f}', flush=True)
    return oooo, cs, tot

run(gt, 'theta')
rng = np.random.default_rng(7)
for s in range(nr):
    run(np.exp(2j * np.pi * rng.random(Np)), f'random{s}')
