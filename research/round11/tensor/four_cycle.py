# The 4-cycle of the trace method for P1, split by propagator sectors (round 11, tensor route).
#   S = Phi diag(g~) X  (K' x L'),  tr((SS*)^2) = tr(Bt A Bt A),
#   A = Phi^T Phi  (quadratic propagator, A(n,m) = sum_k chi_k(nm)),
#   Bt = D X X* D*  (cubic propagator dressed by the theta phases, Bt(n,m) = g~(n) B(n,m) conj g~(m)).
# Each propagator = diagonal part (d) + off-diagonal part (o); the 16 sector traces are printed for
# the true phases g~ and for random unimodular phases (only Bt_o depends on the phases).
# usage: python3 four_cycle.py K N L [seeds]
import sys, os, math, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../round7/signal-processing'))
from build import load
W = np.exp(2j * np.pi / 3)

K, N, L = map(int, sys.argv[1:4]); nseed = int(sys.argv[4]) if len(sys.argv) > 4 else 3
d = load(K, N, L, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data'))
Phi = d['Phi'].astype(float); gt = d['gt']; Xe = d['Xe']
X = np.where(Xe < 0, 0, W ** np.where(Xe < 0, 0, Xe))
Kp, Np = Phi.shape; Lp = X.shape[1]
print(f'K={K} N={N} L={L}: K\'={Kp} N\'={Np} L\'={Lp}  (N\'/(K\'L\') = {Np/(Kp*Lp):.3f})', flush=True)
A = Phi.T @ Phi
B = X @ X.conj().T
Ad = np.diag(np.diag(A)); Ao = A - Ad

def sectors(beta):
    Bt = (beta[:, None] * B) * beta.conj()[None, :]
    Bd = np.diag(np.diag(Bt)); Bo = Bt - Bd
    P = {('d', 'd'): Bd @ Ad, ('d', 'o'): Bd @ Ao, ('o', 'd'): Bo @ Ad, ('o', 'o'): Bo @ Ao}
    T = {}
    for k1, M1 in P.items():
        for k2, M2 in P.items():
            T[k1 + k2] = np.real(np.sum(M1 * M2.T))     # tr(M1 M2)
    S = Phi @ (beta[:, None] * X)
    G = S.conj().T @ S
    FP = np.real(np.diag(G))
    tot = np.sum(np.abs(G) ** 2)
    return T, tot, np.sum(FP ** 2), tot - np.sum(FP ** 2), np.linalg.norm(S, 2) ** 2

def show(name, res):
    T, tot, diagP, MM, op2 = res
    print(f'{name}: tr((SS*)^2) = {tot:.4e}  (sum T = {sum(T.values()):.4e})  sum_P F_P^2 = {diagP:.4e}'
          f'  MM = {MM:.4e}  ||S||^2 = {op2:.4e}')
    keys = sorted(T)
    print('   ' + '  '.join(f'{"".join(k)}={T[k]/tot:+.3f}' for k in keys))

rt = sectors(gt); show('theta g~', rt)
rng = np.random.default_rng(1)
for s in range(nseed):
    u = np.exp(2j * np.pi * rng.random(Np))
    show(f'random #{s}', sectors(u))
# predictions: random model tr ~ N'^2 K' L' (K' + L'), MM ~ L'^2 K' N'^2
print(f'scales: N\'^2K\'L\'(K\'+L\') = {Np**2*Kp*Lp*(Kp+Lp):.3e}  L\'^2 K\' N\'^2 = {Lp**2*Kp*Np**2:.3e}'
      f'  N\'^4 = {Np**4:.3e}  K\'N\' = {Kp*Np:.3e}  N\'^2 = {Np**2:.3e}')
