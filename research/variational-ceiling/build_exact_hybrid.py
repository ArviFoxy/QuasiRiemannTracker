"""Exact hybrid chain for Lean: Lemma F as rotated self-parent cells (task #50, draft).

Input: a float hybrid chain from hybchain2 / hyb_fees (nodes with B, L, cap, pivot, info=[b1,q1,q2]).
Each float node k becomes
  A_k : an ordinary node on [b_x, b1] (LOW = HIGH = previous real face), threshold q1;
  cells: rotated self-parent nodes covering [b1, cap] (LOW = previous cell, HIGH = previous real
         face), child (B_prev - eta*c_prev, L_prev - eta, c_next), so the crossing is exactly c_prev.
Cell sizes double while the float gates pass and halve on failure; each cell's threshold is
searched over the LOW denominator den = 1 - 6qB0/L0 (a smaller den gives a larger amplifier
a' = (qe+r)/den and a longer admissible cell, at a HIGH-gate cost 1.5a').
All arithmetic that defines nodes is exact (Fraction); gate checks here are float pre-checks.
Exact certification is a separate pass (cert_chain_k.certify_node with fees set as module globals).
usage: python3 build_exact_hybrid.py FLOAT.json e,r,f OUT.json"""
import sys, os, json
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
from ss_fb import gates_at, minres
import cchain_k as CK

ETA = Fr(1, 10**9)
RES = 5e-8

def dec(x, nd=13, up=False):
    f = Fr(str(round(x, nd))); step = Fr(1, 10**nd)
    if up and f < Fr(x): f += step
    if (not up) and f > Fr(x): f -= step
    return f

def reserve(b, node, par, HP, q, sched, g_):
    B, L = float(node[0]), float(node[1])
    B0, L0, h0 = (float(v) for v in par)
    g = gates_at(float(b), B, L, q, B0, L0, h0, tuple(float(v) for v in HP), sched=sched, K=CK.K_FB,
                 gain_fn=g_, nnu=401)
    return minres(g)[0]

def best_cell_q(lo, hi, node, par, HP, sched, g_):
    B0, L0 = float(par[0]), float(par[1]); qc = L0/(6*B0)
    best = (-1, None)
    for x in np.geomspace(1e-11, 1e-2, 45):
        q = qc*(1-x)
        if q < 0.5: continue
        r = min(reserve(lo, node, par, HP, q, sched, g_), reserve(hi, node, par, HP, q, sched, g_))
        if r > best[0]: best = (r, q)
    return best

def main():
    fl = json.load(open(sys.argv[1])); sched = tuple(float(v) for v in sys.argv[2].split(','))
    out = sys.argv[3]
    prev = (Fr(1), Fr(11243277, 2500000), Fr(11, 200))   # natural face
    nodes = []; real_idx = -1
    for k, n in enumerate(fl):
        s = Fr(str(n['pivot'])); b1, q1, q2 = n['info']
        L = dec(float(n['L']) + 2e-12, up=True)
        B = prev[0] - (prev[1] - L)*s
        capT = Fr(str(n['cap']))
        HP = prev
        g_ = CK.gfun(tuple(float(v) for v in HP), 8)
        if q1 is not None:
            c0 = dec(float(b1), nd=9, up=True)
            qA = dec(q1, nd=12)
            A = (B, L, c0)
            r = min(reserve(s, A, prev, HP, float(qA), sched, g_), reserve(c0, A, prev, HP, float(qA), sched, g_))
            nodes.append(dict(kind='old', B=str(B), L=str(L), q=str(qA), cap=str(c0), low=real_idx, high=real_idx,
                              pivot=float(s), reserve=r))
            cur = A; low = len(nodes)-1
        else:
            cur = (B, L, s); low = real_idx; c0 = s
        # self cells from c0 to capT
        c = c0; step = Fr(1, 10**5)
        while c < capT:
            nxt = min(capT, c + step)
            node = (cur[0] - ETA*c, cur[1] - ETA, nxt)
            par = cur
            r, q = best_cell_q(c, nxt, node, par, HP, sched, g_)
            if r > RES:
                qQ = dec(q, nd=12)
                nodes.append(dict(kind='self', B=str(node[0]), L=str(node[1]), q=str(qQ), cap=str(nxt),
                                  low=low, high=real_idx, pivot=float(s), reserve=r))
                cur = node; low = len(nodes)-1; c = nxt; step *= 4
            else:
                step /= 2
                if step < Fr(1, 10**10):
                    if nodes and nodes[low]['kind'] == 'old' and c == Fr(nodes[low]['cap']):
                        # stuck at the join: extend the old-parent node to the right and retry
                        A = (Fr(nodes[low]['B']), Fr(nodes[low]['L']), c + Fr(1, 10**6))
                        rA = min(reserve(s, A, prev, HP, float(Fr(nodes[low]['q'])), sched, g_),
                                 reserve(A[2], A, prev, HP, float(Fr(nodes[low]['q'])), sched, g_))
                        if rA <= RES: raise SystemExit(f"node {k}: join stuck at {float(c)}")
                        nodes[low]['cap'] = str(A[2]); nodes[low]['reserve'] = rA
                        cur = A; c = A[2]; step = Fr(1, 10**5); continue
                    raise SystemExit(f"node {k}: cell stuck at {float(c)}")
        prev = cur; real_idx = len(nodes)-1
        print(f"float node {k} pivot {float(s):.5f}: {sum(1 for x in nodes if x['pivot']==float(s))} Lean nodes, "
              f"face B={float(cur[0]):.10f} L={float(cur[1]):.8f} cap={float(cur[2]):.7f}", flush=True)
        json.dump(nodes, open(out, 'w'), indent=0)

if __name__ == '__main__':
    main()
