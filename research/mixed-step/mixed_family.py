"""Fine face family for the mixed step after the fan (family2-style), and exact checks of the draft
SourceValid3 at sample faces.

1. flow:   E' = -L_min(s, E) from the full-gate continuum solver (continuum_mixed.py) with a HIGH
           margin MH and face caps CAPX, from the last fan face (s0, E0).
2. pieces: s = sig_j + H_j y, E_j(y) cubic Hermite through the flow, coefficients rounded to 1e-14.
3. faces:  secant lines on the grid Dy = 2^-16; q(y) = (1 - den)/(6 B0/L0 - 1) from the parent
           (the previous grid face), so den3 = den exactly.
usage: python3 mixed_family.py flow OUT.json [MH] [CAPX] [s_end] [ds]
       python3 mixed_family.py check FLOW.json sig0,sig1,...  [CAPX]"""
import sys, os, json, random
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'faceless-chain'))
import polyq as P

DEN = Fr(1, 2**15)
M = 16

def run_flow(out, mh, capx, s_end, ds, s0, E0, L0):
    sys.argv = ['x', out, '6']
    import continuum_mixed as CM
    G = CM.G
    CM.ok_node_q.__defaults__ = (mh, G.FINE, capx)
    s, E, L = s0, E0, L0
    rows = []
    while s <= s_end + 1e-12:
        Ln, q = CM.min_slope(s, E, L)
        if Ln is None:
            print('infeasible at', s, flush=True); break
        L = Ln
        rows.append(dict(s=s, E=E, L=L, q=q))
        print(f"s={s:.5f} E={E:.7f} L={L:.6f} B={E + L*s:.7f} q={q:.4f}", flush=True)
        json.dump(rows, open(out, 'w'), indent=0)
        Lm, _ = CM.min_slope(s + ds/2, E - L*ds/2, L)
        E -= (Lm if Lm is not None else L)*ds
        s = round(s + ds, 12)
    return rows

class Family:
    def __init__(self, sig, Ey, cap):
        self.sig = sig; self.Ey = Ey; self.cap = cap
        self.H = [sig[j + 1] - sig[j] for j in range(len(sig) - 1)]
        self.Dy = Fr(1, 2**M)
    def polys(self, j):
        Ey = self.Ey[j]; H = self.H[j]; Dy = self.Dy
        L = P.smul(1/(H*Dy), P.sub(Ey, P.shift(Ey, Dy)))
        B = P.add(Ey, P.mul([self.sig[j], H], L))
        return B, L, P.shift(B, -Dy), P.shift(L, -Dy)
    def face(self, j, y):
        B, L, B0, L0 = self.polys(j)
        b0, l0 = P.ev(B0, y), P.ev(L0, y)
        q = (1 - DEN)/(6*b0/l0 - 1)
        import mixed_certs as MC
        n = MC.face(P.ev(B, y), P.ev(L, y), self.cap, q)
        low = MC.face(b0, l0, self.cap)
        return n, low

def build(rows, sig_f, E0exact, cap, RD=14, L0exact=None):
    import numpy as np
    ss = np.array([r['s'] for r in rows]); Es = np.array([r['E'] for r in rows]); Ls = np.array([r['L'] for r in rows])
    sig = [Fr(x).limit_denominator(10**7) for x in sig_f]
    vals = [float(np.interp(float(x), ss, Es)) for x in sig]
    ders = [-float(np.interp(float(x), ss, Ls)) for x in sig]
    if L0exact is not None: ders[0] = -float(L0exact)
    Ey = []
    for j in range(len(sig) - 1):
        h = float(sig[j + 1] - sig[j])
        Ea, Eb, da, db = vals[j], vals[j + 1], ders[j]*h, ders[j + 1]*h
        c = [Ea, da, 3*(Eb - Ea) - 2*da - db, da + db - 2*(Eb - Ea)]
        Ey.append([Fr(round(ck*10**RD), 10**RD) for ck in c])
    Ey[0][0] = E0exact
    return Family(sig, Ey, cap)

def check(fam, nsample=6, seed=0):
    import mixed_certs as MC
    random.seed(seed)
    bad = 0; Dy = fam.Dy
    for j in range(len(fam.H)):
        ys = [Dy, 2*Dy, Fr(1, 2), 1 - Dy] + [Fr(random.randrange(1, 2**M - 1), 2**M) for _ in range(nsample)]
        for y in ys:
            n, low = fam.face(j, y)
            ok, msgs, _ = MC.check_node(n, low, low, Fr(8))
            cell = MC.cell_ok(n, low)
            if not (ok and cell):
                bad += 1
                print(f"piece {j} y={float(y):.6f}: FAIL {msgs[:3]} cell={cell}", flush=True)
        B, L, _, _ = fam.polys(j)
        print(f"piece {j}: s {float(fam.sig[j]):.5f}..{float(fam.sig[j+1]):.5f}  L {float(P.ev(L, 0)):.5f} -> "
              f"{float(P.ev(L, 1 - Dy)):.5f}  B {float(P.ev(B, 0)):.6f} -> {float(P.ev(B, 1 - Dy)):.6f}", flush=True)
    return bad

if __name__ == '__main__':
    if sys.argv[1] == 'flow':
        out = sys.argv[2]
        mh = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-3
        capx = float(sys.argv[4]) if len(sys.argv) > 4 else 0.07
        s_end = float(sys.argv[5]) if len(sys.argv) > 5 else 0.062
        ds = float(sys.argv[6]) if len(sys.argv) > 6 else 5e-4
        fan = json.load(open(os.path.join(HERE, os.environ.get('FANJSON', 'fan_k92_cap0.075.json'))))
        last = fan[-1]
        s0 = 0.016; L0 = float(Fr(last['L'])); E0 = float(Fr(last['B'])) - L0*s0
        run_flow(out, mh, capx, s_end, ds, s0, E0, L0)
    else:
        rows = json.load(open(sys.argv[2]))
        sig_f = [float(x) for x in sys.argv[3].split(',')]
        cap = Fr(sys.argv[4]) if len(sys.argv) > 4 else Fr(7, 100)
        fan = json.load(open(os.path.join(HERE, os.environ.get('FANJSON', 'fan_k92_cap0.075.json'))))
        last = fan[-1]
        s0 = Fr(16, 1000)
        E0 = Fr(last['B']) - Fr(last['L'])*s0
        assert abs(float(s0) - sig_f[0]) < 1e-12
        fam = build(rows, sig_f, E0, cap, L0exact=Fr(last['L']) if os.environ.get('L0EXACT', '1') == '1' else None)
        bad = check(fam)
        print('ALL OK' if bad == 0 else f'{bad} failures')
