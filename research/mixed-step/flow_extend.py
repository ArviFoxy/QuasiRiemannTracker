"""Continue the c6 mixed continuum flow past s = 0.054 with larger face caps.
usage: python3 flow_extend.py CAP s_end OUT.json"""
import sys, os, json, time
CAPX = float(sys.argv[1]); S_END = float(sys.argv[2]); OUT = sys.argv[3]
sys.argv = ['x', OUT, '6']
import continuum_mixed as CM
G = CM.G
CM.ok_node_q.__defaults__ = (0.0, G.FINE, CAPX)
rows = json.load(open('cont_c6.json'))
r = rows[-1]
s, E, L = r['s'], r['E'], r['L']
ds = 1e-3
out = []
t0 = time.time()
while s <= S_END + 1e-12:
    L, q = CM.min_slope(s, E, L)
    if L is None:
        print('infeasible at', s, flush=True); break
    B = E + L*s
    out.append(dict(s=s, E=E, B=B, L=L, q=q, den=1 + q - 6*q*B/L))
    print(f"s={s:.4f} E={E:.6f} L={L:.5f} B={B:.6f} q={q:.4f} t={time.time()-t0:.0f}", flush=True)
    json.dump(out, open(OUT, 'w'), indent=0)
    Lm, _ = CM.min_slope(s + ds/2, E - L*ds/2, L)
    E -= (Lm if Lm is not None else L)*ds
    s = round(s + ds, 10)
