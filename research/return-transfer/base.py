"""Common driver for the return-transfer pricing (exact; Lemma D mode, dMinus > 1/2).

Reproduces ../mixed-step/ret_scan.py at the design point of the brief:
faces from ../mixed-step/faces_k92.json, h = 2011/2500, s_P = s_C = 29/500, face caps 3/40,
P-face count window sPp = 43/1000.  Run with QRH_K=9/2.

Other scripts in this directory monkeypatch cert_return (CR) and call theta_star()."""
import os, sys, json
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
assert os.environ.get('QRH_K') == '9/2', "export QRH_K=9/2"
import cert_return as CR

CR.GLOBAL_DROP = CR.GLOBAL_DROP + ('source_lambda_low',)
_rec0 = CR.receipt
def _receipt(G, *a, **k):
    r = _rec0(G, *a, **k)
    r['dMinus_lower_3_4'] = G['ds'] - Fr(1, 2)      # the fork field relaxed to dMinus > 1/2
    return r
CR.receipt = _receipt

_F = json.load(open(os.path.join(HERE, '..', 'mixed-step', 'faces_k92.json')))
DEF = dict(BC=Fr(_F['C']['B']), LC=Fr(_F['C']['L']), BP=Fr(_F['P']['B']), LP=Fr(_F['P']['L']),
           cap=Fr(3, 40), sP=Fr(29, 500), sC=Fr(29, 500), h=Fr(2011, 2500), sPp=Fr(43, 1000))

def params(spec=''):
    P = dict(DEF)
    for kv in spec.split(','):
        if kv:
            k, v = kv.split('='); P[k] = Fr(v)
    return P

def ok(th, P, raise_=False):
    CR.ADM_CACHE.clear()
    C = (P['BC'], P['LC'], P['cap']); Pf = (P['BP'], P['LP'], P['cap'])
    try:
        rec, cov, bad = CR.run(Fr(th, 10**7), P['h'], C, Pf, verbose=False, sP=P['sP'], sC=P['sC'],
                               sPp=P['sPp'], mode='global')
        return not bad
    except (ValueError, AssertionError, ZeroDivisionError):
        if raise_: raise
        return False

def theta_star(P, lo=8700000, hi=8747700):
    """least theta (units 1e-7) certified; None if even hi fails."""
    if not ok(hi, P): return None
    while hi - lo > 1:
        mid = (lo + hi)//2
        lo, hi = (lo, mid) if ok(mid, P) else (mid, hi)
    return hi

def diag(th, P, out=print):
    """binding edge / branches at theta (units 1e-7)."""
    from collections import Counter
    G = CR.geometry(Fr(th, 10**7), P['h'], P['BP'], P['LP'], P['sP'])
    rec = CR.receipt(G, P['BP'], P['LP'], P['cap'], P['cap'], P['sC'], P['sPp'], CR.THETA_I)
    rec = {k: v for k, v in rec.items() if k not in CR.GLOBAL_DROP}
    out('smallest receipts: ' + str([(k, round(float(v), 7)) for k, v in sorted(rec.items(), key=lambda kv: kv[1])[:5]]))
    out('geometry: ' + str({k: round(float(v), 6) for k, v in G.items()}))
    cands = CR.candidates({'C': (P['BC'], P['LC'], P['sC']), 'P': (P['BP'], P['LP'], P['sPp'])}, G['kap'])
    for name, d, Ccap in CR.edges(G, P['BP'], P['LP']):
        try:
            CR.ADM_CACHE.clear()
            cov = CR.cover_edge(G, d, Ccap, cands)
            cnt = Counter(c[0] for c in cov)
            worst = min(cov, key=lambda c: c[2])
            out(f"edge {name} d={float(d):.5f} C={float(Ccap):.6f}: {len(cov)} rects, min ret {float(worst[2]):.3e} "
                f"at {worst[0]} box {[(round(float(a), 4), round(float(b), 4)) for a, b in worst[1]]}, branches {dict(cnt)}")
        except ValueError as e:
            out(f"edge {name} d={float(d):.5f} C={float(Ccap):.6f}: FAIL {e}")

if __name__ == '__main__':
    spec = sys.argv[1] if len(sys.argv) > 1 else ''
    P = params(spec)
    t = theta_star(P)
    print('theta* =', t, flush=True)
    if t:
        print('--- at theta*:'); diag(t, P)
        print('--- at theta* - 1:'); diag(t - 1, P)
