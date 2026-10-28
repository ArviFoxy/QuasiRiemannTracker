# binding location + window slacks for given configs (at theta* - 1e-9 units), both window systems
import json, sys
from fractions import Fraction as Fr
import pr86, best, cert_return as CR, ode_faces as OF
chain = json.load(open('chain86.json'))
ext = {}
for l in open('greedy_f060_dl005.jsonl'):
    r = json.loads(l)
    if not r.get('infeasible'): ext[r['k']] = (OF.frac(r['B']), OF.frac(r['L']))
def face(k): return (Fr(chain[k]['B']), Fr(chain[k]['L'])) if k <= 46 else ext[k]
def evalpoly(a, dl, p): return sum(float(c)*dl**i*p**j for (i,j),c in a.items())
def analyse(label, kc, kp, win):
    fc, fp = face(kc), face(kp)
    br = ['old','C','Ccap','C-7','P','Pcap'] if win == 'lemmaW' else ['old','C','Pcap']
    cfg = pr86.Cfg(windows=win, branches=br, BC=fc[0], LC=fc[1], BP=fp[0], LP=fp[1])
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873900000, step=1000)
    t, h = r
    cfg_f = cfg.copy(th=Fr(t-1, 10**9), h=best.h_for(Fr(t-1, 10**9), cfg.bounds[1]))   # just failing
    fb = pr86.failing_boxes(cfg_f, 'newTop', maxdepth=16)
    pr86.apply_globals(cfg_f)
    G = pr86.geometry(cfg_f)
    cands = {nm: (b, meta) for nm, b, meta in pr86.candidate_list(cfg_f, G)}
    edges = {nm: (d, C) for nm, d, C in pr86.edge_list(cfg_f, G)}
    d, C = edges['newTop']
    box = fb[0]; (d0,d1),(p0,p1) = box
    dl, p = float((d0+d1)/2), float((p0+p1)/2)
    print('%s [%s]: theta*=%.9f h=%.6f | failing box delta[%.4f,%.4f] p[%.4f,%.4f]' % (label, win, t/1e9, float(h), float(d0), float(d1), float(p0), float(p1)))
    for nm in ('C', 'Pcap', 'Ccap'):
        if nm not in cands: continue
        b, meta = cands[nm]
        B, L, s_plus, capped = meta
        polys, scal = CR.admission_polys(b, B, L, s_plus, capped)
        D = evalpoly(b['D'], dl, p); J = evalpoly(b['J'], dl, p); Mn = evalpoly(b['Mn'], dl, p); N = evalpoly(b['N'], dl, p)
        DJ = D*J; mstar = Mn/DJ
        lowM = float(max(CR.ETA, (B - L*(s_plus-CR.ETA))/2 + CR.ETA)) if (win=='lemmaW' and not capped) else None
        g = {k: evalpoly(q_, dl, p) for k, q_ in polys.items()}
        print('   %-5s count=%.6f  m*=%.5f   guard slacks (/DJ): lowerM %.4f upperM %.4f ; N-tail/J %.4f ; scal %s' % (nm, N/J, mstar, g['Mn-mLDJ']/DJ, g['mUDJ-Mn']/DJ, g['N-tail']/J, {k: round(float(v),4) for k,v in scal.items()}))
for label, kc, kp in (('PR86 split 46/38', 46, 38), ('lowered floor split 73/38', 73, 38), ('lowered floor split 74/38', 74, 38)):
    for win in ('collet', 'lemmaW'):
        analyse(label, kc, kp, win)
