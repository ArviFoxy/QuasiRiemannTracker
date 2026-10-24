"""Run the complete exact certificate for the doubled-mark result and write a JSON receipt.
Usage: python3 certify_all.py cchain_k2.json
Checks (all exact rational arithmetic):
 1. every node of the source chain (cert_chain.certify_node + certify_C1ii);
 2. the final return at theta, h, t_f (cert_return.run): conductor-edge covers, admissions, reserves."""
import sys, json
from fractions import Fraction as Fr
sys.path.insert(0, '.')
import cert_chain as CC
import cert_return as CR
THETA = Fr(8747514, 10**7); H = Fr(79987, 100000); TF = Fr(1, 360)
nodes = json.load(open(sys.argv[1]))
skip_chain = len(sys.argv) > 2 and sys.argv[2] == '--return-only'
out = {'theta': str(THETA), 'h': str(H), 't_f': str(TF), 'nodes': []}
par = (CC.R(1), CC.K, CC.R(11, 200))
if not skip_chain:
    for i, n in enumerate(nodes):
        rep = CC.certify_node(n, par, par)
        c1 = CC.certify_C1ii(par, CC.Q(n['q']))
        out['nodes'].append(dict(index=i, pivot=n['pivot'], B=n['B'], L=n['L'], q=n['q'], cap=n['cap'],
                                 bx=str(rep['bx']), min_scalar=str(rep['min_scalar']),
                                 bernstein_boxes=rep['boxes'], C1ii_boxes=c1))
        par = (CC.Q(n['B']), CC.Q(n['L']), CC.Q(n['cap']))
        print(f"node {i} certified", flush=True)
nC = nodes[-1]; nP = min(nodes, key=lambda n: abs(n['pivot'] - 0.0395))
C = (Fr(nC['B']), Fr(nC['L']), Fr(nC['cap'])); P = (Fr(nP['B']), Fr(nP['L']), Fr(nP['cap']))
rec, cov, bad = CR.run(THETA, H, C, P, tf=TF)
assert not bad, bad
out['faces'] = {'C': {'index': len(nodes)-1, 'B': nC['B'], 'L': nC['L'], 'cap': nC['cap'], 's_plus': '11/250'},
                'P': {'index': nodes.index(nP), 'B': nP['B'], 'L': nP['L'], 'cap': nP['cap'], 's_plus': '43/1000'}}
out['reserves'] = {k: str(v) for k, v in rec.items()}
out['return_cover'] = [dict(edge=e, branch=b, box=[[str(x) for x in iv] for iv in box],
                            min_return=str(m), min_admission=(str(a) if a is not None else None))
                       for (e, b, box, m, a) in cov]
out['summary'] = dict(rectangles=len(cov), min_return=str(min(Fr(r['min_return']) for r in out['return_cover'])),
                      min_reserve=str(min(rec.values())))
json.dump(out, open('certificate_doubled_marks.json', 'w'), indent=1)
print("CERTIFIED theta =", THETA, "=", float(THETA), "rectangles", len(cov))
