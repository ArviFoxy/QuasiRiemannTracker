"""Complete exact certificate for the capped repeated-mark result; writes a JSON receipt.
Usage: python3 certify_all_k.py CHAIN.json K THETA H SC SP OUT.json [--return-only]
  e.g. python3 certify_all_k.py cchain_k8b.json 8 8747289/10000000 802/1000 13/250 9/200 certificate.json
Return mode 'global': the physical face P is applied through its global (downward-closed) source
theorem, so PR #69's window receipts (FR19, FR21, plain/width windows, t_f) are not used (Lemma D).
Checks (exact rational arithmetic):
 1. every source node: cert_chain_k.certify_node (NF8, NF10, NF13, capped K-copy HIGH gate,
    facet monotonicity for the payment lemma, root-completion coefficient bound);
 2. the final return at (theta, h, t_f): cert_return.run (edge covers, FR8 admissions, reserves)."""
import sys, json, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cert_chain_k as CC
import cert_return as CR
path, K = sys.argv[1], int(sys.argv[2])
THETA, H, SC, SP = Fr(sys.argv[3]), Fr(sys.argv[4]), Fr(sys.argv[5]), Fr(sys.argv[6])
OUT = sys.argv[7]
TF = Fr(1, 400)   # unused in global mode (Lemma D)
skip_chain = '--return-only' in sys.argv
nodes = json.load(open(path))
out = {'K': K, 'theta': str(THETA), 'h': str(H), 's_C': str(SC), 's_P': str(SP), 'return_mode': 'global', 'nodes': []}
par = (CC.R(1), CC.K_NAT, CC.R(11, 200))
if not skip_chain:
    for i, n in enumerate(nodes):
        rep = CC.certify_node(n, par, par, K)
        out['nodes'].append(dict(index=i, pivot=n['pivot'], B=n['B'], L=n['L'], q=n['q'], cap=n['cap'],
                                 bx=str(rep['bx']), min_scalar=str(rep['min_scalar']),
                                 bernstein_boxes=rep['boxes']))
        par = (CC.Q(n['B']), CC.Q(n['L']), CC.Q(n['cap']))
        print(f"node {i} certified", flush=True)
nC = nodes[-1]; nP = min(nodes, key=lambda n: abs(n['pivot'] - 0.0395))
C = (Fr(nC['B']), Fr(nC['L']), Fr(nC['cap'])); P = (Fr(nP['B']), Fr(nP['L']), Fr(nP['cap']))
rec, cov, bad = CR.run(THETA, H, C, P, tf=TF, sP=SP, sC=SC, mode='global')
assert not bad, bad
out['faces'] = {'C': {'index': len(nodes)-1, 'B': nC['B'], 'L': nC['L'], 'cap': nC['cap'], 's_plus': str(SC)},
                'P': {'index': nodes.index(nP), 'B': nP['B'], 'L': nP['L'], 'cap': nP['cap'], 's_plus': '43/1000'}}
out['reserves'] = {k: str(v) for k, v in rec.items()}
out['return_cover'] = [dict(edge=e, branch=b, box=[[str(x) for x in iv] for iv in box],
                            min_return=str(m), min_admission=(str(a) if a is not None else None))
                       for (e, b, box, m, a) in cov]
out['summary'] = dict(rectangles=len(cov), min_return=str(min(Fr(r['min_return']) for r in out['return_cover'])),
                      min_reserve=str(min(rec.values())))
json.dump(out, open(OUT, 'w'), indent=1)
print("CERTIFIED theta =", THETA, "=", float(THETA), "rectangles", len(cov))
