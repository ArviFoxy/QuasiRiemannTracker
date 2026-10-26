"""Source-side ceiling: HIGH constraint removed at every (nu, p) (flows/dxi0.05x.json, q hits the floor 1/2).
The return receipt schedule_lambda_low (Lambda_P >= 2, Lemma D schedule) forbids the flat end faces, so P is
taken at the last faces with Lambda_P >= 2; C at 0.06 (no slope receipt for C)."""
import sys, os, json
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import score as SC
rows = json.load(open(os.path.join(HERE, 'flows', 'dxi0.05x.json')))
BC, LC = SC.face_at(rows, 0.06)
jobs = []
for s in (0.0375, 0.038, 0.0385, 0.039):
    BP, LP = SC.face_at(rows, s)
    if LP >= 2: jobs.append((s, (BP, LP, BC, LC)))
with Pool(4) as pool:
    res = pool.map(SC.theta, [j[1] for j in jobs])
for (s, a), th in zip(jobs, res):
    print(f"ceiling P@{s} BP={a[0]:.7f} LP={a[1]:.5f} cap@0.843={(a[0]-0.843)/a[1]:.5f} BC={a[2]:.7f} LC={a[3]:.5f} theta*={th}", flush=True)
