# full greedy chain from bootFace with density floor FLOOR, step dL (re-optimised (A,D) at every step)
import sys, time, json
import numpy as np
import flow_floor as F
dL = float(sys.argv[1]); floor = float(sys.argv[2]); Lend = float(sys.argv[3]); tag = sys.argv[4]
F.FLOOR[0] = floor
B0, L0, c0 = 0.99999, 2.5715, 0.1397
out = open('greedyfull_%s.jsonl' % tag, 'w')
guess = (np.log(0.6065), np.log(400.0)); k = 0; t0 = time.time()
while True:
    L = L0 - dL
    if L < Lend: break
    s, A, D = F.best_step(B0, L0, c0, dL, 0.1, eps=1e-6, guess=guess, N=300)
    if s >= 0.9:
        out.write(json.dumps(dict(k=k+1, infeasible=True, B0=B0, L0=L0)) + '\n'); out.flush(); break
    B = B0 - s*dL; k += 1
    out.write(json.dumps(dict(k=k, B0=B0, L0=L0, B=B, L=L, s0=s, A=A, D=D, t=time.time()-t0)) + '\n'); out.flush()
    guess = (np.log(A), np.log(D)); B0, L0, c0 = B, L, 0.1
