# greedy chain from bootFace with child cap c (all steps), floor FLOOR, step dL: how does the cap of the faces change the chain?
import sys, time, json
import numpy as np
import flow_floor as F
dL = float(sys.argv[1]); floor = float(sys.argv[2]); Lend = float(sys.argv[3]); cchild = float(sys.argv[4]); tag = sys.argv[5]
F.FLOOR[0] = floor
B0, L0, c0 = 0.99999, 2.5715, 0.1397
out = open('greedycap_%s.jsonl' % tag, 'w')
guess = (np.log(0.6065), np.log(400.0)); k = 0; t0 = time.time()
while True:
    L = L0 - dL
    if L < Lend: break
    s, A, D = F.best_step(B0, L0, c0, dL, cchild, eps=1e-6, guess=guess, N=300)
    if s >= 0.9:
        out.write(json.dumps(dict(k=k+1, infeasible=True, B0=B0, L0=L0)) + '\n'); out.flush(); break
    B = B0 - s*dL; k += 1
    out.write(json.dumps(dict(k=k, B0=B0, L0=L0, B=B, L=L, s0=s, A=A, D=D, t=time.time()-t0)) + '\n'); out.flush()
    guess = (np.log(A), np.log(D)); B0, L0, c0 = B, L, cchild
