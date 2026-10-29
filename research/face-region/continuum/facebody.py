"""Face body checks on the chain:  B*(Lam) concave nondecreasing; convex combinations of valid faces are covered by
the max of the two lines (exact, Fractions) -- i.e. the dual (Lam, B) set of valid faces is convex."""
import sys
from fractions import Fraction as Fr
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from faces import load_faces
steps, F = load_faces()
# concavity / monotonicity of the chain's (Lam, B) points: slopes s_k decrease as Lam increases
sl = [(F[k-1][0] - F[k][0])/(F[k-1][1] - F[k][1]) for k in range(1, len(F))]
print('B nondecreasing in Lam:', all(s > 0 for s in sl), ' concave (slopes increase as Lam decreases):',
      all(sl[k+1] > sl[k] for k in range(len(sl) - 1)))
# a convex combination of two faces lies below max of the two lines on [0, cap]
import random
random.seed(1)
ok = True
for _ in range(2000):
    i, j = random.sample(range(len(F)), 2)
    t = Fr(random.randint(0, 1000), 1000)
    (B1, L1, _), (B2, L2, _) = F[i], F[j]
    Bt, Lt = t*B1 + (1 - t)*B2, t*L1 + (1 - t)*L2
    for s in [Fr(k, 1000) for k in range(0, 101)]:
        if Bt - Lt*s > max(B1 - L1*s, B2 - L2*s):
            ok = False
print('convex combination covered by the max of the two lines (exact):', ok)
