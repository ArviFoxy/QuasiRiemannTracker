"""Step 5: is the physical face (step 64) the best chain face for the newTop capacity?  (side check)"""
from fractions import Fraction as Fr
from model import P
from chainfaces import chain_faces

Pm = P(exact=True)
faces = chain_faces()
dp = Pm.dp
rows = []
for name, (B, L, cap) in faces.items():
    if L < 2:          # PhysicalSchedule.lambda_bounds: 2 <= physicalLambda
        continue
    aff = (2 * Pm.y - (2 - B) * dp) / L
    small = 1 - B / 2 - (Fr(9, 2) - L / 2) * Pm.numCap      # small_plain_global (>= 0)
    rows.append((aff, name, B, L, small))
rows.sort(reverse=True)
print('numCap*dp =', float(Pm.numCap * dp))
for aff, name, B, L, small in rows[:6]:
    print(f'{name:10s} B={float(B):.8f} L={float(L):.4f} affine capacity at dp = {float(aff):.8f}  small_plain_global={float(small):+.4f}')
cur = [r for r in rows if r[1] == 'source_64'][0]
print('step 64 capacity', float(cur[0]))
