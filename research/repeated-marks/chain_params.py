"""The chain's parameters, set once (environment variables, with defaults that reproduce PR 73).

- `K` (`QRH_K`): the natural cost, i.e. the cap `6(2β − 1) ≤ K` that the source steps and the
  return use. `THETA_I = (1 + K/6)/2` is the matching incumbent bound on `β`.
- `START` (`QRH_START = "B,L,cap"`): the face the family starts on, i.e. the first parent of the
  chain. Default: Collet's natural face `(1, K, 11/200)`. Sil's fourth-power source face is
  `0.99999,93/25,3/50`.
"""
import os
from fractions import Fraction as Fr

K = Fr(os.environ.get('QRH_K', '11243277/2500000'))
THETA_I = (1 + K/6)/2

FEES = dict(q=Fr(0), allowance=Fr(1, 10**12), lowFee=Fr(1, 10**8), highFee=Fr(1, 10**7))

def _start():
    s = os.environ.get('QRH_START')
    B, L, cap = (Fr(1), K, Fr(11, 200)) if s is None else tuple(Fr(x) for x in s.split(','))
    return dict(B=B, L=L, cap=cap, **FEES)

START = _start()
