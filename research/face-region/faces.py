"""Faces of the density chain (research/chain/steps_f050_dL200.json) and the envelope E(s).

E(s) = max_k (B_k - Lam_k s) over the 130 faces (face 0 = parent of step 1, faces 1..129 = children),
each face valid for 0 <= s <= cap_k.  All arithmetic exact (fractions) unless printed as float.
"""
import json, os
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
CHAIN = os.path.join(HERE, '..', 'chain', 'steps_f050_dL200.json')


def load_faces(path=CHAIN):
    steps = json.load(open(path))
    faces = [(Fr(steps[0]['B0']), Fr(steps[0]['L0']), Fr(steps[0]['c0']))]
    for i, st in enumerate(steps):
        par = (Fr(st['B0']), Fr(st['L0']), Fr(st['c0']))
        assert par == faces[-1], f'step {i}: parent is not the previous child'
        faces.append((Fr(st['B']), Fr(st['L']), Fr(st['c'])))
    return steps, faces


def E(faces, s):
    """envelope value and the index of the active face (ties: smallest index)"""
    best, arg = None, None
    for k, (B, L, c) in enumerate(faces):
        if s <= c:
            v = B - L * s
            if best is None or v > best:
                best, arg = v, k
    return best, arg


if __name__ == '__main__':
    steps, faces = load_faces()
    print(len(faces), 'faces; face 0 =', [float(x) for x in faces[0]], ' last =', [float(x) for x in faces[-1]])
    for s in [Fr(0), Fr(1, 50), Fr(1, 25), Fr(1, 20), Fr(3, 50), Fr(2, 25), Fr(1, 10)]:
        v, k = E(faces, s)
        print(f's={float(s):.3f}  E={float(v):.6f}  active face {k}')
