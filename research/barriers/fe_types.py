# Coxeter type of functional-equation groups for row/column multiple Dirichlet series.
# Coordinates centered at 1/2: x_i = s_i - 1/2 (column variables), y = w - 1/2 (row variable).
# Row Poisson (sextic family): A_k : x_i -> x_i + c_i*y for columns, y -> -y   (column i's conductor
#   contribution to the row Poisson is N(column)^{c_i}; for theta/Gauss-sum columns c_i = 1).
# Column reflection with conductor N(row)^{e_i}: x_i -> -x_i, y -> y + e_i*x_i.
#   theta reflection (cubic theta, conductor ~ N(row)^2): e = 2;  natural L-function reflection: e = 1.
import numpy as np, itertools, sys
def order(M, cap=60):
    P = np.eye(M.shape[0], dtype=int)
    for k in range(1, cap+1):
        P = P @ M
        if (P == np.eye(M.shape[0], dtype=int)).all(): return k
    return None
def group(cs, es):
    n = len(cs); d = n + 1
    A = np.eye(d, dtype=int)
    for i,c in enumerate(cs): A[i, n] = c
    A[n, n] = -1
    Bs = []
    for i,e in enumerate(es):
        B = np.eye(d, dtype=int); B[i, i] = -1; B[n, i] = e
        Bs.append(B)
    gens = [A] + Bs
    labels = {}
    for (a,Ma),(b,Mb) in itertools.combinations(enumerate(gens),2):
        labels[(a,b)] = order(Ma @ Mb)
    return gens, labels
cases = {
 'second moment, two theta columns (inverse moment)': ([1,1],[2,2]),
 'mixed: theta column x natural column (inverse x plain)': ([1,1],[2,1]),
 'two natural columns (plain fourth moment)': ([1,1],[1,1]),
 'first moment, one theta column': ([1],[2]),
 'first moment, one natural column': ([1],[1]),
 'three theta columns': ([1,1,1],[2,2,2]),
}
for name,(cs,es) in cases.items():
    gens, lab = group(cs, es)
    # Coxeter test for rank 3: sum of 1/m over the three pairs > 1 finite, = 1 affine, < 1 hyperbolic
    labs = list(lab.values())
    if None in labs: verdict = 'some pair of infinite order (non-spherical)'
    elif len(gens) == 3:
        sm = sum(1/m for m in labs); verdict = 'finite' if sm > 1 + 1e-12 else ('affine' if abs(sm-1) < 1e-12 else 'hyperbolic')
    elif len(gens) == 2:
        verdict = 'finite dihedral of order %d' % (2*labs[0])
    else:
        verdict = 'rank %d, labels %s' % (len(gens), labs)
    print(f"{name}: pair orders {lab} -> {verdict}")

# rank >= 4: decide finiteness by checking whether the Tits/Gram bilinear form is positive definite
def coxeter_form(labels, n):
    G = np.eye(n)
    for (a,b),m in labels.items():
        G[a,b] = G[b,a] = -np.cos(np.pi/m) if m is not None else -1.0
    return G
print()
more = {
 'plain fourth moment |S1 S2|^2 (4 natural columns)': ([1,1,1,1],[1,1,1,1]),
 'mixed second moment |M S|^2 (2 theta + 2 natural)': ([1,1,1,1],[2,2,1,1]),
 'inverse second moment |M|^2 (2 theta)': ([1,1],[2,2]),
 'plain second moment |S|^2 (2 natural)': ([1,1],[1,1]),
 'mixed |M|^2 |S|^2 with S of one copy (2 theta + 1 natural)': ([1,1,1],[2,2,1]),
}
for name,(cs,es) in more.items():
    gens, lab = group(cs, es)
    G = coxeter_form(lab, len(gens))
    ev = np.linalg.eigvalsh(G)
    t = 'finite (positive definite)' if ev.min() > 1e-9 else ('affine (positive semidefinite, singular)' if ev.min() > -1e-9 else 'hyperbolic/indefinite')
    print(f"{name}: labels {sorted(set(v for v in lab.values()))}, min eig {ev.min():+.4f} -> {t}")
