"""Common parameters for the interpolation-lemma study (fresh7a)."""
import numpy as np

DELTA = 0.4546
P_AMP = 0.5
R1 = 0.7413      # r*  (M saturated)
R2 = 1.1553      # t*  (M saturated, straddle)

def lin_I(r):
    return 1.0 - DELTA*(P_AMP + (1.0-P_AMP)*r)

def lin_L(t):
    return 1.0/6.0 + (5.0/6.0 - DELTA)*t

RCORNER = 0.5*(lin_I(R1) + lin_L(R2))

def lin(r):
    r = np.asarray(r, dtype=float)
    return np.where(r <= 1.0, lin_I(r), lin_L(r))

def tent(r):
    """c(r) = (R - Lin(r))/2, clipped at 0: required log_U dip of |M_r|/sat."""
    return np.maximum(0.0, 0.5*(RCORNER - lin(r)))

if __name__ == "__main__":
    print("R corner (avg of I(r1), L(r2)) =", RCORNER, lin_I(R1), lin_L(R2))
    print("c(1) =", float(tent(1.0)))
    print("slopes: left", DELTA*(1-P_AMP)/2, " right", (5/6-DELTA)/2)
