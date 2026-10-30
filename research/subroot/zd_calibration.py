"""Calibration of PR 93's three-word minimax as a zero-density calculator, and the price of a Guth-Maynard transplant.

count(env) = max_{0<=r<=1, 0<=m<=1/2, r+m>=1} min(env(r), env(2m), env(r+m)),  with env(w) = log_T #{rows with
|D|^2 >= N^(1+nu) ||b||^2/N}, N = T^w, nu = 2 sigma - 1.  Large-value inputs in the t-aspect:
  Montgomery (mean value T + N):   env = max(1, w) - nu w
  Huxley:                          |W| << N^2 V^-2 + T N^4 V^-6
  Guth-Maynard (arXiv 2405.20552): |W| << N^2 V^-2 + N^(18/5) V^-4 + T N^(12/5) V^-4
The minimax reproduces the known zero-density exponents A(sigma) = count / (1 - sigma):
Ingham 3/(2 - sigma), Huxley 3/(3 sigma - 1) (sigma >= 3/4), Guth-Maynard 15/(3 + 5 sigma) on [7/10, 8/10].
[numerical; model]"""
import numpy as np


def count(env, n=1201):
    r = np.linspace(0, 1, n)[:, None]
    m = np.linspace(0, 0.5, n)[None, :]
    v = np.minimum(np.minimum(env(r), env(2 * m)), env(r + m))
    return np.where(r + m >= 1, v, -np.inf).max()


def envs(nu):
    mont = lambda w: np.maximum(1, w) - nu * w
    hux = lambda w: np.minimum(np.maximum(w * (1 - nu), 1 + w * (1 - 3 * nu)), mont(w))
    gm = lambda w: np.minimum(np.maximum.reduce([w * (1 - nu), w * (1.6 - 2 * nu), 1 + w * (0.4 - 2 * nu)]), mont(w))
    return mont, hux, gm


if __name__ == '__main__':
    for s in (0.70, 0.72, 0.726, 0.75, 0.78, 0.80):
        mont, hux, gm = envs(2 * s - 1)
        print('sigma %.3f  A: Montgomery %.4f (3/(2-s) %.4f)  Huxley %.4f  GM %.4f (15/(3+5s) %.4f)' % (
            s, count(mont) / (1 - s), 3 / (2 - s), count(hux) / (1 - s), count(gm) / (1 - s), 15 / (3 + 5 * s)))
    nu = 0.452
    print('binding point nu = 0.452: DH %.4f, GM %.4f; the return has 0.6072, the bar needs <= 0.6063' % (
        1 - nu, count(envs(nu)[2])))
