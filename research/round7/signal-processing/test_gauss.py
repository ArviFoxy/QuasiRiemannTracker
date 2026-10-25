import sys; sys.path.insert(0, '.')
from zw import *
ar = Arith(4000)
primes = ar.elems(1, 4000, primes_only=True)
gtab = GaussTable(ar, primes)
els = [e for e in ar.elems(1, 4000) if len(e['ps']) >= 2][:40]
mx = 0
for n in els:
    d = gauss_direct(ar, n) / math.sqrt(n['N'])
    t = gtab.gt(n)
    mx = max(mx, abs(d - t))
print("max |direct - twisted-mult| over", len(els), "composite n:", mx)
# check |g~|=1 and Jacobi-type identity g~(pi)^2 = conj(g~(pi)) * (pi/|pi|) * unit ?
import cmath
for P in primes[:8]:
    p, r = P['ps'][0], P['rs'][0]
    g = gtab.prime[(p, r)][2]
    z = complex(P['a'] - P['b']/2, P['b']*math.sqrt(3)/2)   # a + b omega as complex
    ratio = g**2 / (np.conj(g) * z/abs(z))
    print(p, P['a'], P['b'], "|g~|=%.6f" % abs(g), " g~^2/(conj g~ * pi/|pi|) =", np.round(ratio, 6))
