"""Bounded exact rational verification of this written manuscript.

No imported project code, no external process, no proof assistant, no network.
Reads frozen JSON evidence and writes only beside this file.
"""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import hashlib
import json
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
CHECKS = {}

def bind(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}

def eq(name, actual, expected):
    expected = Q(expected)
    assert actual == expected, (name, actual, expected)
    CHECKS[name] = str(actual)
    return actual

def pos(name, actual):
    assert actual > 0, (name, actual)
    CHECKS[name] = str(actual)
    return actual

class Poly:
    def __init__(self, value):
        self.c = {k: Q(v) for k, v in value.items() if v} if isinstance(value, dict) else ({(0, 0): Q(value)} if value else {})
    def __add__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        out = self.c.copy()
        for k, v in other.c.items():
            out[k] = out.get(k, Q(0)) + v
        return Poly(out)
    __radd__ = __add__
    def __neg__(self):
        return Poly({k: -v for k, v in self.c.items()})
    def __sub__(self, other):
        return self + (-other if isinstance(other, Poly) else -Q(other))
    def __rsub__(self, other):
        return -self + other
    def __mul__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        out = {}
        for (i, j), a in self.c.items():
            for (k, l), b in other.c.items():
                key = (i + k, j + l)
                out[key] = out.get(key, Q(0)) + a * b
        return Poly(out)
    __rmul__ = __mul__
    def __truediv__(self, other):
        return self * (1 / Q(other))
    def at(self, a, b):
        return sum(v * a**i * b**j for (i, j), v in self.c.items())

delta = Poly({(1, 0): 1})
p = Poly({(0, 1): 1})
theta = Q(874861, 1000000)
h = Q(3969737987, 5000000000)
ell = Q(11, 3) - 4 * theta
x, y = 1 + ell - h, h - 2 * ell
ks = 2 * theta - 1
Lam = Q(19312, 4787)
B0, epscell, alpha = Q(14200, 14361), Q(1, 100000), Q(1, 400000)
B = B0 - epscell
dm, dp, d0, t0 = h - Q(1, 1000), h + Q(1, 10**10), Q(1, 200), Q(1, 1000)
q0, Ka = Q(17, 25), Q(34, 21)
rho = lambda d: 1 - 10 * d / (3 * (5 - 2 * d))
rho0 = rho(q0)
eq("constant_high_slope", q0 * (Lam - 1) - Ka * (5 - 6 * rho0) * (Q(9, 2) - Lam), 0)
eq("ell", ell, "125417/750000")
eq("x", x, "5599126039/15000000000")
eq("y", y, "6892533961/15000000000")
eq("upper_d", dp, "317579039/400000000")
mins = {}
for j in (1, 600):
    bj = Q(17, 500) + j * epscell
    gj = B - 1 + (Q(9, 2) - Lam) * bj
    aj = Ka * gj + alpha
    Aj = B - (Lam - 1) * (bj - epscell)
    vals = {
        "low": aj * (1 - 4 * q0 / 3) - 2 * q0 * gj / 9,
        "high": 1 - rho0 - q0 * Aj - aj * (5 - 6 * rho0),
        "error_one": aj / 4 - gj / 6,
        "error_six": 13 * aj / 4 - gj / 6,
        "error_seven": 4 * aj - gj / 6,
        "second_zero": 1 - Aj - 5 * aj,
        "main_exceptional": 1 - Aj - 4 * aj,
        "error_exceptional": 1 - Aj - 9 * aj,
    }
    for key, value in vals.items():
        mins[key] = min(mins.get(key, value), value)
expected = {
    "low": "7/30000000", "high": "720486667/30493190000000",
    "error_one": "530959781/482529600000", "error_six": "11360006033/482529600000",
    "error_seven": "3516816899/120632400000", "second_zero": "8754683599/120632400000",
    "main_exceptional": "127361803/1507905000", "error_exceptional": "988504553/40210800000",
}
for key, value in mins.items():
    eq("atlas_" + key, value, expected[key])
    assert value > 0
amax=Q(289458497,24126480000)
Amax=Q(1271830639,1436100000)
eq("high_derivative_lower",50*(1-6*amax)/(3*(5-2*q0)**2)-Amax,
   "4397519373071/15608701631250")
eq("high_constant_formula",Q(81379,15925)*(B0-B)-Q(9877,4787)*epscell-Q(249,91)*alpha,
   "720486667/30493190000000")
pos("d_slope_below_two",2-(Q(33,50)+Q(3,8)*(2-B)/(2*Lam)))

nmin, nmax = 1 - y / dm, 1 - y / dp + t0
zmin, zmax = (B - 2*nmax)/Lam, (B - 2*nmin)/Lam
eq("nmin", nmin, "5001680000/11894213961")
eq("nmax", nmax, "402287137237/952737117000")
eq("zmin", zmin, "65807969436717121/1839925920350400000")
eq("zmax", zmax, "841262571937768693/22970106001483200000")
pos("plain_upper_gap", Q(264, 625) - nmax)
pos("slot_upper_gap", Q(37, 1000) - zmax)
pos("slot_lower_gap", zmin - Q(17, 500))
eq("complement_small_slot", 1 - 2*Q(264,625) - Q(9,2)*Q(17,500), "11/5000")
eq("complement_short_plain", 1 - Q(41,100) - Q(264,625) - Q(9,2)*Q(37,1000), "11/10000")
pos("actual_supply", ell-dp*zmax)
eq("detector_supply", ell/dp-Q(4,21), "44784748/2223053273")
eq("lower_supply", 2*ell-Q(1,3), "139/125000")
eq("four_ell_y", 4*ell-y, "1046942013/5000000000")
bmax=2*y/dm-1
eq("bmax", bmax, "1890853961/11894213961")
pos("bmax_below_4_25", Q(4,25)-bmax)
oldz = lambda b,t: max(Q(0),(b-2*t)/Q(9,2))
shift = lambda b,t: t/2-((b-(1-B))/Lam-oldz(b,t))/4
eq("shift_coarse",shift(Q(4,25),t0),"4035883/69523200000")
eq("shift_exact",shift(bmax,t0),"7636096506749509/118131973721913600000")
capacity = lambda d,new: (2*y-(2-B)*d)/Lam if new else (2*y-d)/(6*ks)
eq("junction",capacity(dm,True)-capacity(dm,False),"33165294566691730080019/32576920344000000000000000")
eq("extension",Q(1,10**6)-2*(dp-h),"4999/5000000000")
eq("floor",theta-(Q(51,100)+h/3+Q(51,100)*ell),"223923613/15000000000")
eq("lower_row",theta-(Q(7,8)-49*h/150+7*ell/8+33*d0/50),"82198036363/750000000000")
eq("small_row",-(13*h/75-y/2+63*d0/50),"21458387121/250000000000")
eq("principal_w",y/20-(1+h)/1000-Q(1,4000),"313967484089/15000000000000")
eq("principal_z",h/600-Q(1,1000)-Q(1,4000),"219737987/3000000000000")
eq("probe_first",y-2*x+ell,"-599126039/5000000000")
eq("probe_second",1+3*ell-2*(x+y),"-24583/150000")
eq("probe_boundary",(5*x+y)/12-(theta-(Q(5,6)-x/3-ell/6)),0)
eq("local_feedback",5*dp/288,"317579039/23040000000")
eq("old_feedback",Q(5,288)+Q(3,8)*Q(1,2)/(12*Q(7,10)**2),"695/14112")

D=3-p-2*p/(3*ks)
P=2*(1-p)*(1-p/(3*ks))
V=Q(5,6)-delta
J=V*D+delta*P
eq("J_positive_lower_bound",D.at(Q(0),Q(1,2))/12,"4622915/26989992")
pos("J_actual_corner",J.at(Q(3,4),Q(1,2)))
def numerator(d,v,new):
    C=capacity(d,new)
    return J*(theta-v-(1+delta)/2-13*h/75+y/2+ell/2-ell*delta*p-d*(Q(1,4)-Q(17,50))+delta*p*C/2)-3*d*((1-delta)*J+delta*P*V/2)/4

def bernstein(poly, box):
    a,b,c,d=map(Q,box)
    f={}
    for (i,j),value in poly.c.items():
        for r in range(i+1):
            for s in range(j+1):
                key=(r,s)
                f[key]=f.get(key,Q(0))+value*comb(i,r)*a**(i-r)*(b-a)**r*comb(j,s)*c**(j-s)*(d-c)**s
    return [sum(f.get((r,s),Q(0))*Q(comb(i,r),comb(2,r))*Q(comb(j,s),comb(3,s))
                for r in range(i+1) for s in range(j+1))
            for i in range(3) for j in range(4)]

rp=HERE/"endpoint-receipt.json"
receipt=json.loads(rp.read_text(encoding="utf-8-sig"))
assert bind(rp)["sha256"]=="95949e70cddd9964089b519c452fc0683e864747f8f269e41986c905332d0756"
certresults=[]
for cert in receipt["certificates"]:
    new=cert["name"]=="shaped_upper"
    d,v=Q(cert["d"]),Q(cert["saving"])
    poly=numerator(d,v,new)
    recorded={tuple(map(int,k.split(","))):Q(value) for k,value in cert["power_coefficients"].items() if Q(value)}
    assert poly.c==recorded,(cert["name"],"power polynomial")
    boxes=[tuple(map(Q,leaf["box"])) for leaf in cert["leaves"]]
    assert sum((b-a)*(d1-c) for a,b,c,d1 in boxes)==Q(3,8)
    for i,(a,b,c,d1) in enumerate(boxes):
        assert 0<=a<b<=Q(3,4) and 0<=c<d1<=Q(1,2)
        for a2,b2,c2,d2 in boxes[i+1:]:
            assert max(a,a2)>=min(b,b2) or max(c,c2)>=min(d1,d2)
    allcoeff=[]
    for leaf in cert["leaves"]:
        coeff=bernstein(poly,leaf["box"])
        assert coeff==list(map(Q,leaf["coefficients"])),cert["name"]
        assert min(coeff)>0
        assert min(coeff)==Q(leaf["lower"]) and max(coeff)==Q(leaf["upper"])
        allcoeff+=coeff
    assert min(allcoeff)==Q(cert["minimum"])
    certresults.append({"name":cert["name"],"boxes":len(boxes),"coefficients":len(allcoeff),"minimum":str(min(allcoeff)),"polynomial_identity":True,"cover_and_disjoint_interiors":True})
assert sum(c["coefficients"] for c in certresults)==156

out={"status":"PASS exact rational reconstruction; not formalization",
     "utc":datetime.now(timezone.utc).isoformat(),
     "source_receipt":bind(rp),"scalar_checks":CHECKS,
     "certificates":certresults,"source_code_imported_or_run":False,
     "helper":bind(Path(__file__))}
(HERE/"rational-receipt.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
print(json.dumps({"status":out["status"],"scalar_count":len(CHECKS),"coefficients":156,"receipt":bind(HERE/"rational-receipt.json")}))
