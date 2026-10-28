"""Common definitions for the transport-box study (TB_transport_box.md).

Everything is exact (Fractions).  The transport layer of PR 83 / PR 86 (ReturnD/TransportGeometry.lean:19, class
`BoundsN`) is a box on the five scalar parameters (theta, h, y, ell, x).  They are not independent: the signal
boundary field of `Geometry.Parameters` gives (ReturnD/TransportGeometry.lean:40, `ell_eq`, `x_eq`, `y_eq`)

    ell = 11/3 - 4*theta,     x = 1 + ell - h,     y = h - 2*ell,     dPlus = h + 1e-10.

So the actual point is a function of (theta, h), and the box is a polygon in the (theta, h) plane.
"""
from fractions import Fraction as F
from dataclasses import dataclass, replace

TEN10 = F(1, 10**10)


def ell_of(theta):
    return F(11, 3) - 4 * theta


def x_of(theta, h):
    return 1 + ell_of(theta) - h


def y_of(theta, h):
    return h - 2 * ell_of(theta)


def dplus_of(h):
    return h + TEN10


def signal_of(theta, h):
    """signal theta = x/2 + (y-x)/12   (Assembly.signal_at_boundary, TransportGeometry.lean:77)"""
    x, y = x_of(theta, h), y_of(theta, h)
    return x / 2 + (y - x) / 12


def small_saving_val(theta, h):
    """y/2 - h*(17/50-1/6) - 1/50   (field small_saving: 7/100 < this)"""
    y = y_of(theta, h)
    return y / 2 - h * (F(17, 50) - F(1, 6)) - F(1, 50)


def floor_lhs(theta, h):
    """4/25 x - 3/20 - 51/100 y + 67/100 dPlus - 3/20 ell   (field floor_margin: lhs <= signal theta - 1/200)"""
    x, y, ell = x_of(theta, h), y_of(theta, h), ell_of(theta)
    return F(4, 25) * x - F(3, 20) - F(51, 100) * y + F(67, 100) * dplus_of(h) - F(3, 20) * ell


def floor_slack(theta, h, margin=F(1, 200)):
    """signal theta - margin - lhs   (>= 0 is the field floor_margin)"""
    return signal_of(theta, h) - margin - floor_lhs(theta, h)


@dataclass(frozen=True)
class Box:
    name: str
    theta_lo: F = F(873, 1000)
    theta_hi: F = F(7, 8)
    h_lo: F = F(793, 1000)
    h_hi: F = F(806, 1000)
    y_lo: F = F(458, 1000)
    y_hi: F = F(467, 1000)
    ell_lo: F = F(1672, 10000)
    ell_hi: F = F(171, 1000)
    ss: F = F(7, 100)          # small_saving constant
    fm: F = F(1, 200)          # floor_margin constant (the loss budget `htotal` of CubeFloorSaving)

    def w(self, **kw):
        return replace(self, **kw)


COLLET = Box('Collet Bounds', theta_lo=F(874, 1000), h_hi=F(802, 1000), y_hi=F(466, 1000), ell_hi=F(1677, 10000))
PR76 = Box('PR76 BoundsR', theta_lo=F(874, 1000), h_hi=F(803, 1000), ell_hi=F(1690, 10000))
PR83 = Box('PR83/86 BoundsN')           # the current box
W_CALLER = PR83.w(name='caller example: theta>0.8735, ell<0.175', theta_lo=F(8735, 10000), ell_hi=F(175, 1000))
W_MIN = PR83.w(name='minimal: ell<0.1715', ell_hi=F(1715, 10000))
W_WIDE = PR83.w(name='ell<0.175 (theta>0.873 kept)', ell_hi=F(175, 1000))
W_FUT = PR83.w(name='future-proof: ell<0.175, y>0.44, ss=0.06', ell_hi=F(175, 1000), y_lo=F(440, 1000), ss=F(60, 1000))


def constraints(box):
    """half-planes  a*theta + b*h + c  >(=) 0   describing the box in the (theta,h) plane, with names.
    strictness is ignored (closure)."""
    cons = []
    # theta
    cons.append(('theta>lo', F(1), F(0), -box.theta_lo))
    cons.append(('theta<hi', F(-1), F(0), box.theta_hi))
    # h
    cons.append(('h>lo', F(0), F(1), -box.h_lo))
    cons.append(('h<hi', F(0), F(-1), box.h_hi))
    # ell = 11/3 - 4 theta
    cons.append(('ell>lo', F(-4), F(0), F(11, 3) - box.ell_lo))
    cons.append(('ell<hi', F(4), F(0), box.ell_hi - F(11, 3)))
    # y = h - 2 ell = h - 22/3 + 8 theta
    cons.append(('y>lo', F(8), F(1), -F(22, 3) - box.y_lo))
    cons.append(('y<hi', F(-8), F(-1), F(22, 3) + box.y_hi))
    # small saving: 49 h/150 - ell - 1/50 - ss > 0 -> 49h/150 - 11/3 + 4 theta - 1/50 - ss
    cons.append(('small_saving', F(4), F(49, 150), -F(11, 3) - F(1, 50) - box.ss))
    # floor margin: slack(theta,h) >= 0, slack is affine in (theta,h): evaluate by differences
    s00 = floor_slack(F(0), F(0), box.fm)
    a = floor_slack(F(1), F(0), box.fm) - s00
    b = floor_slack(F(0), F(1), box.fm) - s00
    cons.append(('floor_margin', a, b, s00))
    return cons


def polygon(box):
    """vertices of the feasible polygon in the (theta,h) plane (exact), sorted counter-clockwise"""
    cons = constraints(box)
    pts = []
    n = len(cons)
    for i in range(n):
        for j in range(i + 1, n):
            _, a1, b1, c1 = cons[i]
            _, a2, b2, c2 = cons[j]
            det = a1 * b2 - a2 * b1
            if det == 0:
                continue
            th = (-c1 * b2 + c2 * b1) / det
            h = (-a1 * c2 + a2 * c1) / det
            if all(a * th + b * h + c >= 0 for _, a, b, c in cons):
                if (th, h) not in pts:
                    pts.append((th, h))
    if not pts:
        return []
    cx = sum(p[0] for p in pts) / len(pts)
    cy = sum(p[1] for p in pts) / len(pts)
    import math
    pts.sort(key=lambda p: math.atan2(float(p[1] - cy), float(p[0] - cx)))
    return pts


def active_at(box, th, h):
    out = []
    for nm, a, b, c in constraints(box):
        if a * th + b * h + c == 0:
            out.append(nm)
    return out


def h_floor_max(theta, margin=F(1, 200)):
    """largest h allowed by floor_margin (slack affine in h, decreasing)"""
    s0 = floor_slack(theta, F(0), margin)
    s1 = floor_slack(theta, F(1), margin)
    slope = s1 - s0
    return -s0 / slope


def h_small_saving_min(theta, ss=F(7, 100)):
    """smallest h with small_saving > ss"""
    s0 = small_saving_val(theta, F(0)) - ss
    s1 = small_saving_val(theta, F(1)) - ss
    slope = s1 - s0
    return -s0 / slope


def h_y_lo_min(theta, y_lo=F(458, 1000)):
    return y_lo + 2 * ell_of(theta)


def fl(x, nd=7):
    return ('%.' + str(nd) + 'f') % float(x)
