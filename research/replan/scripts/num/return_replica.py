"""Floating-point replica of the final-return row certificate of PR 83
(Return/Formulas.lean, Return/Constants.lean). NOT a proof; used only to see which
(delta,p,edge,branch) cells are tight and how theta responds to the source faces."""
import numpy as np
from dataclasses import dataclass, field

EPS7 = 1e-7

@dataclass
class Faces:
    # count face C and physical face P (the two literal subfaces of the final source G)
    CB: float = 4967/5000
    CL: float = 49/20
    Ccap: float = 9999/100000
    PB: float = 9933999/1e7
    PL: float = 2451/1000
    Pcap: float = 31/500
    numeratorCap: float = 3/50     # physical slot cap (schedule field)
    dm: float = 19/25              # fixed switch
    d0: float = 1/200
    reserve: float = 1e-8
    sMinus: float = 3/100
    mMinus: float = 19/50
    naturalK: float = 9/2

class Ret:
    def __init__(self, c, h, F: Faces):
        self.F = F; self.c = c; self.h = h
        self.theta = 1-c; self.ell = 4*c-1/3
        self.x = 1+self.ell-h; self.y = h-2*self.ell; self.kappa = 1-2*c
        self.dp = h+1e-10
        self.naturalM = (1-F.naturalK*F.sMinus)/2
    # edges
    def oldCap(self, d): return min(d, 2*self.y-d)/(6*self.kappa)
    def newCap(self, d):
        F=self.F
        return min(F.numeratorCap*d, (2*self.y-(2-F.PB)*d)/F.PL)
    def edges(self):
        F=self.F
        return {'oldSmall':(F.d0,self.oldCap(F.d0)),
                'oldSwitch':(F.dm,self.oldCap(F.dm)),
                'newSwitch':(F.dm,self.newCap(F.dm)),
                'newTop':(self.dp,self.newCap(self.dp))}
    def Ebase(self, d, C, dl, p):
        return 0.5+13*self.h/75-self.y/2-self.ell/2-9*d/100+dl/2+dl*p*(self.ell-C/2)
    # branches
    def br(self, b):
        F=self.F
        if b=='C': return F.CB, F.CL, F.Ccap, False
        if b=='capP': return F.PB, F.PL, F.Pcap, True
        raise ValueError
    def parts(self, b, dl, p):
        V = 5/6-dl
        if b=='old':
            k=self.kappa
            oldD = 3-p-2*p/(3*k); oldC = 2*(1-p)*(1-p/(3*k))
            J = V*oldD+dl*oldC
            N = (1-dl)*J+dl*oldC*V/2
            return J, N, None
        B,L,cap,isCap = self.br(b)
        Z_ = cap-EPS7
        D = 3-p if isCap else 3-p-4*p/L
        A = 2+0*p if isCap else 2-4*p/L
        C0 = 1-2*p*Z_ if isCap else 1-2*p*B/L
        Zz = 2*p*Z_ if isCap else 2*p*B/L
        U = (1-p)*C0
        J = V*D+dl*(1-p)*A
        N = (1-dl)*J+V*dl*U
        T = J+dl*U
        RN = A*T+(Zz-p)*J
        MN = D*T-RN
        DJ = D*J
        return J, N, dict(V=V,D=D,A=A,C0=C0,Z=Zz,U=U,T=T,RN=RN,MN=MN,DJ=DJ,B=B,L=L,cap=cap,isCap=isCap)
    def guards(self, b, dl, p):
        F=self.F
        J,N,q = self.parts(b,dl,p)
        B,L,cap,isCap = q['B'],q['L'],q['cap'],q['isCap']
        Z_ = cap-EPS7
        if isCap:
            lowerM = F.mMinus+EPS7
            upperM = min(min(11/25-EPS7, self.naturalM-EPS7), (B-L*Z_)/2-EPS7)
            dD,dA,dC = -1.0, 0.0, -2*Z_
        else:
            lowerM = max(F.mMinus+EPS7,(B-L*(cap-EPS7))/2+EPS7)
            upperM = min(min(11/25-EPS7, self.naturalM-EPS7),(B-L*(F.sMinus+EPS7))/2-EPS7)
            dD,dA,dC = -1-4/L, -4/L, -2*B/L
        dU = -q['C0']+(1-p)*dC
        dJ = q['V']*dD+dl*(-q['A']+(1-p)*dA)
        g = [q['D'], q['A'], q['C0'], J, q['T']-J, 12499/10000*J-q['T'],
             q['RN']-(23/37)*q['DJ'], q['DJ']-q['RN'],
             q['MN']-lowerM*q['DJ'], upperM*q['DJ']-q['MN'],
             N-(1-2*dl*self.naturalM-2*dl*p*F.sMinus)*J,
             q['U']*dJ-dU*J,
             11/25-self.naturalM-EPS7 + 0*dl,
             B-2*self.naturalM-L*(F.sMinus+EPS7)-2*EPS7 + 0*dl,
             ((Z_-F.sMinus-EPS7)*q['DJ']) if isCap else 1+0*dl]
        return g
    def admitted(self, b, dl, p):
        g = self.guards(b,dl,p)
        ok = np.ones_like(dl, dtype=bool)
        for gi in g: ok &= (gi>0)
        return ok
    def needed(self, e, b, dl, p):
        """minimal theta-reserve needed at (dl,p) on edge e using branch b: Ebase+3/4 d N/J"""
        d,C = self.edges()[e]
        J,N,_ = self.parts(b,dl,p)
        return self.Ebase(d,C,dl,p)+0.75*d*N/J

def grid(n=301):
    dl = np.linspace(0,0.75,n); p = np.linspace(0,0.5,n)
    return np.meshgrid(dl,p,indexing='ij')

def slack(r: Ret, n=301, verbose=False):
    DL,P = grid(n)
    out = {}
    for e in r.edges():
        best = r.needed(e,'old',DL,P)
        src = np.zeros_like(DL, dtype=int)  # 0 old
        for bi,b in enumerate(['C','capP'],1):
            adm = r.admitted(b,DL,P)
            nd = r.needed(e,b,DL,P)
            upd = adm & (nd<best)
            best = np.where(upd, nd, best); src = np.where(upd, bi, src)
        out[e]=(best,src)
    worst = {}
    for e,(best,src) in out.items():
        i = np.unravel_index(np.argmax(best), best.shape)
        worst[e] = (best[i], DL[i], P[i], ['old','C','capP'][src[i]])
    return worst, out

if __name__=='__main__':
    F = Faces()
    r = Ret(25201/200000, 8053/10000, F)
    worst,_ = slack(r, 601)
    print("theta=%.6f  theta-reserve=%.9f" % (r.theta, r.theta-F.reserve))
    for e,(val,dl,p,b) in worst.items():
        print("%-10s worst needed=%.9f  slack=%+.3e at delta=%.4f p=%.4f using %s" % (e,val,r.theta-F.reserve-val,dl,p,b))
