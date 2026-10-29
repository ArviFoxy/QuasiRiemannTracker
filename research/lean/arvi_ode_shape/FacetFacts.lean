/-
The two scalar conditions of the facet bound (`facets_ge_facet12_of_N10`) along the curve.

`slQ`: a polynomial lower bound for the chord slope (`β'(Λ₀) - 10⁻⁶`). For every parent `t` and every density
`ν ∈ [q_min(t), 3/4]`, written `ν = (N + z(3/4·Dq - N))/Dq` with `z ∈ [0, 1]`, `q_min = N/Dq`,
`Dq = F + 11·10⁻⁴`, the conditions N₁₀ and P₁₂ at `S = sl(t)`, `Q = 1` hold (multiplied by `Dq²`). Kernel checks.
-/
import Submissions.arvi_ode_shape.High

set_option autoImplicit false

namespace QRH.ArviOdeShape
open QRH.ArviReturnTuning

/-- The derivative of a polynomial in `t` (coefficient list). -/
def derivQ1 (p : Q1) : Q1 := (p.drop 1).zipIdx.map (fun (c, i) => ((i + 1 : ℕ) : ℚ) * c)

/-- The slope lower bound `sl(t) = P'(t)/Lh - 10⁻⁶`, a polynomial in `t`. -/
def slQ : Q2 := Q2.sub (ofQ1X (Q1.smul (1/Lh) (derivQ1 curveQ))) (Q2.C (1/1000000))

/-- The chord slope exceeds `sl(t)` on `[-1, 1] × [0, hmax]`. -/
def chordSlQ : Q2 := Q2.sub chordQ slQ
theorem chordSlQ_pos : posBox chordSlQ 14 (-1) 1 0 hmax = true := by decide +kernel

/-- `Dq = F + 11/10000`, `νn = N + z(3/4 Dq - N)` (so `ν = νn/Dq`), `wn = 5 Dq - 6 νn`. -/
def DqQ : Q2 := Q2.add FQ (Q2.C (11/10000))
def νnQ : Q2 := Q2.add NQ (Q2.mul Q2.Y (Q2.sub (Q2.smul (3/4) DqQ) NQ))
def wnQ : Q2 := Q2.sub (Q2.smul 5 DqQ) (Q2.smul 6 νnQ)
/-- `DL·Dq = (Λ₀-1)(25 Dq - 18 νn) + wn`. -/
def DLnQ : Q2 := Q2.add (Q2.mul (Q2.sub LQ (Q2.C 1)) (Q2.sub (Q2.smul 25 DqQ) (Q2.smul 18 νnQ))) wnQ
/-- `E·Dq = wn (B₀Λ₀ - 4B₀ - 4Λ₀² + 6Λ₀) + 10 Λ₀ (1 - B₀) Dq`. -/
def EnQ : Q2 :=
  Q2.add (Q2.mul wnQ (Q2.add (Q2.sub (Q2.sub (Q2.mul BQ LQ) (Q2.smul 4 BQ)) (Q2.smul 4 (Q2.mul LQ LQ)))
      (Q2.smul 6 LQ)))
    (Q2.mul (Q2.smul 10 (Q2.mul LQ (Q2.sub (Q2.C 1) BQ))) DqQ)
/-- N₁₀ at `S = sl`, `Q = 1`: `5 sl (wn² + 5 wn Dq + 10 Dq²) - 2 wn² > 0`. -/
def p10Q : Q2 := Q2.sub (Q2.smul 5 (Q2.mul slQ (Q2.add (Q2.add (Q2.mul wnQ wnQ) (Q2.smul 5 (Q2.mul wnQ DqQ)))
    (Q2.smul 10 (Q2.mul DqQ DqQ))))) (Q2.smul 2 (Q2.mul wnQ wnQ))
/-- P₁₂ at `S = sl`, `Q = 1`: `sl·DLn² + wn·En > 0`. -/
def p12Q : Q2 := Q2.add (Q2.mul slQ (Q2.mul DLnQ DLnQ)) (Q2.mul wnQ EnQ)

theorem p10Q_pos : posBox p10Q 14 (-1) 1 0 1 = true := by decide +kernel
theorem p12Q_pos : posBox p12Q 16 (-1) 1 0 1 = true := by decide +kernel

end QRH.ArviOdeShape
