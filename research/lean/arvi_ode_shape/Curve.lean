/-
The explicit curve of the continuous energy region estimate.

The curve is `Λ ↦ (β Λ, Λ)` on `[La, Lb]`, with `β Λ = P((Λ - Lm)/Lh)` for a degree-6 polynomial `P` (seven
rational coefficients, `curveQ`); it lies below the ODE solution with margin `η = 10⁻⁴`
(`research/face-region/odeshape/curve_fit.py`). One density step along the curve goes from the parent
`(β Λ₀, Λ₀)` to the child `(β (Λ₀ - h), Λ₀ - h)` with the chord slope `s₀ = (β Λ₀ - β (Λ₀ - h))/h`.
In the variables `t = (Λ₀ - Lm)/Lh ∈ [-1, 1]` and `h ∈ [0, h₀]` all of `Λ₀`, `β Λ₀`, `β (Λ₀ - h)` and `s₀` are
polynomials (`LQ`, `BQ`, `BchildQ`, `chordQ`), so every scalar condition of the step is a polynomial positivity
on a box, checked by the kernel (`posBox`, `research/lean/arvi_return_tuning/Poly2.lean`).
-/
import Submissions.arvi_return_tuning.Poly2

set_option autoImplicit false

namespace QRH.ArviOdeShape
open QRH.ArviReturnTuning

/-- The ends of the curve, its midpoint and half-length: `t = (Λ - Lm)/Lh ∈ [-1, 1]`. -/
def La : ℚ := 19276/10000
def Lb : ℚ := 5143/2000
def Lm : ℚ := 44991/20000
def Lh : ℚ := 6439/20000
/-- The longest step of the induction. -/
def hmax : ℚ := 1/10000

/-- The curve `P(t)`, lowest degree first. -/
def curveQ : Q1 :=
  [492802907603/500000000000, 961170757/50000000000, -4242233647/1000000000000,
    -443200117/1000000000000, -5873391/50000000000, -7101517/250000000000, -1605539/200000000000]

/-- A polynomial in `t` alone, as a polynomial in `(t, h)`. -/
def ofQ1X (p : Q1) : Q2 := p.map (fun c => [c])

/-- `p(x)` for a polynomial `x` in `(t, h)` (Horner). -/
def comp (p : Q1) (x : Q2) : Q2 := p.foldr (fun c acc => Q2.add (Q2.C c) (Q2.mul x acc)) []

/-- The `h⁰` part and the quotient by `h`. -/
def h0part (P : Q2) : Q2 := P.map (fun c => [c.headD 0])
def divH (P : Q2) : Q2 := P.map List.tail

/-- `Λ₀ = Lm + Lh t`. -/
def LQ : Q2 := Q2.add (Q2.C Lm) (Q2.smul Lh Q2.X)
/-- `β Λ₀`. -/
def BQ : Q2 := ofQ1X curveQ
/-- `(Λ₀ - h - Lm)/Lh = t - h/Lh`. -/
def tChildQ : Q2 := Q2.sub Q2.X (Q2.smul (1/Lh) Q2.Y)
/-- `β (Λ₀ - h)`. -/
def BchildQ : Q2 := comp curveQ tChildQ
/-- The chord slope `(β Λ₀ - β (Λ₀ - h))/h`. -/
def chordQ : Q2 := divH (Q2.sub BQ BchildQ)

theorem ev_ofQ1X (p : Q1) (d q : ℝ) : Q2.ev (ofQ1X p) d q = Q1.ev p d := by
  induction p with
  | nil => simp [ofQ1X]
  | cons c p ih =>
    simp only [ofQ1X, List.map_cons, Q2.ev_cons, Q1.ev_cons, Q1.ev_nil] at ih ⊢
    rw [ih]; ring

theorem ev_comp (p : Q1) (x : Q2) (d q : ℝ) : Q2.ev (comp p x) d q = Q1.ev p (Q2.ev x d q) := by
  induction p with
  | nil => simp [comp]
  | cons c p ih =>
    have : comp (c :: p) x = Q2.add (Q2.C c) (Q2.mul x (comp p x)) := rfl
    rw [this, Q2.ev_add, Q2.ev_mul, Q2.ev_C, ih, Q1.ev_cons]

theorem Q1_ev_split (c : Q1) (q : ℝ) : Q1.ev c q = ((c.headD 0 : ℚ) : ℝ) + q * Q1.ev c.tail q := by
  cases c with
  | nil => simp
  | cons a cs => simp

theorem ev_split (P : Q2) (d q : ℝ) :
    Q2.ev P d q = Q2.ev (h0part P) d q + q * Q2.ev (divH P) d q := by
  induction P with
  | nil => simp [h0part, divH]
  | cons c P ih =>
    simp only [h0part, divH, List.map_cons, Q2.ev_cons] at ih ⊢
    rw [ih, Q1_ev_split c q]
    simp only [Q1.ev_cons, Q1.ev_nil]
    ring

/-- `β` on the reals. -/
noncomputable def beta (L : ℝ) : ℝ := Q1.ev curveQ ((L - Lm) / Lh)

theorem Lh_pos : (0 : ℝ) < (Lh : ℝ) := by norm_num [Lh]

theorem ev_LQ (t h : ℝ) : Q2.ev LQ t h = (Lm : ℝ) + Lh * t := by
  simp [LQ, Q2.ev_add, Q2.ev_smul]

theorem ev_BQ (t h : ℝ) : Q2.ev BQ t h = beta (Lm + Lh * t) := by
  rw [BQ, ev_ofQ1X, beta]
  congr 1
  field_simp [Lh_pos.ne']
  ring

theorem ev_BchildQ (t h : ℝ) : Q2.ev BchildQ t h = beta (Lm + Lh * t - h) := by
  rw [BchildQ, ev_comp, beta]
  congr 1
  simp only [tChildQ, Q2.ev_sub, Q2.ev_X, Q2.ev_smul, Q2.ev_Y]
  have hL : (Lh : ℝ) ≠ 0 := Lh_pos.ne'
  push_cast
  field_simp
  ring

theorem chord_h0part : Q2.isZero (h0part (Q2.sub BQ BchildQ)) = true := by decide +kernel

/-- The chord identity: `β Λ₀ - β (Λ₀ - h) = h · s₀`. -/
theorem ev_chordQ (t h : ℝ) :
    beta (Lm + Lh * t) - beta (Lm + Lh * t - h) = h * Q2.ev chordQ t h := by
  have hs := ev_split (Q2.sub BQ BchildQ) t h
  rw [Q2.ev_of_isZero _ chord_h0part, Q2.ev_sub, ev_BQ, ev_BchildQ] at hs
  rw [chordQ, hs]; ring

/-! ### A first condition: the density floor `q(vmax) > 1/2` along the curve -/

def selA : ℚ := 19/50
def selD : ℚ := 100

/-- `A (2·0.999 Λ₀ - 6 β Λ₀ + Λ₀) - h (1 + D (1/10 - s₀))`. -/
def floorQ : Q2 :=
  Q2.sub (Q2.smul selA (Q2.sub (Q2.smul (2998/1000) LQ) (Q2.smul 6 BQ)))
    (Q2.mul Q2.Y (Q2.add (Q2.C 1) (Q2.smul selD (Q2.sub (Q2.C (1/10)) chordQ))))

theorem floorQ_pos : posBox floorQ 12 (-1) 1 0 hmax = true := by decide +kernel

end QRH.ArviOdeShape

#print axioms QRH.ArviOdeShape.floorQ_pos
#print axioms QRH.ArviOdeShape.ev_chordQ
