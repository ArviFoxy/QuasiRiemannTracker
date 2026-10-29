/-
The marked HIGH gate of a density step along the curve.

For `v ∈ [0, vmax]` and `ν ∈ [q(v), 3/4]` the gate `highJ + gainC` is at least the binding pair
`Γ₁₂(v, ν)` (facet `(1,2)` at `p = 1/2`; the facet bound `hfac` is the input from `FacetForms`), which is
nondecreasing in `ν` (`gamma_nu_mono`) and at `ν = q(v)` stays above `q(vmax)·m₀` (`gamma_lower`, the no-dip
bound). The scalar inputs are polynomial facts in `(t, h)` checked by the kernel.
-/
import Submissions.arvi_ode_shape.Gates
import Submissions.arvi_uniform_chain.BindingPair
import Submissions.arvi_uniform_chain.HighCore
import Submissions.arvi_uniform_chain.HighConcrete

set_option autoImplicit false

namespace QRH.ArviOdeShape
open QRH.ArviReturnTuning QRH.ArviDensity QRH.ArviDensity.Hybrid QRH.ArviUniformChain Set

/-! ### Polynomial facts -/

/-- `N = (999/1000) A Λ₀` and `E₀ = h + (6β Λ₀ - Λ₀) A` (so `q(0) = N/E₀`). -/
def NQ : Q2 := Q2.smul (999/1000 * (19/50)) LQ
def E0Q : Q2 := Q2.add Q2.Y (Q2.smul (19/50) (Q2.sub (Q2.smul 6 BQ) LQ))
/-- `25 E₀ - 18 N` and `5 E₀ - 6 N`: `y(q₀) = (5E₀ - 6N)/(25E₀ - 18N)`. -/
def GyQ : Q2 := Q2.sub (Q2.smul 25 E0Q) (Q2.smul 18 NQ)
def HyQ : Q2 := Q2.sub (Q2.smul 5 E0Q) (Q2.smul 6 NQ)
/-- `m₀ > 0`: `s₀ ((Λ₀-1) G + H) - ((β Λ₀ - 1) G + H)` (that is `s₀ > σ(q₀)`). -/
def m0Q : Q2 :=
  Q2.sub (Q2.mul chordQ (Q2.add (Q2.mul (Q2.sub LQ (Q2.C 1)) GyQ) HyQ))
    (Q2.add (Q2.mul (Q2.sub BQ (Q2.C 1)) GyQ) HyQ)
/-- the denominator `(Λ₀-1) G + H` is positive. -/
def m0denQ : Q2 := Q2.add (Q2.mul (Q2.sub LQ (Q2.C 1)) GyQ) HyQ

theorem m0Q_pos : posBox m0Q 16 (-1) 1 0 hmax = true := by decide +kernel
theorem m0denQ_pos : posBox m0denQ 12 (-1) 1 0 hmax = true := by decide +kernel


/-- `F = (6β Λ₀ - Λ₀) A`, so the ideal density is `Q₀ = N/F`; `x(Q₀) = (5F - 6N)/(20F - 12N)` and
`R(Q₀) = Rn/Rd`, `Rn = (Λ₀-1)(20F-12N) + (5F-6N)β Λ₀`, `Rd = (Λ₀-1)(20F-12N) + (5F-6N)Λ₀`. -/
def FQ : Q2 := Q2.smul (19/50) (Q2.sub (Q2.smul 6 BQ) LQ)
def XnQ : Q2 := Q2.sub (Q2.smul 5 FQ) (Q2.smul 6 NQ)
def XdQ : Q2 := Q2.sub (Q2.smul 20 FQ) (Q2.smul 12 NQ)
def RnQ : Q2 := Q2.add (Q2.mul (Q2.sub LQ (Q2.C 1)) XdQ) (Q2.mul XnQ BQ)
def RdQ : Q2 := Q2.add (Q2.mul (Q2.sub LQ (Q2.C 1)) XdQ) (Q2.mul XnQ LQ)
/-- no dip: `N(Λ₀ - 101/100) F Rd - A (6N Rn - N Rd - F Rd)(F + 11 hmax) > 0`, i.e.
`A·C₁₂(Q₀) < q_min·(Λ₀ - 1 - 1/100)` with `q_min = N/(F + 11 hmax)`. -/
def nodipQ : Q2 :=
  Q2.sub (Q2.mul (Q2.mul (Q2.mul NQ (Q2.sub LQ (Q2.C (101/100)))) FQ) RdQ)
    (Q2.smul (19/50) (Q2.mul (Q2.sub (Q2.sub (Q2.smul 6 (Q2.mul NQ RnQ)) (Q2.mul NQ RdQ)) (Q2.mul FQ RdQ))
      (Q2.add FQ (Q2.C (11 * hmax)))))
/-- `(Λ₀-1)·Lσ ≤ 1`: `(23/2)²(Λ₀ - 22/23)² - 60(Λ₀ - 1)(Λ₀ - β Λ₀) > 0`. -/
def lsigQ : Q2 := Q2.sub (Q2.smul (529/4) (Q2.pow (Q2.sub LQ (Q2.C (22/23))) 2))
  (Q2.smul 60 (Q2.mul (Q2.sub LQ (Q2.C 1)) (Q2.sub LQ BQ)))
/-- `6·(3/4)·KR ≤ 4`: `484(Λ₀ - 1) - 270(Λ₀ - β Λ₀) > 0`. -/
def krQ : Q2 := Q2.sub (Q2.smul 484 (Q2.sub LQ (Q2.C 1))) (Q2.smul 270 (Q2.sub LQ BQ))
/-- ν-monotonicity: `30(Λ₀-1)(Λ₀ - β Λ₀) - (64/5)(Λ₀ - 7/8)² > 0`. -/
def nQ : Q2 := Q2.sub (Q2.smul 30 (Q2.mul (Q2.sub LQ (Q2.C 1)) (Q2.sub LQ BQ)))
  (Q2.smul (64/5) (Q2.pow (Q2.sub LQ (Q2.C (7/8))) 2))
/-- `22/23 < β Λ₀ < 1`. -/
def blQ : Q2 := Q2.sub BQ (Q2.C (22/23))
def bhQ : Q2 := Q2.sub (Q2.C 1) BQ

theorem nodipQ_pos : posBox nodipQ 14 (-1) 1 0 hmax = true := by decide +kernel
theorem lsigQ_pos : posBox lsigQ 10 (-1) 1 0 hmax = true := by decide +kernel
theorem krQ_pos : posBox krQ 10 (-1) 1 0 hmax = true := by decide +kernel
theorem nQ_pos : posBox nQ 10 (-1) 1 0 hmax = true := by decide +kernel
theorem blQ_pos : posBox blQ 10 (-1) 1 0 hmax = true := by decide +kernel
theorem bhQ_pos : posBox bhQ 10 (-1) 1 0 hmax = true := by decide +kernel


/-! ### The real facts at one step -/

/-- All scalar facts of the step `(t, h)` on the reals, with `L₀ = Lr t`, `B₀ = Br t`, `s = Sr t h`,
`N = (999/1000)(19/50) L₀`, `F = (19/50)(6B₀ - L₀)`. -/
structure StepFacts (L0 B0 s h : ℝ) : Prop where
  h_pos : 0 < h
  h_le : h ≤ 1/10000
  L_lo : 4819/2500 ≤ L0
  L_hi : L0 ≤ 5143/2000
  s_lo : 1/50 < s
  s_hi : s < 1/10
  six : 3 < 6 * B0 - L0
  up : 999/1000 * L0 < 3/4 * (6 * B0 - L0)
  floor : h * (1 + 100 * (1/10 - s)) < 19/50 * (1499/500 * L0 - 6 * B0)
  B_lo : 22/23 < B0
  B_hi : B0 < 1
  m0 : 0 < s * ((L0 - 1) * (25 * (h + 19/50 * (6 * B0 - L0)) - 18 * (999/1000 * (19/50) * L0)) +
      (5 * (h + 19/50 * (6 * B0 - L0)) - 6 * (999/1000 * (19/50) * L0))) -
    ((B0 - 1) * (25 * (h + 19/50 * (6 * B0 - L0)) - 18 * (999/1000 * (19/50) * L0)) +
      (5 * (h + 19/50 * (6 * B0 - L0)) - 6 * (999/1000 * (19/50) * L0)))
  lsig : 60 * ((L0 - 1) * (L0 - B0)) < 529/4 * (L0 - 22/23) ^ 2
  kr : 270 * (L0 - B0) < 484 * (L0 - 1)
  nmono : 64/5 * (L0 - 7/8) ^ 2 < 30 * ((L0 - 1) * (L0 - B0))
  nodip : 19/50 * ((6 * (999/1000 * (19/50) * L0 * ((L0 - 1) * (20 * (19/50 * (6 * B0 - L0)) -
        12 * (999/1000 * (19/50) * L0)) + (5 * (19/50 * (6 * B0 - L0)) - 6 * (999/1000 * (19/50) * L0)) * B0)) -
      999/1000 * (19/50) * L0 * ((L0 - 1) * (20 * (19/50 * (6 * B0 - L0)) - 12 * (999/1000 * (19/50) * L0)) +
        (5 * (19/50 * (6 * B0 - L0)) - 6 * (999/1000 * (19/50) * L0)) * L0) -
      19/50 * (6 * B0 - L0) * ((L0 - 1) * (20 * (19/50 * (6 * B0 - L0)) - 12 * (999/1000 * (19/50) * L0)) +
        (5 * (19/50 * (6 * B0 - L0)) - 6 * (999/1000 * (19/50) * L0)) * L0)) *
      (19/50 * (6 * B0 - L0) + 11/10000)) <
    999/1000 * (19/50) * L0 * (L0 - 101/100) * (19/50 * (6 * B0 - L0)) *
      ((L0 - 1) * (20 * (19/50 * (6 * B0 - L0)) - 12 * (999/1000 * (19/50) * L0)) +
        (5 * (19/50 * (6 * B0 - L0)) - 6 * (999/1000 * (19/50) * L0)) * L0)

theorem stepFacts {t h : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (hh : 0 < h) (hh' : h ≤ hmax) :
    StepFacts (Lr t) (Br t) (Sr t h) h := by
  have hev : ∀ {P : Q2} {k : ℕ}, posBox P k (-1) 1 0 hmax = true → 0 < Q2.ev P t h :=
    fun hP => posBox_ev hP ht hh.le hh'
  have f1 := hev slopePosQ_pos
  have f2 := hev slopeLtQ_pos
  have f3 := hev sixQ_pos
  have f4 := hev upQ_pos
  have f5 := hev floorQ_pos
  have g1 := hev m0Q_pos
  have g3 := hev nodipQ_pos
  have g4 := hev lsigQ_pos
  have g5 := hev krQ_pos
  have g6 := hev nQ_pos
  have g7 := hev blQ_pos
  have g8 := hev bhQ_pos
  simp only [slopePosQ, slopeLtQ, sixQ, upQ, floorQ, m0Q, GyQ, HyQ, E0Q, NQ, lsigQ, krQ, nQ, blQ, bhQ,
    nodipQ, FQ, XnQ, XdQ, RnQ, RdQ,
    Q2.ev_add, Q2.ev_sub, Q2.ev_mul, Q2.ev_smul, Q2.ev_C, Q2.ev_Y, Q2.ev_pow, ev_LQ', ev_BQ',
    ev_chordQ'] at f1 f2 f3 f4 f5 g1 g3 g4 g5 g6 g7 g8
  norm_num [selA, selD, hmax] at f1 f2 f3 f4 f5 g1 g3 g4 g5 g6 g7 g8
  have hL := Lr_mem ht
  norm_num [La, Lb] at hL
  have hh'' : h ≤ 1/10000 := by simpa [hmax] using hh'
  exact ⟨hh, hh'', hL.1, hL.2, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

end QRH.ArviOdeShape
