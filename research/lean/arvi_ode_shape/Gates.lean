/-
The one-variable gates of a density step along the curve.

For a parent `t ∈ [-1, 1]` (`Λ₀ = Lm + Lh t`) and a step `0 < h ≤ hmax`, the step goes from `(β Λ₀, Λ₀)` to
`(β (Λ₀ - h), Λ₀ - h) = (β Λ₀ - s₀ h, Λ₀ - h)` with the chord slope `s₀`. Every field of `HybridGatesM` except the
marked HIGH gate follows from `hybridGatesM_of_scalar` and nine polynomial facts in `(t, h)`, each checked by the
kernel on `[-1, 1] × [0, hmax]`.
-/
import Submissions.arvi_ode_shape.Curve
import Submissions.arvi_uniform_chain.Gates1D

set_option autoImplicit false

namespace QRH.ArviOdeShape
open QRH.ArviReturnTuning QRH.ArviDensity QRH.ArviDensity.Hybrid QRH.ArviUniformChain Set

/-! ### The polynomial facts -/

/-- `s₀ - 1/50`. -/
def slopePosQ : Q2 := Q2.sub chordQ (Q2.C (1/50))
/-- `1/10 - s₀`. -/
def slopeLtQ : Q2 := Q2.sub (Q2.C (1/10)) chordQ
/-- `6 β Λ₀ - Λ₀ - 3`. -/
def sixQ : Q2 := Q2.sub (Q2.sub (Q2.smul 6 BQ) LQ) (Q2.C 3)
/-- `(3/4)(6 β Λ₀ - Λ₀) - 0.999 Λ₀` (the density never reaches `3/4`). -/
def upQ : Q2 := Q2.sub (Q2.smul (3/4) (Q2.sub (Q2.smul 6 BQ) LQ)) (Q2.smul (999/1000) LQ)

/-- The three facts of a shape gate `α + β v - γ u(v)` on `[0, T]`, `T = 1/10 - s₀`:
`α > 0`, the cleared value at `T`, and `α D + β - γ A ≥ 0`. -/
def shapeAQ (α : Q2) : Q2 := α
def shapeTQ (α β : Q2) (γ : ℚ) : Q2 :=
  Q2.sub (Q2.mul (Q2.add α (Q2.mul β slopeLtQ)) (Q2.add (Q2.C 1) (Q2.smul selD slopeLtQ)))
    (Q2.smul (γ * selA) slopeLtQ)
def shapeSQ (α β : Q2) (γ : ℚ) : Q2 := Q2.sub (Q2.add (Q2.smul selD α) β) (Q2.C (γ * selA))

/-- principal: `α = 1 - β Λ₀ + (Λ₀ - 2) s₀`, `β = Λ₀ - h - 2`, `γ = 9/2`. -/
def prinα : Q2 := Q2.add (Q2.sub (Q2.C 1) BQ) (Q2.mul (Q2.sub LQ (Q2.C 2)) chordQ)
def prinβ : Q2 := Q2.sub (Q2.sub LQ Q2.Y) (Q2.C 2)
/-- second reference: `α = 1/20 + (3/2)(1 - β Λ₀) + ((3/2)Λ₀ - 5/2) s₀`, `β = (3/2)(Λ₀ - h) - 5/2`, `γ = 9/2`. -/
def srefα : Q2 := Q2.add (Q2.add (Q2.C (1/20)) (Q2.smul (3/2) (Q2.sub (Q2.C 1) BQ)))
  (Q2.mul (Q2.sub (Q2.smul (3/2) LQ) (Q2.C (5/2))) chordQ)
def srefβ : Q2 := Q2.sub (Q2.smul (3/2) (Q2.sub LQ Q2.Y)) (Q2.C (5/2))
/-- second diagonal: `α = 1 - β Λ₀ + (Λ₀ - 1) s₀`, `β = Λ₀ - h - 1`, `γ = 4`. -/
def sdiaα : Q2 := Q2.add (Q2.sub (Q2.C 1) BQ) (Q2.mul (Q2.sub LQ (Q2.C 1)) chordQ)
def sdiaβ : Q2 := Q2.sub (Q2.sub LQ Q2.Y) (Q2.C 1)

theorem slopePosQ_pos : posBox slopePosQ 10 (-1) 1 0 hmax = true := by decide +kernel
theorem slopeLtQ_pos : posBox slopeLtQ 10 (-1) 1 0 hmax = true := by decide +kernel
theorem sixQ_pos : posBox sixQ 10 (-1) 1 0 hmax = true := by decide +kernel
theorem upQ_pos : posBox upQ 12 (-1) 1 0 hmax = true := by decide +kernel
theorem prinA_pos : posBox (shapeAQ prinα) 12 (-1) 1 0 hmax = true := by decide +kernel
theorem prinT_pos : posBox (shapeTQ prinα prinβ (9/2)) 12 (-1) 1 0 hmax = true := by decide +kernel
theorem prinS_pos : posBox (shapeSQ prinα prinβ (9/2)) 12 (-1) 1 0 hmax = true := by decide +kernel
theorem srefA_pos : posBox (shapeAQ srefα) 12 (-1) 1 0 hmax = true := by decide +kernel
theorem srefT_pos : posBox (shapeTQ srefα srefβ (9/2)) 12 (-1) 1 0 hmax = true := by decide +kernel
theorem srefS_pos : posBox (shapeSQ srefα srefβ (9/2)) 12 (-1) 1 0 hmax = true := by decide +kernel
theorem sdiaA_pos : posBox (shapeAQ sdiaα) 12 (-1) 1 0 hmax = true := by decide +kernel
theorem sdiaT_pos : posBox (shapeTQ sdiaα sdiaβ 4) 12 (-1) 1 0 hmax = true := by decide +kernel
theorem sdiaS_pos : posBox (shapeSQ sdiaα sdiaβ 4) 12 (-1) 1 0 hmax = true := by decide +kernel


/-! ### Reading the facts on the reals -/

/-- The parent `Λ₀`, its budget `β Λ₀` and the chord slope `s₀` at `(t, h)`. -/
noncomputable def Lr (t : ℝ) : ℝ := (Lm : ℝ) + Lh * t
noncomputable def Br (t : ℝ) : ℝ := beta (Lr t)
noncomputable def Sr (t h : ℝ) : ℝ := Q2.ev chordQ t h

theorem posBox_ev {P : Q2} {k : ℕ} (hP : posBox P k (-1) 1 0 hmax = true) {t h : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (hh0 : 0 ≤ h) (hh : h ≤ hmax) : 0 < Q2.ev P t h :=
  posBox_sound P k _ _ _ _ hP (by push_cast; exact ht.1) (by push_cast; exact ht.2)
    (by push_cast; exact hh0) hh

theorem ev_LQ' (t h : ℝ) : Q2.ev LQ t h = Lr t := ev_LQ t h
theorem ev_BQ' (t h : ℝ) : Q2.ev BQ t h = Br t := ev_BQ t h

/-- The child is the curve point `Λ₀ - h`, and the crossing slope of the step is the chord slope. -/
theorem child_eq (t h : ℝ) : Br t - Sr t h * h = beta (Lr t - h) := by
  have := ev_chordQ t h
  simp only [Br, Sr, Lr] at this ⊢
  linarith

theorem cross_curve (t h : ℝ) (hh : h ≠ 0) :
    cross (Br t) (Lr t) (Br t - Sr t h * h) (Lr t - h) = Sr t h := by
  unfold cross
  have : Lr t - (Lr t - h) = h := by ring
  rw [this, show Br t - (Br t - Sr t h * h) = Sr t h * h by ring, mul_div_assoc, div_self hh, mul_one]

theorem shapePos_of_three {A D α β γ T : ℝ} (hα : 0 < α) (hT : 0 < (α + β * T) * (1 + D * T) - γ * A * T)
    (hS : 0 < α * D + β - γ * A) : ShapePos A D α β γ T :=
  ⟨hα, hT, Or.inr (Or.inl hS.le)⟩

theorem ev_chordQ' (t h : ℝ) : Q2.ev chordQ t h = Sr t h := rfl

theorem Lr_mem {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : (La : ℝ) ≤ Lr t ∧ Lr t ≤ Lb := by
  have h1 := ht.1; have h2 := ht.2
  simp only [Lr, La, Lb, Lm, Lh]; push_cast
  constructor <;> nlinarith

/-- The marked HIGH gate of the step along the curve (the field `high_marked`). -/
def HighCurve (t h : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ v, 0 ≤ v → v ≤ 1/10 - cross (Br t) (Lr t) (Br t - Sr t h * h) (Lr t - h) →
    ∀ ν, dens (Br t) (Lr t) (Lr t - h) (19/50) 100 v ≤ ν → ν ≤ 3 / 4 →
      r ≤ highJ (Br t - Sr t h * h) (Lr t - h) (width (Br t) (Lr t) (Br t - Sr t h * h) (Lr t - h) v)
          (sel (19/50) 100 v) ν +
        QRH.RepeatedMarks.Source.gainC ν (Br t) (Lr t) (1/10)
          (width (Br t) (Lr t) (Br t - Sr t h * h) (Lr t - h) v - sel (19/50) 100 v) (packed (19/50) 100 v)

set_option maxHeartbeats 1000000 in
/-- **Every field of the marked step's gates except the HIGH gate**, for every parent on the curve and every
step `0 < h ≤ hmax`. -/
theorem hybridGatesM_curve {t h : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (hh : 0 < h) (hh' : h ≤ hmax)
    (hhigh : HighCurve t h) :
    HybridGatesM (1/2) (Br t) (Lr t) (1/10) (Br t - Sr t h * h) (Lr t - h) (1/10) (19/50) 100 := by
  have hev : ∀ {P : Q2} {k : ℕ}, posBox P k (-1) 1 0 hmax = true → 0 < Q2.ev P t h :=
    fun hP => posBox_ev hP ht hh.le hh'
  have f1 := hev slopePosQ_pos
  have f2 := hev slopeLtQ_pos
  have f3 := hev sixQ_pos
  have f4 := hev upQ_pos
  have f5 := hev floorQ_pos
  have pA := hev prinA_pos
  have pT := hev prinT_pos
  have pS := hev prinS_pos
  have rA := hev srefA_pos
  have rT := hev srefT_pos
  have rS := hev srefS_pos
  have dA := hev sdiaA_pos
  have dT := hev sdiaT_pos
  have dS := hev sdiaS_pos
  simp only [slopePosQ, slopeLtQ, sixQ, upQ, floorQ, shapeAQ, shapeTQ, shapeSQ, prinα, prinβ, srefα, srefβ,
    sdiaα, sdiaβ, Q2.ev_add, Q2.ev_sub, Q2.ev_mul, Q2.ev_smul, Q2.ev_C, Q2.ev_X, Q2.ev_Y, ev_LQ', ev_BQ',
    ev_chordQ'] at f1 f2 f3 f4 f5 pA pT pS rA rT rS dA dT dS
  norm_num [selA, selD] at f1 f2 f3 f4 f5 pA pT pS rA rT rS dA dT dS
  have hL := Lr_mem ht
  norm_num [La, Lb] at hL
  have hcr := cross_curve t h hh.ne'
  set s := Sr t h with hs
  set L0 := Lr t
  set B0 := Br t
  have hv : (0:ℝ) < 1/10 - s := by linarith
  have hu : (0:ℝ) < sel (19/50) 100 (1/10 - s) := by unfold sel; positivity
  have hu' : sel (19/50) 100 (1/10 - s) ≤ 19/5000 := by
    unfold sel; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hh' : L0 - (L0 - h) = h := by ring
  have hden : 0 < h * (1 + 100 * (1/10 - s)) + (6 * B0 - L0) * (19/50) := by
    have : 0 < h * (1 + 100 * (1/10 - s)) := mul_pos hh (by linarith)
    linarith
  refine hybridGatesM_of_scalar (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
    (by rw [hcr]; linarith) ?_ ?_ ?_ ?_ (by rw [hcr]; linarith) ?_ (by rw [hcr]; linarith) (by norm_num) ?_
    ?_ ?_ ?_ hhigh
  · rw [hcr]; unfold dens; rw [hh', lt_div_iff₀ hden]; linarith
  · rw [hcr]; unfold dens; rw [hh', lt_div_iff₀ hden]; linarith
  · unfold dens
    rw [hh', mul_zero, add_zero, mul_one, div_lt_iff₀ (by linarith)]; linarith
  · rw [hcr]; linarith
  · rw [hcr]; unfold gRetainedCap width packed; rw [hcr]; linarith
  · rw [hcr]; unfold gRefUpper width; rw [hcr]; linarith
  · rw [hcr]
    have e : 1 - (B0 - s * h) + (L0 - h - 2) * s = 1 - B0 + (L0 - 2) * s := by ring
    rw [e]; exact shapePos_of_three pA (by linarith) (by linarith)
  · rw [hcr]
    have e : 1/20 + 3/2 * (1 - (B0 - s * h)) + (3/2 * (L0 - h) - 5/2) * s =
        1/20 + 3/2 * (1 - B0) + (3/2 * L0 - 5/2) * s := by ring
    rw [e]; exact shapePos_of_three rA (by linarith) (by linarith)
  · rw [hcr]
    have e : 1 - (B0 - s * h) + (L0 - h - 1) * s = 1 - B0 + (L0 - 1) * s := by ring
    rw [e]; exact shapePos_of_three dA (by linarith) (by linarith)

end QRH.ArviOdeShape

#print axioms QRH.ArviOdeShape.hybridGatesM_curve
