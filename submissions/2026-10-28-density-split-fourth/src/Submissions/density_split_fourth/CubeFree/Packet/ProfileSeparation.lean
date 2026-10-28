/- Copyright (c) 2026 Sil. Apache-2.0.
Common-profile separation of ordinary-prefix dilations (common-profile lemma, Section 2).

For a source profile `W` supported in `[1/4, 9/4]` and a prefix dilation parameter
`v ∈ [0, log 2]`, Fourier inversion of `f = W ∘ exp` gives

  `W (exp v * x) = ∫ 𝓕f(τ) e^{2πiτv} x^{2πiτ} dτ`

(the `(2π)⁻¹ ∫ f̂(t) e^{itv} x^{it} dt` of the paper after `t = 2πτ`). A fixed smooth
partition of unity on `[1/8, 9/4]` (two pieces, scales `c₀ = 1/4`, `c₁ = 3/2`) then writes
the dilated profile through the label-independent common profiles

  `W_{e,τ}(u) = ψ_e(c_e u) u^{2πiτ} ∈ Profiles (1/4) (9/4)`

at the ordinary scale `c_e · Y`, with the phase `c_e^{2πiτ}` and the central-normalization
factor `√c_e` kept in the scalar coefficient. The common profiles have polynomially bounded
source seminorms, and the majorant `√(c c') |𝓕f₁(τ₁)| |𝓕f₂(τ₂)|` is integrable against every
polynomial weight. The output `prefix_hrep` is the `hrep` hypothesis of
`QRH.DensitySplitThird.CommonProfile.weighted_separation`, for the literal OAI positive slot row;
`prefix_weighted_separation` is the assembled inequality, and `pairMajorant_mass_control`
bounds the masses `L₀`, `L_J` by finitely many seminorms of the original profiles. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RetainedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Descent.DescentProfiles
import Submissions.density_split_fourth.Analysis.CommonProfile
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.Packet
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open MeasureTheory
open OAI OAI.SevenEighths
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice FourierBridge

namespace ProfileSeparation

/-! ### 1. The log pullback and Fourier inversion of a dilation -/

theorem logPull_compact (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) :
    HasCompactSupport (fun y : ℝ => W (Real.exp y)) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := Real.log (1/4)) (b := Real.log (9/4)))
  intro y hy
  by_contra h
  have hm := hs h
  apply hy
  constructor
  · rw [Real.log_le_iff_le_exp (by norm_num)]; exact hm.1
  · rw [Real.le_log_iff_exp_le (by norm_num)]; exact hm.2

/-- `f = W ∘ exp` as a Schwartz function. -/
def logProfile (W : 𝓢(ℝ, ℂ)) (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) :
    𝓢(ℝ, ℂ) :=
  (logPull_compact W hs).toSchwartzMap ((W.smooth ⊤).comp Real.contDiff_exp)

theorem logProfile_apply (W : 𝓢(ℝ, ℂ)) (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (y : ℝ) : logProfile W hs y = W (Real.exp y) := rfl

/-- The spectral density `𝓕 (W ∘ exp)`. -/
def density (W : 𝓢(ℝ, ℂ)) (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) :
    𝓢(ℝ, ℂ) :=
  𝓕 (logProfile W hs)

/-- Fourier inversion of a dilation: `W(e^v x) = ∫ 𝓕f(τ) e^{2πiτv} e^{2πiτ log x} dτ`. -/
theorem dilation_inversion (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) (v x : ℝ) (hx : 0 < x) :
    W (Real.exp v * x) =
      ∫ τ : ℝ, density W hs τ * (logPhase τ v * logPhase τ (Real.log x)) := by
  have h := InverseMoment.schwartz_logPhase_inversion (logProfile W hs) (v + Real.log x)
  rw [logProfile_apply, Real.exp_add, Real.exp_log hx] at h
  rw [h]
  congr 1
  funext τ
  rw [logPhase_add]
  simp only [density]
  ring

/-- Weighted integrability of the spectral density (rapid decay). -/
theorem density_weighted_integrable (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) (J : ℕ) :
    Integrable (fun τ : ℝ => (1 + ‖τ‖) ^ J * ‖density W hs τ‖) :=
  AnalyticBridge.schwartz_fourier_one_plus_integrable (logProfile W hs) J

theorem density_norm_integrable (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) :
    Integrable (fun τ : ℝ => ‖density W hs τ‖) :=
  (density W hs).integrable.norm

/-! ### 2. A fixed smooth partition of unity on the annulus `[1/8, 9/4]` -/

/-- Equal to one on `[1/8, 1/2]`, supported in `(1/16, 9/16) = (1/4)·(1/4, 9/4)`. -/
def bump₀ : ContDiffBump (5/16 : ℝ) := ⟨3/16, 1/4, by norm_num, by norm_num⟩
/-- Equal to one on `[1/2, 9/4]`, supported in `(3/8, 19/8) ⊆ (3/2)·(1/4, 9/4)`. -/
def bump₁ : ContDiffBump (11/8 : ℝ) := ⟨7/8, 1, by norm_num, by norm_num⟩

/-- The two annular pieces `ψ_e` in the annulus variable `x`. -/
def annular : Fin 2 → ℝ → ℝ := ![(bump₀ : ℝ → ℝ), fun x => bump₁ x * (1 - bump₀ x)]

/-- The constant rescalings `c_e`. -/
def scale : Fin 2 → ℝ := ![1/4, 3/2]

theorem scale_pos (e : Fin 2) : 0 < scale e := by
  fin_cases e <;> norm_num [scale]

theorem scale_mem (e : Fin 2) : scale e ∈ Set.Icc (1/4 : ℝ) (3/2) := by
  fin_cases e <;> norm_num [scale]

theorem annular_sum (x : ℝ) (hx : x ∈ Set.Icc (1/8 : ℝ) (9/4)) : ∑ e, annular e x = 1 := by
  rw [Fin.sum_univ_two]
  simp only [annular, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases le_total x (1/2) with h | h
  · have h0 : bump₀ x = 1 := by
      apply bump₀.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      simp only [bump₀]
      constructor <;> linarith [hx.1, hx.2]
    rw [h0]; ring
  · have h1 : bump₁ x = 1 := by
      apply bump₁.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      simp only [bump₁]
      constructor <;> linarith [hx.1, hx.2]
    rw [h1]; ring

theorem annular_contDiff (e : Fin 2) : ContDiff ℝ ∞ (annular e) := by
  fin_cases e
  · simpa [annular] using (bump₀.contDiff : ContDiff ℝ ∞ (bump₀ : ℝ → ℝ))
  · simp only [annular, Fin.mk_one, Matrix.cons_val_one]
    exact bump₁.contDiff.mul (contDiff_const.sub bump₀.contDiff)

/-- Each piece, pulled back to the common variable `u = x / c_e`, lives in `(1/4, 9/4)`. -/
theorem annular_scale_support (e : Fin 2) (u : ℝ) (hu : annular e (scale e * u) ≠ 0) :
    u ∈ Set.Icc (1/4 : ℝ) (9/4) := by
  fin_cases e
  · simp only [annular, scale, Fin.zero_eta, Matrix.cons_val_zero] at hu
    have hm : (1/4 * u) ∈ Function.support (bump₀ : ℝ → ℝ) := hu
    rw [bump₀.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at hm
    simp only [bump₀] at hm
    constructor <;> linarith [hm.1, hm.2]
  · simp only [annular, scale, Fin.mk_one, Matrix.cons_val_one] at hu
    have hm : (3/2 * u) ∈ Function.support (bump₁ : ℝ → ℝ) := left_ne_zero_of_mul hu
    rw [bump₁.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at hm
    simp only [bump₁] at hm
    constructor <;> linarith [hm.1, hm.2]

/-- The piece `u ↦ ψ_e(c_e u)` in the common variable. -/
def pieceFun (e : Fin 2) (u : ℝ) : ℂ := (annular e (scale e * u) : ℂ)

theorem pieceFun_support (e : Fin 2) :
    Function.support (pieceFun e) ⊆ Set.Icc (1/4 : ℝ) (9/4) := by
  intro u hu
  apply annular_scale_support e u
  intro h
  exact hu (by simp [pieceFun, h])

theorem pieceFun_contDiff (e : Fin 2) : ContDiff ℝ ∞ (pieceFun e) :=
  Complex.ofRealCLM.contDiff.comp ((annular_contDiff e).comp (contDiff_const.mul contDiff_id))

theorem pieceFun_compact (e : Fin 2) : HasCompactSupport (pieceFun e) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (1/4 : ℝ)) (b := 9/4))
  intro u hu
  by_contra h
  exact hu (pieceFun_support e h)

/-- The smooth piece as a Schwartz function. -/
def piece (e : Fin 2) : 𝓢(ℝ, ℂ) := (pieceFun_compact e).toSchwartzMap (pieceFun_contDiff e)

theorem piece_apply (e : Fin 2) (u : ℝ) : piece e u = (annular e (scale e * u) : ℂ) := rfl

theorem piece_support (e : Fin 2) :
    Function.support (piece e : ℝ → ℂ) ⊆ Set.Icc (1/4 : ℝ) (9/4) :=
  pieceFun_support e

theorem piece_div_scale (e : Fin 2) (x : ℝ) : piece e (x / scale e) = (annular e x : ℂ) := by
  rw [piece_apply, mul_div_cancel₀ x (scale_pos e).ne']

/-! ### 3. The common profiles `W_{e,τ}(u) = ψ_e(c_e u) u^{2πiτ}` -/

/-- The label-independent common ordinary profile. -/
def commonProfile (e : Fin 2) (τ : ℝ) : 𝓢(ℝ, ℂ) :=
  normPowerProfile (piece e) (1/4) (9/4) (by norm_num) (piece_support e) ((piece e).smooth ⊤)
    (2 * Real.pi * τ)

theorem commonProfile_apply (e : Fin 2) (τ u : ℝ) :
    commonProfile e τ u = logPhase τ (Real.log u) * piece e u := by
  rw [commonProfile, normPowerProfile_apply]
  by_cases hz : piece e u = 0
  · rw [hz, mul_zero, mul_zero]
  · have hu : 0 < u := lt_of_lt_of_le (by norm_num) (piece_support e hz).1
    have h := logPhase_eq_normPower (2 * Real.pi * τ) u hu
    rw [show 2 * Real.pi * τ / (2 * Real.pi) = τ by field_simp] at h
    rw [← h]

theorem commonProfile_support (e : Fin 2) (τ : ℝ) :
    Function.support (commonProfile e τ : ℝ → ℂ) ⊆ Set.Icc (1/4 : ℝ) (9/4) :=
  (CenteredMomentTwist.normPowerProfile_support _ _ _ _ _ _ _).trans (piece_support e)

theorem commonProfile_norm_le (e : Fin 2) (τ u : ℝ) :
    ‖commonProfile e τ u‖ = ‖piece e u‖ := by
  rw [commonProfile_apply, norm_mul, logPhase_norm, one_mul]

theorem commonProfile_continuous_left (e : Fin 2) (u : ℝ) :
    Continuous (fun τ : ℝ => commonProfile e τ u) := by
  have : (fun τ : ℝ => commonProfile e τ u) = fun τ => logPhase τ (Real.log u) * piece e u := by
    funext τ; exact commonProfile_apply e τ u
  rw [this]
  exact (logPhase_continuous_left _).mul continuous_const

/-- Polynomial control of the common profiles: every finite family of source seminorms
grows at most polynomially in the spectral variable, uniformly in the cell. -/
theorem commonProfile_control (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ e : Fin 2, ∀ τ : ℝ,
      sourceControl S (commonProfile e τ) ≤ C * (1 + |τ|) ^ n := by
  obtain ⟨n, T, C, hC, h⟩ := normPowerProfile_source_control (1/4) (9/4) (by norm_num) S
  let Ap : ℝ := 1 + ∑ e : Fin 2, T.sup (schwartzSeminormFamily ℝ ℝ ℂ) (piece e)
  have hAp : 0 < Ap := by
    have := Finset.sum_nonneg (fun (e : Fin 2) (_ : e ∈ Finset.univ) =>
      apply_nonneg (T.sup (schwartzSeminormFamily ℝ ℝ ℂ)) (piece e))
    dsimp [Ap]; linarith
  refine ⟨n, C * Ap * (1 + 2 * Real.pi) ^ n, by positivity, ?_⟩
  intro e τ
  have he : T.sup (schwartzSeminormFamily ℝ ℝ ℂ) (piece e) ≤ Ap := by
    have := Finset.single_le_sum (fun (e : Fin 2) (_ : e ∈ Finset.univ) =>
      apply_nonneg (T.sup (schwartzSeminormFamily ℝ ℝ ℂ)) (piece e)) (Finset.mem_univ e)
    dsimp [Ap]; linarith
  have hfreq : 1 + ‖2 * Real.pi * τ‖ ≤ (1 + 2 * Real.pi) * (1 + |τ|) := by
    rw [norm_mul, norm_mul, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith [Real.pi_pos, abs_nonneg τ]
  have hb := h (piece e) (piece_support e) (2 * Real.pi * τ)
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (commonProfile e τ) ≤ _
  calc S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (commonProfile e τ)
      ≤ C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) (piece e) * (1 + ‖2 * Real.pi * τ‖) ^ n := hb
    _ ≤ C * Ap * ((1 + 2 * Real.pi) * (1 + |τ|)) ^ n := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left he hC.le)
          (pow_le_pow_left₀ (by positivity) hfreq n) (by positivity) (by positivity)
    _ = C * Ap * (1 + 2 * Real.pi) ^ n * (1 + |τ|) ^ n := by rw [mul_pow]; ring

/-! ### 4. Pointwise separation of one dilated profile -/

/-- The scalar coefficient of cell `e` at spectral parameter `τ`: the density, the unimodular
prefix phase `e^{2πiτv}`, and the scale phase `c_e^{2πiτ}`. -/
def cellCoeff (W : 𝓢(ℝ, ℂ)) (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (e : Fin 2) (v τ : ℝ) : ℂ :=
  density W hs τ * logPhase τ v * logPhase τ (Real.log (scale e))

theorem cellCoeff_norm (W : 𝓢(ℝ, ℂ)) (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (e : Fin 2) (v τ : ℝ) : ‖cellCoeff W hs e v τ‖ = ‖density W hs τ‖ := by
  rw [cellCoeff, norm_mul, norm_mul, logPhase_norm, logPhase_norm, mul_one, mul_one]

theorem cellCoeff_continuous (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) (e : Fin 2) (v : ℝ) :
    Continuous (fun τ => cellCoeff W hs e v τ) := by
  unfold cellCoeff
  exact ((density W hs).continuous.mul (logPhase_continuous_left v)).mul
    (logPhase_continuous_left _)

theorem cell_integrable (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) (e : Fin 2) (v y : ℝ) (c : ℂ) :
    Integrable (fun τ : ℝ => cellCoeff W hs e v τ * (c * commonProfile e τ y)) := by
  apply ((density_norm_integrable W hs).mul_const (‖c‖ * ‖piece e y‖)).mono'
  · exact ((cellCoeff_continuous W hs e v).mul
      (continuous_const.mul (commonProfile_continuous_left e y))).aestronglyMeasurable
  · filter_upwards with τ
    rw [norm_mul, norm_mul, cellCoeff_norm, commonProfile_norm_le]

/-- One cell of the separation integral equals the piece times the dilated profile. -/
theorem cell_integral (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) (e : Fin 2) (v x : ℝ)
    (hx : 0 < x) :
    ∫ τ : ℝ, cellCoeff W hs e v τ * commonProfile e τ (x / scale e) =
      (annular e x : ℂ) * W (Real.exp v * x) := by
  have hc := scale_pos e
  have hpt : ∀ τ : ℝ, cellCoeff W hs e v τ * commonProfile e τ (x / scale e) =
      (density W hs τ * (logPhase τ v * logPhase τ (Real.log x))) * (annular e x : ℂ) := by
    intro τ
    rw [commonProfile_apply, piece_div_scale, Real.log_div hx.ne' hc.ne', cellCoeff]
    have hphase : logPhase τ (Real.log (scale e)) * logPhase τ (Real.log x - Real.log (scale e))
        = logPhase τ (Real.log x) := by
      rw [← logPhase_add]; congr 1; ring
    calc density W hs τ * logPhase τ v * logPhase τ (Real.log (scale e)) *
          (logPhase τ (Real.log x - Real.log (scale e)) * (annular e x : ℂ))
        = density W hs τ * logPhase τ v * (logPhase τ (Real.log (scale e)) *
            logPhase τ (Real.log x - Real.log (scale e))) * (annular e x : ℂ) := by ring
      _ = _ := by rw [hphase]; ring
  simp_rw [hpt]
  rw [integral_mul_const, ← dilation_inversion W hs v x hx]
  ring

/-- **Separation of a dilated profile.** For every prefix dilation `v ∈ [0, log 2]` and every
real `x`, the dilated profile is a finite sum over the two cells of spectral integrals of the
common profiles at the rescaled variable `x / c_e`. -/
theorem dilated_separation (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) (v : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ Real.log 2) (x : ℝ) :
    W (Real.exp v * x) =
      ∑ e : Fin 2, ∫ τ : ℝ, cellCoeff W hs e v τ * commonProfile e τ (x / scale e) := by
  rcases le_or_gt x 0 with hx | hx
  · -- both sides vanish off the positive axis
    have hW : W (Real.exp v * x) = 0 := by
      by_contra h
      have := (hs h).1
      have : Real.exp v * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos v).le hx
      linarith
    have hP : ∀ e : Fin 2, ∀ τ : ℝ, commonProfile e τ (x / scale e) = 0 := by
      intro e τ
      by_contra h
      have h1 := (commonProfile_support e τ h).1
      have : x / scale e ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx (scale_pos e).le
      linarith
    rw [hW]
    symm
    apply Finset.sum_eq_zero
    intro e _
    simp [hP e]
  · simp_rw [cell_integral W hs _ v x hx]
    rw [← Finset.sum_mul]
    by_cases hW : W (Real.exp v * x) = 0
    · rw [hW, mul_zero]
    · have hm := hs hW
      have hexp1 : 1 ≤ Real.exp v := Real.one_le_exp hv0
      have hexp2 : Real.exp v ≤ 2 := by
        calc Real.exp v ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hv1
          _ = 2 := Real.exp_log (by norm_num)
      have hxl : 1/8 ≤ x := by nlinarith [hm.1]
      have hxu : x ≤ 9/4 := by nlinarith [hm.2]
      rw [← Complex.ofReal_sum, annular_sum x ⟨hxl, hxu⟩, Complex.ofReal_one, one_mul]

/-! ### 5. Ideal sums and the literal OAI ordinary sum -/

section IdealSums
local notation "O" => ActualEisensteinCubic.O
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentRetainedEnergy

/-- The prefix-dilated profile `x ↦ W(e^v x)`. -/
def dilate (W : 𝓢(ℝ, ℂ)) (v : ℝ) : ℝ → ℂ := fun x => W (Real.exp v * x)

/-- The finite ideal ball carrying every ordinary sum below at scale `Y`. -/
def ball (Y : ℝ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) ⌈4 * Y⌉₊).toFinset

theorem tsum_eq_ball (F : Ideal O → ℂ) (Y : ℝ)
    (hF : ∀ I : Ideal O, F I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ 4 * Y) :
    ∑' I, F I = ∑ I ∈ ball Y, F I := by
  apply tsum_eq_sum
  intro I hI
  by_contra h
  apply hI
  rw [ball, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact_mod_cast (hF I h).trans (Nat.le_ceil _)

theorem dilate_bound (W : 𝓢(ℝ, ℂ)) (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (v : ℝ) (hv0 : 0 ≤ v) (Y : ℝ) (hY : 0 < Y) (I : Ideal O) (a : ℂ)
    (h : a * dilate W v ((Ideal.absNorm I : ℝ) / Y) ≠ 0) :
    (Ideal.absNorm I : ℝ) ≤ 4 * Y := by
  have hm := (hs (right_ne_zero_of_mul h)).2
  have hexp : 1 ≤ Real.exp v := Real.one_le_exp hv0
  have hN : 0 ≤ (Ideal.absNorm I : ℝ) / Y := div_nonneg (Nat.cast_nonneg _) hY.le
  have h1 : (Ideal.absNorm I : ℝ) / Y ≤ 9/4 := by nlinarith
  rw [div_le_iff₀ hY] at h1
  linarith

theorem common_bound (e : Fin 2) (τ : ℝ) (Y : ℝ) (hY : 0 < Y) (I : Ideal O) (a : ℂ)
    (h : a * commonProfile e τ ((Ideal.absNorm I : ℝ) / (scale e * Y)) ≠ 0) :
    (Ideal.absNorm I : ℝ) ≤ 4 * Y := by
  have hm := (commonProfile_support e τ (right_ne_zero_of_mul h)).2
  have hc := scale_mem e
  have hcY : 0 < scale e * Y := mul_pos (scale_pos e) hY
  rw [div_le_iff₀ hcY] at hm
  nlinarith [hc.2]

/-- **Separation of a prefix-dilated ordinary ideal sum.** For arbitrary coefficients
`a`, the dilated sum at the common scale `Y` is a two-cell spectral integral of the common
ordinary sums at the scales `c_e · Y`. -/
theorem ideal_sum_separation (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) (v : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ Real.log 2) (a : Ideal O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    ∑' I : Ideal O, a I * dilate W v ((Ideal.absNorm I : ℝ) / Y) =
      ∑ e : Fin 2, ∫ τ : ℝ, cellCoeff W hs e v τ *
        ∑' I : Ideal O, a I * commonProfile e τ ((Ideal.absNorm I : ℝ) / (scale e * Y)) := by
  rw [tsum_eq_ball _ Y (fun I h => dilate_bound W hs v hv0 Y hY I (a I) h)]
  have hinner : ∀ (e : Fin 2) (τ : ℝ),
      ∑' I : Ideal O, a I * commonProfile e τ ((Ideal.absNorm I : ℝ) / (scale e * Y)) =
        ∑ I ∈ ball Y, a I * commonProfile e τ (((Ideal.absNorm I : ℝ) / Y) / scale e) := by
    intro e τ
    rw [tsum_eq_ball _ Y (fun I h => common_bound e τ Y hY I (a I) h)]
    apply Finset.sum_congr rfl
    intro I _
    rw [div_div, mul_comm Y]
  simp_rw [hinner, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun e _ => integral_finsetSum (ball Y)
    (fun I _ => cell_integrable W hs e v _ (a I)))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  rw [dilate, dilated_separation W hs v hv0 hv1, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [← integral_const_mul]
  congr 1
  funext τ
  ring

/-- The same statement for the literal OAI ordinary sum `rowTwistedSum`. -/
theorem rowTwisted_separation (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) (v : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ Real.log 2) (η : Character) (m A z : O) (t Y : ℝ) (hY : 0 < Y) :
    rowTwistedSum η m A z (dilate W v) t Y =
      ∑ e : Fin 2, ∫ τ : ℝ, cellCoeff W hs e v τ *
        rowTwistedSum η m A z (commonProfile e τ) t (scale e * Y) := by
  unfold rowTwistedSum
  exact ideal_sum_separation W hs v hv0 hv1 _ Y hY

/-- The common ordinary sum is a finite sum over the fixed ball, continuous and
uniformly bounded in the spectral variable. -/
theorem rowTwisted_common_eq (η : Character) (m A z : O) (e : Fin 2) (τ t Y : ℝ)
    (hY : 0 < Y) :
    rowTwistedSum η m A z (commonProfile e τ) t (scale e * Y) =
      ∑ I ∈ ball Y, ((idealCoeff η I * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I) *
        (Ideal.absNorm I : ℂ)^(Complex.I*t)) *
          commonProfile e τ ((Ideal.absNorm I : ℝ) / (scale e * Y)) := by
  unfold rowTwistedSum
  exact tsum_eq_ball _ Y (fun I h => common_bound e τ Y hY I _ h)

theorem rowTwisted_common_continuous (η : Character) (m A z : O) (e : Fin 2) (t Y : ℝ)
    (hY : 0 < Y) :
    Continuous (fun τ : ℝ => rowTwistedSum η m A z (commonProfile e τ) t (scale e * Y)) := by
  simp_rw [rowTwisted_common_eq η m A z e _ t Y hY]
  exact continuous_finsetSum _ fun I _ =>
    continuous_const.mul (commonProfile_continuous_left e _)

/-- A τ-independent bound for the common ordinary sum. -/
def rowTwistedBound (η : Character) (m A z : O) (e : Fin 2) (t Y : ℝ) : ℝ :=
  ∑ I ∈ ball Y, ‖((idealCoeff η I * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I) *
    (Ideal.absNorm I : ℂ)^(Complex.I*t))‖ * ‖piece e ((Ideal.absNorm I : ℝ) / (scale e * Y))‖

theorem rowTwisted_common_norm_le (η : Character) (m A z : O) (e : Fin 2) (τ t Y : ℝ)
    (hY : 0 < Y) :
    ‖rowTwistedSum η m A z (commonProfile e τ) t (scale e * Y)‖ ≤
      rowTwistedBound η m A z e t Y := by
  rw [rowTwisted_common_eq η m A z e τ t Y hY, rowTwistedBound]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro I _
  rw [norm_mul, commonProfile_norm_le]

/-! ### 6. Tensor of the two ordinary factors and the `hrep` majorant -/

/-- The common profile pair of cell `e = (e₁, e₂)` at spectral parameter `τ = (τ₁, τ₂)`,
as a source profile pair. -/
def commonPair (e : Fin 2 × Fin 2) (τ : ℝ × ℝ) : Profiles (1/4) (9/4) where
  profile := ![commonProfile e.1 τ.1, commonProfile e.2 τ.2]
  support := by
    intro i
    fin_cases i
    · exact commonProfile_support e.1 τ.1
    · exact commonProfile_support e.2 τ.2

@[simp] theorem commonPair_profile_zero (e : Fin 2 × Fin 2) (τ : ℝ × ℝ) :
    (commonPair e τ).profile 0 = commonProfile e.1 τ.1 := rfl

@[simp] theorem commonPair_profile_one (e : Fin 2 × Fin 2) (τ : ℝ × ℝ) :
    (commonPair e τ).profile 1 = commonProfile e.2 τ.2 := rfl

/-- The polynomial weight on the spectral plane. -/
def pairWeight (J : ℕ) (τ : ℝ × ℝ) : ℝ := (1 + |τ.1|) ^ J * (1 + |τ.2|) ^ J

theorem pairWeight_nonneg (J : ℕ) (τ : ℝ × ℝ) : 0 ≤ pairWeight J τ := by
  unfold pairWeight; positivity

/-- Polynomial source control of the common pair: `p.control S ≤ C (1+|τ₁|)^n (1+|τ₂|)^n`. -/
theorem commonPair_control (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ e : Fin 2 × Fin 2, ∀ τ : ℝ × ℝ,
      (commonPair e τ).control S ≤ C * pairWeight n τ := by
  obtain ⟨n, C, hC, h⟩ := commonProfile_control S
  refine ⟨n, C ^ 2, by positivity, ?_⟩
  intro e τ
  simp only [Profiles.control, commonPair_profile_zero, commonPair_profile_one, pairWeight]
  calc sourceControl S (commonProfile e.1 τ.1) * sourceControl S (commonProfile e.2 τ.2)
      ≤ (C * (1 + |τ.1|) ^ n) * (C * (1 + |τ.2|) ^ n) :=
        mul_le_mul (h e.1 τ.1) (h e.2 τ.2) (sourceControl_nonneg _ _) (by positivity)
    _ = C ^ 2 * ((1 + |τ.1|) ^ n * (1 + |τ.2|) ^ n) := by ring

/-- The squared control, in the form consumed by the source bound (`ω = pairWeight (2n)`). -/
theorem commonPair_control_sq (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ e : Fin 2 × Fin 2, ∀ τ : ℝ × ℝ,
      ((commonPair e τ).control S) ^ 2 ≤ C * pairWeight (2 * n) τ := by
  obtain ⟨n, C, hC, h⟩ := commonPair_control S
  refine ⟨n, C ^ 2, by positivity, ?_⟩
  intro e τ
  have h1 := pow_le_pow_left₀ (Profiles.control_nonneg _ _) (h e τ) 2
  refine h1.trans (le_of_eq ?_)
  simp only [pairWeight]
  rw [mul_comm 2 n, pow_mul, pow_mul]
  ring

/-- The scalar coefficient of the tensored cell, with the central-normalization factor
`√(c_{e₁} c_{e₂})` retained. -/
def pairCoeff (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (e : Fin 2 × Fin 2) (v τ : ℝ × ℝ) : ℂ :=
  (Real.sqrt (scale e.1 * scale e.2) : ℂ) *
    (cellCoeff W₁ hs₁ e.1 v.1 τ.1 * cellCoeff W₂ hs₂ e.2 v.2 τ.2)

/-- The label-independent majorant `M_e(τ) = √(c_{e₁}c_{e₂}) |𝓕f₁(τ₁)| |𝓕f₂(τ₂)|`. -/
def pairMajorant (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (e : Fin 2 × Fin 2) (τ : ℝ × ℝ) : ℝ :=
  Real.sqrt (scale e.1 * scale e.2) * (‖density W₁ hs₁ τ.1‖ * ‖density W₂ hs₂ τ.2‖)

theorem pairMajorant_nonneg (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (e : Fin 2 × Fin 2) (τ : ℝ × ℝ) : 0 ≤ pairMajorant W₁ W₂ hs₁ hs₂ e τ := by
  unfold pairMajorant; positivity

theorem pairCoeff_norm (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (e : Fin 2 × Fin 2) (v τ : ℝ × ℝ) :
    ‖pairCoeff W₁ W₂ hs₁ hs₂ e v τ‖ = pairMajorant W₁ W₂ hs₁ hs₂ e τ := by
  rw [pairCoeff, pairMajorant, norm_mul, norm_mul, cellCoeff_norm, cellCoeff_norm,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem scale_sqrt_le (e : Fin 2 × Fin 2) : Real.sqrt (scale e.1 * scale e.2) ≤ 3/2 := by
  have h1 := scale_mem e.1
  have h2 := scale_mem e.2
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- `hM1`: the majorant is integrable on the spectral plane. -/
theorem pairMajorant_integrable (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (e : Fin 2 × Fin 2) :
    Integrable (pairMajorant W₁ W₂ hs₁ hs₂ e) (volume : Measure (ℝ × ℝ)) := by
  have h := (density_norm_integrable W₁ hs₁).mul_prod (density_norm_integrable W₂ hs₂)
  rw [← Measure.volume_eq_prod] at h
  exact h.const_mul _

/-- `hMω`: the majorant is integrable against every polynomial weight (rapid decay). -/
theorem pairMajorant_weighted_integrable (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (e : Fin 2 × Fin 2) (J : ℕ) :
    Integrable (fun τ => pairMajorant W₁ W₂ hs₁ hs₂ e τ * pairWeight J τ)
      (volume : Measure (ℝ × ℝ)) := by
  have h := (density_weighted_integrable W₁ hs₁ J).mul_prod
    (density_weighted_integrable W₂ hs₂ J)
  rw [← Measure.volume_eq_prod] at h
  have h' := h.const_mul (Real.sqrt (scale e.1 * scale e.2))
  refine h'.congr (Filter.Eventually.of_forall fun τ => ?_)
  simp only [pairMajorant, pairWeight, Real.norm_eq_abs]
  ring

end IdealSums

/-! ### 7. The literal positive slot row: exact pair separation and the `hrep` majorant -/

section Rows
local notation "O" => ActualEisensteinCubic.O
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
variable {ι : Type*} [Fintype ι]

/-- The label-independent common coefficient `A_{e,τ}(z)`: the literal OAI positive slot row
with the common profile pair at the rescaled ordinary scales `c_{e₁} Y₁`, `c_{e₂} Y₂`. -/
def commonRow (η : Character) (m A : O) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (t Y₁ Y₂ : ℝ) (e : Fin 2 × Fin 2) (τ : ℝ × ℝ) (z : O) : ℂ :=
  positiveSlotRow η m A z ((commonPair e τ).profile 0) ((commonPair e τ).profile 1)
    S β P t (scale e.1 * Y₁) (scale e.2 * Y₂)

theorem commonRow_mul (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (η : Character) (m A z : O) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (t Y₁ Y₂ : ℝ) (e : Fin 2 × Fin 2) (v τ : ℝ × ℝ) :
    pairCoeff W₁ W₂ hs₁ hs₂ e v τ * commonRow η m A S β P t Y₁ Y₂ e τ z =
      (Real.sqrt (Y₁ * Y₂ * ∏ i, P i) : ℂ)⁻¹ *
        ((cellCoeff W₁ hs₁ e.1 v.1 τ.1 *
            rowTwistedSum η m A z (commonProfile e.1 τ.1) t (scale e.1 * Y₁)) *
          (cellCoeff W₂ hs₂ e.2 v.2 τ.2 *
            rowTwistedSum η m A z (commonProfile e.2 τ.2) t (scale e.2 * Y₂))) *
        ∏ i, rowSlot η m A z (S i) (β i) t := by
  have hc1 := scale_pos e.1
  have hc2 := scale_pos e.2
  have hsq : Real.sqrt (scale e.1 * Y₁ * (scale e.2 * Y₂) * ∏ i, P i) =
      Real.sqrt (scale e.1 * scale e.2) * Real.sqrt (Y₁ * Y₂ * ∏ i, P i) := by
    rw [← Real.sqrt_mul (mul_pos hc1 hc2).le]
    congr 1
    ring
  have hne : (Real.sqrt (scale e.1 * scale e.2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (mul_pos hc1 hc2)).ne'
  have key : (Real.sqrt (scale e.1 * scale e.2) : ℂ) * (Real.sqrt (scale e.1 * scale e.2) : ℂ)⁻¹
      = 1 := mul_inv_cancel₀ hne
  simp only [commonRow, positiveSlotRow, pairCoeff, commonPair_profile_zero,
    commonPair_profile_one]
  rw [hsq, Complex.ofReal_mul, mul_inv]
  linear_combination
    ((Real.sqrt (Y₁ * Y₂ * ∏ i, P i) : ℂ)⁻¹ * cellCoeff W₁ hs₁ e.1 v.1 τ.1 *
      cellCoeff W₂ hs₂ e.2 v.2 τ.2 *
      rowTwistedSum η m A z (commonProfile e.1 τ.1) t (scale e.1 * Y₁) *
      rowTwistedSum η m A z (commonProfile e.2 τ.2) t (scale e.2 * Y₂) *
      ∏ i, rowSlot η m A z (S i) (β i) t) * key

/-- **Exact separation of the literal prefix-dilated positive slot row.** For prefix dilations
`v ∈ [0, log 2]²` of both ordinary profiles, normalized at the common scales `Y₁, Y₂`, the row is
a sum over the four tensored cells of spectral integrals of the common rows, with coefficient
`pairCoeff` (density, unimodular prefix and scale phases, and the retained `√(c_{e₁}c_{e₂})`). -/
theorem pair_row_separation (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (v : ℝ × ℝ) (hv₁ : v.1 ∈ Set.Icc 0 (Real.log 2)) (hv₂ : v.2 ∈ Set.Icc 0 (Real.log 2))
    (η : Character) (m A z : O) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (t Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    positiveSlotRow η m A z (dilate W₁ v.1) (dilate W₂ v.2) S β P t Y₁ Y₂ =
      ∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
        pairCoeff W₁ W₂ hs₁ hs₂ e v τ * commonRow η m A S β P t Y₁ Y₂ e τ z := by
  set N : ℂ := (Real.sqrt (Y₁ * Y₂ * ∏ i, P i) : ℂ)⁻¹ with hN
  set Q₀ : ℂ := ∏ i, rowSlot η m A z (S i) (β i) t with hQ₀
  set F₁ : Fin 2 → ℝ → ℂ := fun e₁ τ₁ => cellCoeff W₁ hs₁ e₁ v.1 τ₁ *
    rowTwistedSum η m A z (commonProfile e₁ τ₁) t (scale e₁ * Y₁) with hF₁
  set F₂ : Fin 2 → ℝ → ℂ := fun e₂ τ₂ => cellCoeff W₂ hs₂ e₂ v.2 τ₂ *
    rowTwistedSum η m A z (commonProfile e₂ τ₂) t (scale e₂ * Y₂) with hF₂
  have hcell : ∀ (e : Fin 2 × Fin 2),
      ∫ τ : ℝ × ℝ, pairCoeff W₁ W₂ hs₁ hs₂ e v τ * commonRow η m A S β P t Y₁ Y₂ e τ z =
        N * ((∫ τ₁ : ℝ, F₁ e.1 τ₁) * (∫ τ₂ : ℝ, F₂ e.2 τ₂)) * Q₀ := by
    intro e
    have hpt : ∀ τ : ℝ × ℝ,
        pairCoeff W₁ W₂ hs₁ hs₂ e v τ * commonRow η m A S β P t Y₁ Y₂ e τ z =
          N * (F₁ e.1 τ.1 * F₂ e.2 τ.2) * Q₀ := fun τ =>
      commonRow_mul W₁ W₂ hs₁ hs₂ η m A z S β P t Y₁ Y₂ e v τ
    simp_rw [hpt]
    rw [integral_mul_const, integral_const_mul]
    have hp := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (F₁ e.1) (F₂ e.2)
    rw [← Measure.volume_eq_prod] at hp
    rw [hp]
  simp only [positiveSlotRow]
  rw [rowTwisted_separation W₁ hs₁ v.1 hv₁.1 hv₁.2 η m A z t Y₁ hY₁,
    rowTwisted_separation W₂ hs₂ v.2 hv₂.1 hv₂.2 η m A z t Y₂ hY₂]
  rw [Finset.sum_congr rfl (fun e _ => hcell e), Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e₁ _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e₂ _
  simp only [hN, hQ₀, hF₁, hF₂]
  ring

/-- **The `hrep` majorant for a family of ordinary-prefix dilations.** Rows `r` carry lattice
points `z r`; each label `l` over `r` has prefix dilations `vd l ∈ [0, log 2]²` and an
arbitrary scalar `sc l r` (frozen character values, valuation/keep weights, `√Φ`, ...) with
`‖sc l r‖ ≤ K`. Then the packets satisfy the `hrep` hypothesis of
`CommonProfile.weighted_separation` with cells `Fin 2 × Fin 2`, the spectral plane `ℝ × ℝ`,
the label-independent majorant `K · pairMajorant` and the common coefficients `commonRow`. -/
theorem prefix_hrep {ρ Λ : Type*} (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (η : Character) (m A : O) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (t Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (rows : Finset ρ) (labels : ρ → Finset Λ) (z : ρ → O) (vd : Λ → ℝ × ℝ)
    (hvd : ∀ r ∈ rows, ∀ l ∈ labels r,
      (vd l).1 ∈ Set.Icc 0 (Real.log 2) ∧ (vd l).2 ∈ Set.Icc 0 (Real.log 2))
    (sc : Λ → ρ → ℂ) (K : ℝ) (hsc : ∀ r ∈ rows, ∀ l ∈ labels r, ‖sc l r‖ ≤ K)
    (B : Λ → ρ → ℂ)
    (hB : ∀ r ∈ rows, ∀ l ∈ labels r, B l r = sc l r *
      positiveSlotRow η m A (z r) (dilate W₁ (vd l).1) (dilate W₂ (vd l).2) S β P t Y₁ Y₂) :
    ∀ r ∈ rows, ∀ l ∈ labels r, ‖B l r‖ ≤
      ∑ e ∈ (Finset.univ : Finset (Fin 2 × Fin 2)), ∫ τ : ℝ × ℝ,
        (K * pairMajorant W₁ W₂ hs₁ hs₂ e τ) *
          ‖commonRow η m A S β P t Y₁ Y₂ e τ (z r)‖ := by
  intro r hr l hl
  obtain ⟨hv₁, hv₂⟩ := hvd r hr l hl
  rw [hB r hr l hl, norm_mul,
    pair_row_separation W₁ W₂ hs₁ hs₂ (vd l) hv₁ hv₂ η m A (z r) S β P t Y₁ Y₂ hY₁ hY₂]
  have hsum : ‖∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
        pairCoeff W₁ W₂ hs₁ hs₂ e (vd l) τ * commonRow η m A S β P t Y₁ Y₂ e τ (z r)‖ ≤
      ∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
        pairMajorant W₁ W₂ hs₁ hs₂ e τ * ‖commonRow η m A S β P t Y₁ Y₂ e τ (z r)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e _ => ?_)
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext τ
    rw [norm_mul, pairCoeff_norm]
  have hnn : 0 ≤ ∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
      pairMajorant W₁ W₂ hs₁ hs₂ e τ * ‖commonRow η m A S β P t Y₁ Y₂ e τ (z r)‖ :=
    Finset.sum_nonneg fun e _ => integral_nonneg fun τ =>
      mul_nonneg (pairMajorant_nonneg _ _ _ _ _ _) (norm_nonneg _)
  calc ‖sc l r‖ * _ ≤ K * ∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
        pairMajorant W₁ W₂ hs₁ hs₂ e τ * ‖commonRow η m A S β P t Y₁ Y₂ e τ (z r)‖ :=
        mul_le_mul (hsc r hr l hl) hsum (norm_nonneg _) ((norm_nonneg _).trans (hsc r hr l hl))
    _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        rw [← integral_const_mul]
        congr 1
        funext τ
        ring

/-! ### 8. Integrability of the common coefficients against the majorant (`hMA`, `hMA2`) -/

/-- A τ-independent bound for the common row. -/
def commonRowBound (η : Character) (m A : O) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (t Y₁ Y₂ : ℝ) (e : Fin 2 × Fin 2) (z : O) : ℝ :=
  ‖(Real.sqrt (scale e.1 * Y₁ * (scale e.2 * Y₂) * ∏ i, P i) : ℂ)⁻¹‖ *
    ((rowTwistedBound η m A z e.1 t Y₁ * rowTwistedBound η m A z e.2 t Y₂) *
      ‖∏ i, rowSlot η m A z (S i) (β i) t‖)

theorem commonRow_norm_le (η : Character) (m A : O) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (e : Fin 2 × Fin 2) (τ : ℝ × ℝ) (z : O) :
    ‖commonRow η m A S β P t Y₁ Y₂ e τ z‖ ≤ commonRowBound η m A S β P t Y₁ Y₂ e z := by
  simp only [commonRow, positiveSlotRow, commonPair_profile_zero, commonPair_profile_one,
    commonRowBound, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul (rowTwisted_common_norm_le η m A z e.1 τ.1 t Y₁ hY₁)
    (rowTwisted_common_norm_le η m A z e.2 τ.2 t Y₂ hY₂) (norm_nonneg _)
    ((norm_nonneg _).trans (rowTwisted_common_norm_le η m A z e.1 τ.1 t Y₁ hY₁))

theorem commonRow_continuous (η : Character) (m A : O) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (e : Fin 2 × Fin 2) (z : O) :
    Continuous (fun τ : ℝ × ℝ => commonRow η m A S β P t Y₁ Y₂ e τ z) := by
  simp only [commonRow, positiveSlotRow, commonPair_profile_zero, commonPair_profile_one]
  exact continuous_const.mul
    ((((rowTwisted_common_continuous η m A z e.1 t Y₁ hY₁).comp continuous_fst).mul
      ((rowTwisted_common_continuous η m A z e.2 t Y₂ hY₂).comp continuous_snd)).mul
        continuous_const)

/-- `hMA`. -/
theorem majorant_row_integrable (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (η : Character) (m A : O) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (t Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (K : ℝ)
    (hK : 0 ≤ K) (e : Fin 2 × Fin 2) (z : O) :
    Integrable (fun τ : ℝ × ℝ => (K * pairMajorant W₁ W₂ hs₁ hs₂ e τ) *
      ‖commonRow η m A S β P t Y₁ Y₂ e τ z‖) (volume : Measure (ℝ × ℝ)) := by
  have hM := (pairMajorant_integrable W₁ W₂ hs₁ hs₂ e).const_mul K
  refine (hM.mul_const (commonRowBound η m A S β P t Y₁ Y₂ e z)).mono' ?_ ?_
  · exact hM.aestronglyMeasurable.mul
      (commonRow_continuous η m A S β P t Y₁ Y₂ hY₁ hY₂ e z).norm.aestronglyMeasurable
  · filter_upwards with τ
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (mul_nonneg hK (pairMajorant_nonneg _ _ _ _ _ _))]
    exact mul_le_mul_of_nonneg_left (commonRow_norm_le η m A S β P t Y₁ Y₂ hY₁ hY₂ e τ z)
      (mul_nonneg hK (pairMajorant_nonneg _ _ _ _ _ _))

/-- `hMA2`. -/
theorem majorant_row_sq_integrable (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (η : Character) (m A : O) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (t Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (K : ℝ)
    (hK : 0 ≤ K) (e : Fin 2 × Fin 2) (z : O) :
    Integrable (fun τ : ℝ × ℝ => (K * pairMajorant W₁ W₂ hs₁ hs₂ e τ) *
      ‖commonRow η m A S β P t Y₁ Y₂ e τ z‖ ^ 2) (volume : Measure (ℝ × ℝ)) := by
  have hM := (pairMajorant_integrable W₁ W₂ hs₁ hs₂ e).const_mul K
  refine (hM.mul_const (commonRowBound η m A S β P t Y₁ Y₂ e z ^ 2)).mono' ?_ ?_
  · exact hM.aestronglyMeasurable.mul
      ((commonRow_continuous η m A S β P t Y₁ Y₂ hY₁ hY₂ e z).norm.pow 2).aestronglyMeasurable
  · filter_upwards with τ
    rw [norm_mul, norm_pow, norm_norm,
      Real.norm_of_nonneg (mul_nonneg hK (pairMajorant_nonneg _ _ _ _ _ _))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _)
        (commonRow_norm_le η m A S β P t Y₁ Y₂ hY₁ hY₂ e τ z) 2)
      (mul_nonneg hK (pairMajorant_nonneg _ _ _ _ _ _))

/-- `hM1` for the scaled majorant. -/
theorem prefix_hM1 (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) (K : ℝ) :
    ∀ e ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
      Integrable (fun τ : ℝ × ℝ => K * pairMajorant W₁ W₂ hs₁ hs₂ e τ)
        (volume : Measure (ℝ × ℝ)) :=
  fun e _ => (pairMajorant_integrable W₁ W₂ hs₁ hs₂ e).const_mul K

/-- `hMω` for the scaled majorant and the polynomial weight `pairWeight J`, for every `J`. -/
theorem prefix_hMω (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) (K : ℝ) (J : ℕ) :
    ∀ e ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
      Integrable (fun τ : ℝ × ℝ => (K * pairMajorant W₁ W₂ hs₁ hs₂ e τ) * pairWeight J τ)
        (volume : Measure (ℝ × ℝ)) := by
  intro e _
  refine ((pairMajorant_weighted_integrable W₁ W₂ hs₁ hs₂ e J).const_mul K).congr
    (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  ring

end Rows

/-! ### 9. Assembly with the abstract weighted separation inequality -/

section Assembly
local notation "O" => ActualEisensteinCubic.O
open HeckeFamily CenteredMomentRetainedEnergy
variable {ι : Type*} [Fintype ι]

/-- **Common-profile separation for ordinary-prefix dilations.** The weighted packet sum of the
literal prefix-dilated positive slot rows is bounded by the fibre bound `D`, the source bound
`C·pairWeight J·T` for the label-independent common rows, and the two majorant masses. -/
theorem prefix_weighted_separation {ρ Λ : Type*} (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (η : Character) (m A : O) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (t Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (rows : Finset ρ) (labels : ρ → Finset Λ) (z : ρ → O) (vd : Λ → ℝ × ℝ)
    (hvd : ∀ r ∈ rows, ∀ l ∈ labels r,
      (vd l).1 ∈ Set.Icc 0 (Real.log 2) ∧ (vd l).2 ∈ Set.Icc 0 (Real.log 2))
    (sc : Λ → ρ → ℂ) (K : ℝ) (hK : 0 ≤ K) (hsc : ∀ r ∈ rows, ∀ l ∈ labels r, ‖sc l r‖ ≤ K)
    (B : Λ → ρ → ℂ)
    (hB : ∀ r ∈ rows, ∀ l ∈ labels r, B l r = sc l r *
      positiveSlotRow η m A (z r) (dilate W₁ (vd l).1) (dilate W₂ (vd l).2) S β P t Y₁ Y₂)
    (w : Λ → ρ → ℝ) (D C T : ℝ) (J : ℕ)
    (hw : ∀ l r, 0 ≤ w l r) (hD0 : 0 ≤ D) (hD : ∀ r ∈ rows, ∑ l ∈ labels r, w l r ≤ D)
    (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hsource : ∀ (e : Fin 2 × Fin 2) (τ : ℝ × ℝ),
      ∑ r ∈ rows, ‖commonRow η m A S β P t Y₁ Y₂ e τ (z r)‖ ^ 2 ≤ C * pairWeight J τ * T) :
    ∑ r ∈ rows, ∑ l ∈ labels r, w l r * ‖B l r‖ ^ 2 ≤
      D * C * (∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ, K * pairMajorant W₁ W₂ hs₁ hs₂ e τ) *
        (∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
          K * pairMajorant W₁ W₂ hs₁ hs₂ e τ * pairWeight J τ) * T :=
  CommonProfile.weighted_separation (volume : Measure (ℝ × ℝ)) Finset.univ rows labels w B
    (fun e τ => K * pairMajorant W₁ W₂ hs₁ hs₂ e τ)
    (fun e τ r => commonRow η m A S β P t Y₁ Y₂ e τ (z r)) (pairWeight J) D C T
    hw hD0 hD (fun _ _ => mul_nonneg hK (pairMajorant_nonneg _ _ _ _ _ _))
    (pairWeight_nonneg J) hC hT
    (prefix_hM1 W₁ W₂ hs₁ hs₂ K) (prefix_hMω W₁ W₂ hs₁ hs₂ K J)
    (fun e _ r _ => majorant_row_integrable W₁ W₂ hs₁ hs₂ η m A S β P t Y₁ Y₂ hY₁ hY₂ K hK e (z r))
    (fun e _ r _ =>
      majorant_row_sq_integrable W₁ W₂ hs₁ hs₂ η m A S β P t Y₁ Y₂ hY₁ hY₂ K hK e (z r))
    (prefix_hrep W₁ W₂ hs₁ hs₂ η m A S β P t Y₁ Y₂ hY₁ hY₂ rows labels z vd hvd sc K hsc B hB)
    (fun e _ τ => hsource e τ)

end Assembly

/-! ### 10. Quantitative spectral masses: finitely many seminorms of the original profiles

The masses `L₀ = Σₑ∫Mₑ` and `L_J = Σₑ∫Mₑ·pairWeight J` are bounded by a fixed constant times
finitely many original Schwartz seminorms of `W₁` and `W₂`, uniformly in the profiles. -/

theorem logProfile_eq_clm (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) :
    logProfile W hs = CubicReflectionKernel.logPullbackCLM (1/4) (9/4) W := by
  ext u
  rw [logProfile_apply,
    CubicReflectionKernel.logPullbackCLM_eq_actual (1/4) (9/4) (by norm_num) W hs]

theorem coefficientMomentBound_linear (J : ℕ) (C : ℝ) :
    FourierBridge.coefficientMomentBound J C = C * FourierBridge.coefficientMomentBound J 1 := by
  simp only [FourierBridge.coefficientMomentBound]
  ring

/-- Weighted spectral mass of one profile, bounded by finitely many seminorms of `W`. -/
theorem density_moment_control (J : ℕ) :
    ∃ T : Finset (ℕ × ℕ), ∃ K : ℝ, 0 < K ∧ ∀ (W : 𝓢(ℝ, ℂ))
      (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)),
      ∫ τ : ℝ, (1 + ‖τ‖) ^ J * ‖density W hs τ‖ ≤
        K * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  set p := (volume : Measure ℝ).integrablePower
  let Sset : Finset (ℕ × ℕ) := (Finset.range (J + p + 1)).image (fun i => (0, i)) ∪
    (Finset.range (J + p + 1)).image (fun i => (p, i))
  obtain ⟨T, C₁, hC₁, hctl⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (CubicReflectionKernel.logPullbackCLM (1/4) (9/4)) Sset
  set B : ℝ := FourierBridge.coefficientMomentBound 0 1 + FourierBridge.coefficientMomentBound J 1
  have hB : 0 ≤ B := add_nonneg (FourierBridge.coefficientMomentBound_nonneg 0 1 zero_le_one)
    (FourierBridge.coefficientMomentBound_nonneg J 1 zero_le_one)
  refine ⟨T, 2 * C₁ * 2 ^ J * B + 1, by positivity, ?_⟩
  intro W hs
  set g := logProfile W hs
  set A := T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hA : 0 ≤ A := apply_nonneg _ _
  set C := 2 * C₁ * A
  have hC : 0 ≤ C := by positivity
  have hg : Sset.sup (schwartzSeminormFamily ℝ ℝ ℂ) g ≤ C₁ * A := by
    rw [show g = _ from logProfile_eq_clm W hs]
    exact hctl W
  have hsrc : ∀ i ≤ J + p, 1 * ((SchwartzMap.seminorm ℝ 0 i) g +
      (SchwartzMap.seminorm ℝ p i) g) ≤ C := by
    intro i hi
    have hi' : i ∈ Finset.range (J + p + 1) := Finset.mem_range.mpr (by omega)
    have h0 : (SchwartzMap.seminorm ℝ 0 i) g ≤ Sset.sup (schwartzSeminormFamily ℝ ℝ ℂ) g :=
      Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) (i := (0, i))
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi', rfl⟩))
    have hp : (SchwartzMap.seminorm ℝ p i) g ≤ Sset.sup (schwartzSeminormFamily ℝ ℝ ℂ) g :=
      Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) (i := (p, i))
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi', rfl⟩))
    have : C = 2 * (C₁ * A) := by ring
    rw [this]
    linarith
  have hm := FourierBridge.uniform_fourier_one_plus_moment g J 1 C zero_le_one hC hsrc
  rw [one_mul, coefficientMomentBound_linear 0 C, coefficientMomentBound_linear J C] at hm
  calc ∫ τ : ℝ, (1 + ‖τ‖) ^ J * ‖density W hs τ‖
      ≤ 2 ^ J * (C * FourierBridge.coefficientMomentBound 0 1 +
          C * FourierBridge.coefficientMomentBound J 1) := hm
    _ = (2 * C₁ * 2 ^ J * B) * A := by simp only [C, B]; ring
    _ ≤ (2 * C₁ * 2 ^ J * B + 1) * A := by nlinarith

section Masses
theorem pairWeight_zero (τ : ℝ × ℝ) : pairWeight 0 τ = 1 := by simp [pairWeight]

/-- The weighted mass of one tensored cell factorizes. -/
theorem pairMajorant_mass (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (e : Fin 2 × Fin 2) (J : ℕ) :
    ∫ τ : ℝ × ℝ, pairMajorant W₁ W₂ hs₁ hs₂ e τ * pairWeight J τ =
      Real.sqrt (scale e.1 * scale e.2) *
        ((∫ τ : ℝ, (1 + ‖τ‖) ^ J * ‖density W₁ hs₁ τ‖) *
          (∫ τ : ℝ, (1 + ‖τ‖) ^ J * ‖density W₂ hs₂ τ‖)) := by
  have hpt : ∀ τ : ℝ × ℝ, pairMajorant W₁ W₂ hs₁ hs₂ e τ * pairWeight J τ =
      Real.sqrt (scale e.1 * scale e.2) *
        (((1 + ‖τ.1‖) ^ J * ‖density W₁ hs₁ τ.1‖) * ((1 + ‖τ.2‖) ^ J * ‖density W₂ hs₂ τ.2‖)) := by
    intro τ
    simp only [pairMajorant, pairWeight, Real.norm_eq_abs]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  have hp := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun τ : ℝ => (1 + ‖τ‖) ^ J * ‖density W₁ hs₁ τ‖)
    (fun τ : ℝ => (1 + ‖τ‖) ^ J * ‖density W₂ hs₂ τ‖)
  rw [← Measure.volume_eq_prod] at hp
  rw [hp]

/-- **Uniform spectral masses.** `∫ Mₑ · pairWeight J ≤ K · ‖W₁‖_T · ‖W₂‖_T` for a fixed finite
seminorm set `T`; with `J = 0` this bounds `L₀`, with the source degree it bounds `L_J`. -/
theorem pairMajorant_mass_control (J : ℕ) :
    ∃ T : Finset (ℕ × ℕ), ∃ K : ℝ, 0 < K ∧ ∀ (W₁ W₂ : 𝓢(ℝ, ℂ))
      (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
      (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4)) (e : Fin 2 × Fin 2),
      ∫ τ : ℝ × ℝ, pairMajorant W₁ W₂ hs₁ hs₂ e τ * pairWeight J τ ≤
        K * (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁ * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂) := by
  obtain ⟨T, K₀, hK₀, h⟩ := density_moment_control J
  refine ⟨T, 3/2 * K₀ ^ 2, by positivity, ?_⟩
  intro W₁ W₂ hs₁ hs₂ e
  rw [pairMajorant_mass]
  have hI₁ : 0 ≤ ∫ τ : ℝ, (1 + ‖τ‖) ^ J * ‖density W₁ hs₁ τ‖ :=
    integral_nonneg fun τ => by positivity
  have hI₂ : 0 ≤ ∫ τ : ℝ, (1 + ‖τ‖) ^ J * ‖density W₂ hs₂ τ‖ :=
    integral_nonneg fun τ => by positivity
  calc Real.sqrt (scale e.1 * scale e.2) *
        ((∫ τ : ℝ, (1 + ‖τ‖) ^ J * ‖density W₁ hs₁ τ‖) *
          (∫ τ : ℝ, (1 + ‖τ‖) ^ J * ‖density W₂ hs₂ τ‖))
      ≤ 3/2 * ((K₀ * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
          (K₀ * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) :=
        mul_le_mul (scale_sqrt_le e) (mul_le_mul (h W₁ hs₁) (h W₂ hs₂) hI₂
          (le_trans hI₁ (h W₁ hs₁))) (mul_nonneg hI₁ hI₂) (by norm_num)
    _ = _ := by ring
end Masses

end ProfileSeparation
end
end QRH.DensitySplitThird.CubeFree.Packet
