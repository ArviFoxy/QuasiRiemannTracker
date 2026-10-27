/- Copyright (c) 2026 Sil. Apache-2.0.
HIGH pointwise bound of the density-split leaf (DS §3, final source audit §5).

For a kept row of nonzero weight of a natural state whose whole ray-twisted family has
zero maximum `< b + 2e` at the supplier height `3(i+1)Z^τ` (the upper guard of its
buffered bin), PR69 `actual_high_retained_row` bounds the retained positive row with the
two ordinary factors and all marked slots by `Z^{(2b-1)(P₁+P₂+∑w)+small}`. The packed row
is the literal `positiveSlotRow` of the natural state with ordinary profiles
`Profiles (1/4) (9/4)`; it is reduced to the supplier's `retainedPositiveRow` by
* `retained_rectangle_raw_energy` (clipping factor `≤ (9/4)²`, both ordinary scales are
  `≥ 4/9` on a nonzero row, `positive_row_surviving_scales`),
* the separate homogeneous normalisation of the two ordinary profiles
  (`fixed_clipped_normalization`, `retained_plain_normalized_norm_sq`): the Mellin budget
  `profileBound` is fixed before the supplier, the normalised clipped profiles have support
  in `[1/9, 9/4]`, Mellin bounds on `[-1,2] ⊇ [1-b-6e,2]`, and the discarded product is at
  most `C·p.control T`. -/
import Submissions.density_split_third_20261026.Density.LeafRows
import Submissions.hailey_collet_1252270103.Cycle61.Moment.HighRetainedRows
import Submissions.hailey_collet_1252270103.Cycle61.Physical.HighProfiles.Control
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularPositiveRawProfile
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.ExcludedCharacterBound
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryZeroPartition

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.DensitySplitThird.Density
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentEnergyCapacityRemoval ConcreteTraceCRT
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedProfile
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open LocalMoment Cycle61HighProfiles HeckeDetectorZeros
local notation "O" => HeckeFamily.O

/-- The clipped scale is `Z` to the ordinary length. -/
theorem clippedScale_eq_rpow {Z X d : ℝ} (hZ : 1 < Z) (hd : 0 < d) :
    clippedScale X = (Z^d)^(length Z X/d) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  rw [← Real.rpow_mul hZ0.le, mul_div_cancel₀ _ hd.ne']
  unfold length clippedScale
  rw [Real.rpow_logb hZ0 hZ.ne' (zero_lt_one.trans_le (le_max_left _ _))]

section
variable (rayM : Ideal O) [NeZero rayM]
local instance leafHighRowQuotientFinite : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- **HIGH pointwise row bound.** Constants first (after the slot type, the height scale
`τ` and the small parameters), then the anchor `η₀`, then the threshold in `Z`, and only
then the density parameter `b ∈ [51/100,1]` of the upper guard, the state, the row, the
slot data, the ordinary profiles and lengths. -/
theorem high_row_bound {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (bΦ Mcap Lplain τ ε₁ e kap v d : ℝ) (hbΦ : 0 ≤ bΦ) (hL : 0 ≤ Lplain) (hτ : 0 < τ)
    (hε₁ : 0 < ε₁) (he : 0 < e) (he' : e < 1/1000) (hkap : 0 < kap) (hkap' : kap ≤ 1)
    (hv : 0 ≤ v) (hd : 0 < d) (hdsupply : Mcap+0+1 ≤ d)
    (hslotBudget : 8*e*(1/d)+kap ≤ ε₁)
    (hplainBudget : 12*e*(Lplain/d+2)+8*kap+2*v ≤ ε₁) :
    ∃ K : ℝ, 0 < K ∧ ∃ S : Finset (ℕ×ℕ), ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ st : NaturalState Z 0 bΦ, st.puncture = 1 → st.width ≤ Mcap →
    ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
      (b : ℝ) (i : ℕ), 51/100 ≤ b → b ≤ 1 →
    ∀ z : O, ∀ hz : st.radial.keep z,
      st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 →
      Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz
        (3*(i+1 : ℕ)*Z^τ) < b + 2*e →
    ∀ (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v' : T → ℝ) (t : ℝ),
      (∀ k, 0 ≤ w k) → (∀ k, w k ≤ 1) →
      (∀ k, (33/50:ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
      (∀ k, |t+v' k|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) → |t|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^v →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
      length Z X₁ ≤ Lplain → length Z X₂ ≤ Lplain →
      ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
        (fun k => primePool rayM H 2 (Z^(w k)))
        (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
        (fun k => Z^(w k)) t X₁ X₂‖^2 ≤
      K * (p.control S)^2 *
        Z^((2*b-1)*(length Z X₁ + length Z X₂ + ∑ k, w k) +
          2*ε₁*d*(Fintype.card α + 1)) := by
  have ha : (0:ℝ) < 1/4 := by norm_num
  obtain ⟨bound, hbound, hnorm⟩ := fixed_clipped_normalization (1/4) (9/4) ha
  obtain ⟨n, Cp, Cs, hCp, hCs, hrow⟩ := actual_high_retained_row rayM H hH W 1 2 one_pos
    hWs hW (1/d) (Lplain/d) d τ ε₁ ε₁ e kap v v (33/50) (33/50) bΦ Mcap 0 1 d
    (by positivity) (div_nonneg hL hd.le) hd.le hτ hε₁ hε₁ he he' hkap hkap' hv hv
    hslotBudget hplainBudget hbΦ one_pos hd hdsupply le_rfl bound (fun k => (hbound k).le)
  obtain ⟨S, Tc, Cc, hS, hCc, hclip⟩ := hnorm n
  let N : ℕ := Fintype.card α
  refine ⟨(9/4)^2*Cc^2*(Cp^2*(max 1 Cs)^N), by positivity, Tc, ?_⟩
  intro η₀
  filter_upwards [hrow η₀, eventual_state_conductor bΦ Mcap hbΦ] with Z hZ hZc
  refine ⟨hZ.1, ?_⟩
  intro st hu hwidth hQM hQη b i hb hb1 z hz hp hupper T θ w σ v' t hw hw1 hσ hσ' hwin
    hwinP hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  have hZ1 : 1 < Z := hZ.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  set pool : T → Finset (Ideal O) := fun k => primePool rayM H 2 (Z^(w k))
  set β : T → Ideal O → ℂ := fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
    HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I
  set P : T → ℝ := fun k => Z^(w k)
  have hP : ∀ k, 0 < P k := fun k => Real.rpow_pos_of_pos hZ0 _
  let X : Fin 2 → ℝ := ![X₁, X₂]
  have hX : ∀ k, 0 < X k := by
    intro k; fin_cases k
    · exact hX₁
    · exact hX₂
  by_cases hne : positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
      pool β P t X₁ X₂ = 0
  · rw [hne, norm_zero]
    have hK : 0 ≤ (9/4:ℝ)^2*Cc^2*(Cp^2*(max 1 Cs)^N) := by positivity
    have hz := Real.rpow_nonneg hZ0.le ((2*b-1)*(length Z X₁ + length Z X₂ + ∑ k, w k) +
      2*ε₁*d*(Fintype.card α + 1))
    calc (0:ℝ)^2 = 0 := by norm_num
      _ ≤ _ := mul_nonneg (mul_nonneg hK (sq_nonneg _)) hz
  have hret : ∀ k, 1 ≤ X k * (9/4) :=
    OAI.SevenEighths.Record1252270103Source.positive_row_surviving_scales p st.character
      st.mask z pool β P t X hX hne
  obtain ⟨hcc, -, hsupp, hsmooth, hmellin⟩ := hclip p X hX hret
  -- the retained-row supplier
  let F := naturalRow st.character z (st.row_ne_zero z hz)
  have hcond := hZc.2 0 st hwidth z (st.row_ne_zero z hz) hp
  have hmod : (((excluded F.character st.puncture).modulus.absNorm : ℕ) : ℝ) ≤ Z^d := by
    have hR : (st.puncture.absNorm : ℝ) ≤ Z^(0:ℝ) := by rw [hu]; simp
    have := QRH.Record1252270103Low.excluded_character_power_bound Z (Mcap+1) 0 hZ0
      F.character st.puncture st.puncture_ne_zero hcond hR
    refine this.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  have hAL : LowBranch.ActualLow rayM H hH st η₀ hQM hQη b e (3*(i+1 : ℕ)*Z^τ) z :=
    whole_source_upper_actual_low rayM H hH st η₀ hQM hQη z hz b e _ hp hupper
  have hgate2 : (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^v := by
    have h1 : (1:ℝ) ≤ 3+(3*i+2 : ℕ)*Z^τ := by
      have := Real.rpow_nonneg hZ0.le τ
      have : (0:ℝ) ≤ ((3*i+2 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact le_trans (pow_le_pow_right₀ h1 (by norm_num)) hgate
  let Wn : Fin 2 → ℝ → ℂ := fun k => ((normalizedPlains ha S p X hX).profile k : ℝ → ℂ)
  let r : Fin 2 → ℝ := fun k => length Z (X k)/d
  have hr0 : ∀ k, 0 ≤ r k := fun k => div_nonneg (length_nonneg Z _ hZ1) hd.le
  have hrR : ∀ k, r k ≤ Lplain/d := by
    intro k
    apply div_le_div_of_nonneg_right _ hd.le
    fin_cases k
    · exact hl₁
    · exact hl₂
  have hbd := hZ.2 st hwidth hQM hQη b i hb hb1 z hz F hAL
    (Cycle61InitialMass.geometryRowFamily rayM H hH st η₀ z hz)
    (Cycle61InitialMass.geometry_row_family_nonprincipal rayM H hH st η₀ hQM hQη z hz)
    (Sum.inl ()) rfl hupper hmod w σ v' θ t hw
    (fun k => by rw [div_le_div_iff_of_pos_right hd]; exact hw1 k) hσ hσ' hwin hgate2
    hwinP hgate Wn X r (fun _ => 1/9) (fun _ => 9/4) hX
    (fun k => clippedScale_eq_rpow hZ1 hd) (fun _ => by norm_num)
    (fun k => by
      have := hsupp k
      norm_num at this ⊢
      exact this)
    hsmooth hr0 hrR
    (fun k x hx u => hmellin k 2 (Or.inl rfl) x (high_strip_mem hb1 he'.le hx) u)
    (fun k x hx u => hmellin k (n+2) (Or.inr rfl) x (high_strip_mem hb1 he'.le hx) u)
  -- reduce the packed row to the normalised retained row
  have hraw := retained_rectangle_raw_energy st.character st.mask 1 z (p.profile 0)
    (p.profile 1) pool β P hP t X₁ X₂ (X₁*X₂) hX₁ hX₂ (mul_pos hX₁ hX₂)
  have hnormsq : ‖retainedPositiveRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
      pool β P t X₁ X₂‖^2 =
      (clippedControl ha S p X hX 0 * clippedControl ha S p X hX 1)^2 *
      ‖retainedPositiveRow st.character st.mask 1 z (Wn 0) (Wn 1) pool β P t X₁ X₂‖^2 :=
    OAI.SevenEighths.Record1252270103Source.retained_plain_normalized_norm_sq ha S hS p
      st.character st.mask z pool β P t X hX hret
  have hclip1 : clipDilation X₁ ≤ 9/4 := by
    have := clipDilation_le (9/4) X₁ hX₁ (hret 0)
    rwa [max_eq_right (by norm_num : (1:ℝ) ≤ 9/4)] at this
  have hclip2 : clipDilation X₂ ≤ 9/4 := by
    have := clipDilation_le (9/4) X₂ hX₂ (hret 1)
    rwa [max_eq_right (by norm_num : (1:ℝ) ≤ 9/4)] at this
  have hfac : clippedScale X₁ * clippedScale X₂ / (X₁*X₂) ≤ (9/4)^2 := by
    rw [← div_mul_div_comm]
    change clipDilation X₁ * clipDilation X₂ ≤ _
    have h1 := clipDilation_ge_one X₁ hX₁
    nlinarith [clipDilation_ge_one X₂ hX₂]
  have hfac0 : 0 ≤ clippedScale X₁ * clippedScale X₂ / (X₁*X₂) := by
    have := clippedScale_ge_one X₁
    have := clippedScale_ge_one X₂
    positivity
  have hc0 := clippedControl_nonneg ha S p X hX 0
  have hc1 := clippedControl_nonneg ha S p X hX 1
  have hpc := p.control_nonneg Tc
  have hcc2 : (clippedControl ha S p X hX 0 * clippedControl ha S p X hX 1)^2 ≤
      Cc^2 * (p.control Tc)^2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hc0 hc1) hcc 2
  -- the supplier exponent
  have hexp : (2*b-1)*(d*(r 0+r 1)+(∑ k, w k)) + 2*ε₁*d + 2*ε₁*d*(Fintype.card T) ≤
      (2*b-1)*(length Z X₁ + length Z X₂ + ∑ k, w k) + 2*ε₁*d*(Fintype.card α + 1) := by
    have e1 : d*(r 0+r 1) = length Z X₁ + length Z X₂ := by
      change d*(length Z X₁/d + length Z X₂/d) = _
      field_simp
    rw [e1]
    have hc : (Fintype.card T : ℝ) ≤ Fintype.card α := by
      exact_mod_cast Fintype.card_le_of_injective _ Subtype.val_injective
    have : 0 ≤ 2*ε₁*d := by positivity
    nlinarith
  have hCsN : Cs^(Fintype.card T) ≤ (max 1 Cs)^N := by
    calc Cs^(Fintype.card T) ≤ (max 1 Cs)^(Fintype.card T) :=
          pow_le_pow_left₀ hCs.le (le_max_right _ _) _
      _ ≤ (max 1 Cs)^N := pow_le_pow_right₀ (le_max_left _ _)
          (Fintype.card_le_of_injective _ Subtype.val_injective)
  have hbd' : ‖retainedPositiveRow st.character st.mask 1 z (Wn 0) (Wn 1) pool β P t X₁ X₂‖^2
      ≤ Cp^2*(max 1 Cs)^N*Z^((2*b-1)*(length Z X₁ + length Z X₂ + ∑ k, w k) +
          2*ε₁*d*(Fintype.card α + 1)) := by
    refine (hbd : _).trans ?_
    have hz1 := Real.rpow_le_rpow_of_exponent_le hZ1.le hexp
    have hz0 := Real.rpow_nonneg hZ0.le ((2*b-1)*(d*(r 0+r 1)+(∑ k, w k)) + 2*ε₁*d +
      2*ε₁*d*(Fintype.card T))
    calc Cp^2*Cs^(Fintype.card T)*Z^((2*b-1)*(d*(r 0+r 1)+(∑ k, w k)) + 2*ε₁*d +
          2*ε₁*d*(Fintype.card T))
        ≤ Cp^2*(max 1 Cs)^N*Z^((2*b-1)*(d*(r 0+r 1)+(∑ k, w k)) + 2*ε₁*d +
          2*ε₁*d*(Fintype.card T)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCsN (sq_nonneg _)) hz0
      _ ≤ _ := mul_le_mul_of_nonneg_left hz1 (by positivity)
  have hrow0 : ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
      pool β P t X₁ X₂‖^2 = clippedScale X₁ * clippedScale X₂ / (X₁*X₂) *
      ‖retainedPositiveRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
        pool β P t X₁ X₂‖^2 := by
    unfold positiveSlotRow
    exact hraw
  rw [hrow0, hnormsq]
  have hR0 := sq_nonneg ‖retainedPositiveRow st.character st.mask 1 z (Wn 0) (Wn 1)
    pool β P t X₁ X₂‖
  calc clippedScale X₁ * clippedScale X₂ / (X₁*X₂) *
        ((clippedControl ha S p X hX 0 * clippedControl ha S p X hX 1)^2 *
        ‖retainedPositiveRow st.character st.mask 1 z (Wn 0) (Wn 1) pool β P t X₁ X₂‖^2)
      ≤ (9/4)^2 * ((Cc^2 * (p.control Tc)^2) *
        (Cp^2*(max 1 Cs)^N*Z^((2*b-1)*(length Z X₁ + length Z X₂ + ∑ k, w k) +
          2*ε₁*d*(Fintype.card α + 1)))) := by
        apply mul_le_mul hfac _ (by positivity) (by norm_num)
        exact mul_le_mul hcc2 hbd' hR0 (by positivity)
    _ = _ := by ring

end
end
end QRH.DensitySplitThird.Density
