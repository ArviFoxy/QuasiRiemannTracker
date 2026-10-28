/- Copyright (c) 2026 Sil. Apache-2.0.
HIGH branch of the density-split leaf (DS §3, final source audit §§2, 5, 7).

The HIGH rows at the cut `q` are the kept rows that are not LOW (`lowRow`); each has its
q-free chosen bin `selectBin` with value `b ≥ (q+1)/2`, so `ν = 2b-1 ∈ [q, 3/4]` and
`b ∈ [33/40, 7/8]` (the clip `q ≥ 13/20`). In bin `b`:
* the upper guard `max < b+2e` at height `3(p+1)T₀` gives the pointwise bound
  `|row|² ≤ K·Z^{ν(P+s)+small}` (`high_row_bound`, PR69 `actual_high_retained_row`);
* the lower guard `b ≤ max` at height `3pT₀` puts the row frequency `z ≠ 0`
  (`N(z) ≤ bΦ Z^M`) among the zero rows of the fixed natural dictionary
  `wholeSourceBase η₀ (anchors j) ·` (`whole_source_family_mask`,
  `physical_family_maximum_to_fixed_dictionary`), counted by PR69
  `fixed_natural_dictionary_raw_density`: `#rows ≤ C(1+3pT₀)^J (bΦ Z^M)^{ρ(ν)+loss}`.
The dictionary and the density degree `J` are fixed before the height scale `τ`; then
`(1+3pT₀)^J ≤ const·(1+|t|+height)^J·Z^{τJ}`. Summing over the finitely many bins,
`ρ(ν)M + ν(P+s) = M + highTerm ν P s M ≤ M + highSup q P s M`. -/
import Submissions.density_split_fourth.Density.LeafHighRow
import Submissions.density_split_fourth.Density.Price
import Submissions.hailey_collet_1252270103.Cycle61.Moment.PhysicalHighRows

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
open LocalMoment HeckeDetectorZeros ProbePhysical
local notation "O" => HeckeFamily.O

/-! ### Scalar facts -/

theorem unmarkedDensity_le_one {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 3/4) :
    unmarkedDensity ν ≤ 1 := by
  unfold unmarkedDensity
  have : 0 ≤ 10*ν/(3*(5-2*ν)) := div_nonneg (by linarith) (by nlinarith)
  linarith

/-- `ρ(ν)M + ν(P+s) = M + highTerm ν P s M ≤ M + highSup q P s M` on `ν ∈ [q, 3/4]`. -/
theorem high_exponent {q ν P s M : ℝ} (hq : 0 ≤ q) (h1 : q ≤ ν) (h2 : ν ≤ 3/4) :
    ν*(P+s) + M*unmarkedDensity ν ≤ M + highSup q P s M := by
  have hh := le_highSup hq h1 h2 P s M
  have e : M + highTerm ν P s M = ν*(P+s) + M*unmarkedDensity ν := by
    unfold highTerm unmarkedDensity
    have : (3*(5-2*ν)) = 15 - 6*ν := by ring
    rw [this]; ring
  linarith

/-- The density-count height cost. -/
theorem height_count_le {B c h : ℕ} (J : ℕ) {x y : ℝ} (hc : c ≤ B) (hx : 0 ≤ x)
    (hh : (h:ℝ) ≤ x + 1) (hy : 1 ≤ y) :
    (1 + ((3*c : ℕ):ℝ)*(((h+1:ℕ):ℝ)*y))^J ≤ (1+6*(B:ℝ))^J*(1+x)^J*y^J := by
  have hc' : ((3*c:ℕ):ℝ) ≤ 3*(B:ℝ) := by
    have : 3*c ≤ 3*B := by omega
    exact_mod_cast this
  have hh' : ((h+1:ℕ):ℝ) ≤ 2*(1+x) := by push_cast; linarith
  have h0 : (0:ℝ) ≤ ((3*c:ℕ):ℝ) := Nat.cast_nonneg _
  have h1 : (0:ℝ) ≤ ((h+1:ℕ):ℝ) := Nat.cast_nonneg _
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  have hB : (0:ℝ) ≤ B := Nat.cast_nonneg _
  have hxy : 1 ≤ (1+x)*y := one_le_mul_of_one_le_of_one_le (by linarith) hy
  have hm : ((3*c : ℕ):ℝ)*(((h+1:ℕ):ℝ)*y) ≤ (3*(B:ℝ))*((2*(1+x))*y) :=
    mul_le_mul hc' (mul_le_mul_of_nonneg_right hh' hy0) (mul_nonneg h1 hy0) (by positivity)
  have base : 1 + ((3*c : ℕ):ℝ)*(((h+1:ℕ):ℝ)*y) ≤ (1+6*(B:ℝ))*(1+x)*y := by nlinarith
  calc (1 + ((3*c : ℕ):ℝ)*(((h+1:ℕ):ℝ)*y))^J ≤ ((1+6*(B:ℝ))*(1+x)*y)^J :=
        pow_le_pow_left₀ (by positivity) base J
    _ = _ := by rw [mul_pow, mul_pow]

/-- The density-count norm cost. -/
theorem density_power_le {bΦ Z M Mcap ρ loss : ℝ} (hb : 1 ≤ bΦ) (hZ : 1 ≤ Z)
    (hMc : M ≤ Mcap) (hρ : ρ ≤ 1) (hl : 0 ≤ loss) (hl1 : loss ≤ 1) :
    (bΦ*Z^M)^(ρ+loss) ≤ bΦ^2 * Z^(M*ρ + Mcap*loss) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
  have h1 : bΦ^(ρ+loss) ≤ bΦ^2 := by
    have := Real.rpow_le_rpow_of_exponent_le hb (show ρ+loss ≤ (2:ℕ) by push_cast; linarith)
    rwa [Real.rpow_natCast] at this
  have h2 : Z^(M*(ρ+loss)) ≤ Z^(M*ρ + Mcap*loss) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hZ0.le _) (by positivity)

section
variable (rayM : Ideal O) [NeZero rayM]
local instance leafHighQuotientFinite : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The fixed natural dictionary of the HIGH count: the plain anchor and all its relative
ray twists. -/
def highDictionary {κ : Type} (anchors : κ → Character) (η₀ : Character) :
    κ × WholeSourceIndex rayM H → Character :=
  fun x => wholeSourceBase rayM H hH η₀ (anchors x.1) x.2

/-- **HIGH row count of one bin.** The kept rows of nonzero weight with lower guard
`b ≤ max` at height `T'` are zero rows of the fixed natural dictionary. -/
theorem high_row_count {κ : Type} [Fintype κ] (anchors : κ → Character) (η₀ : Character)
    (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ {Z bΦ : ℝ}, 0 < bΦ → ∀ (j : κ) (st : NaturalState Z 0 bΦ),
      st.character = anchors j → st.puncture = 1 →
      ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
        (b T' : ℝ), 33/40 ≤ b → b ≤ 7/8 → 0 ≤ T' →
      ∀ rows : Finset O, (∀ z ∈ rows, ∃ hz : st.radial.keep z,
        st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
        b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T') →
      (rows.card : ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(unmarkedDensity (2*b-1)+loss) := by
  obtain ⟨J, C, hC, hcount⟩ := fixed_natural_dictionary_raw_density
    (orientedFixedBase (highDictionary rayM H hH anchors η₀)) loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro Z bΦ hbΦ j st hchar hu hQM hQη b T' hb hb' hT' rows hrows
  let rows' : Finset NonzeroFrequency := rows.subtype (fun z => z ≠ 0)
  have hcard : rows'.card = rows.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    intro z hz
    obtain ⟨hk, _⟩ := hrows z hz
    exact st.row_ne_zero z hk
  have hZ0 : 0 < Z := zero_lt_one.trans_le st.base_ge_one
  have hH0 : 0 < bΦ*Z^st.rowWidth := mul_pos hbΦ (Real.rpow_pos_of_pos hZ0 _)
  rw [← hcard]
  apply hcount Prod.snd b T' hb hb' hT' _ hH0 rows'
  intro u hu'
  have hz : u.val ∈ rows := Finset.mem_subtype.mp hu'
  obtain ⟨hk, hp, hmax⟩ := hrows u.val hz
  refine ⟨?_, ?_⟩
  · -- the frequency norm
    have hs := st.radial_support hp
    have h1 : ‖eisEmbedding u.val‖^2 ≤ bΦ*st.radial.scale :=
      (div_le_iff₀ st.radial.scale_pos).mp hs
    rw [st.scale_eq, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at h1
    exact h1
  · -- the zero transfer to the fixed dictionary
    have hc0 : ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character
          st.puncture) I =
        idealCoeff (excluded (naturalRow (anchors j) u.val u.property).character 1) I := by
      intro I
      rw [hu, excluded_ideal _ _ one_ne_zero, excluded_ideal _ _ one_ne_zero,
        NaturalRow.ideal, NaturalRow.ideal, hchar]
    exact physical_family_maximum_to_fixed_dictionary (highDictionary rayM H hH anchors η₀)
      (Cycle61InitialMass.geometryRowFamily rayM H hH st η₀ u.val hk) (fun _ => false)
      (Cycle61InitialMass.geometry_row_family_nonprincipal rayM H hH st η₀ hQM hQη u.val hk)
      (fun idx => (j, idx)) (fun _ => 1) u
      (fun idx I => whole_source_family_mask rayM H hH η₀ (anchors j)
        (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character
          st.puncture) u.val u.property (naturalRow (anchors j) u.val u.property) 1
        one_ne_zero hc0
        (fun idx => naturalRow (wholeSourceBase rayM H hH η₀ (anchors j) idx) u.val
          u.property) idx I)
      b T' (by linarith) hmax

end
end
end QRH.DensitySplitThird.Density
