/- Pointwise suppliers of the marked HIGH branch.

* `high_row_plain_factor`: for a kept row of nonzero weight whose whole ray-twisted family has
  zero maximum `< a + 2e` at the supplier height `3(i+1)Z^τ`, the packed row
  `positiveSlotRow` is bounded by the two ordinary factors, `K·ctl²·Z^{(2a-1)(P₁+P₂)+2ε₁d}`, times
  the squared product of the slots at amplitude `max 1 ‖slot‖`. This is the first half of the
  full-amplitude HIGH row bound (`high_row_bound`) and stops before the slot product; the
  slots stay in the raw natural form summed by the repeated-mark dictionary count
  (Collet's `eventual_natural_positive_raw`).
* `high_slot_bound`: one slot at full amplitude, `(max 1 ‖slot‖)² ≤ Cs·Z^{2ε_s d + (2a-1) w}`
  (Collet's `actual_high_slots`). -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularPositiveRawNatural
import Submissions.hailey_collet_1252270103.Cycle61.Moment.HighRetainedRows
import Submissions.sil_density_split_20261026.Density.LeafRows

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.ArviDensity.Density
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
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

/-- The parameter record of Collet's HIGH suppliers at the unit puncture (`Bmask = 0`), unit slot
width bound (`Rwidth = 1`), slots of amplitude `σ = 33/50` and slot ranges `[1,2]`; the height
gates have exponent `ε₁/8`. -/
def markedParameters (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (hW : ContDiff ℝ ∞ W) (bΦ Mcap Rplain d τ εslot ε₁ e κ : ℝ)
    (bound : ℕ → ℝ) (hbound : ∀ k, 0 ≤ bound k)
    (hbΦ : 0 ≤ bΦ) (hRp : 0 ≤ Rplain) (hd : 0 < d) (hdsupply : Mcap + 0 + 1 ≤ d)
    (hτ : 0 < τ) (hεs : 0 < εslot) (hε₁ : 0 < ε₁) (he : 0 < e) (he' : e < 1/1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hslotBudget : 8*e*1 + κ ≤ εslot)
    (hplainBudget : 12*e*(Rplain+2) + 8*κ + 2*(ε₁/8) ≤ ε₁) : HighSourceParameters where
  Wslot := W
  A₀ := 1
  B₀ := 2
  hA₀ := one_pos
  hWs := hWs
  hW := hW
  Rwidth := 1
  Rplain := Rplain
  dmax := d
  τ := τ
  εslot := εslot
  εplain := ε₁
  e := e
  κ := κ
  vplain := ε₁/8
  vslot := ε₁/8
  σmin := 33/50
  σmax := 33/50
  bΦ := bΦ
  Mcap := Mcap
  Bmask := 0
  margin := 1
  d := d
  hRw := zero_le_one
  hRp := hRp
  hdmax := hd.le
  hτ := hτ
  hεs := hεs
  hεp := hε₁
  he := he
  he' := he'
  hκ := hκ
  hκ' := hκ'
  hvp := by positivity
  hvs := by positivity
  hslotBudget := hslotBudget
  hplainBudget := hplainBudget
  hbΦ := hbΦ
  hmargin := one_pos
  hd := hd
  hdsupply := hdsupply
  hdm := le_rfl
  profileBound := bound
  hprofile := hbound

/-- The ordinary lengths bound the scales: `X ≤ Z^{length Z X}` for `X > 0`. -/
theorem le_rpow_length {Z X : ℝ} (hZ : 1 < Z) : X ≤ Z^(length Z X) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  unfold length
  rw [Real.rpow_logb hZ0 hZ.ne' (zero_lt_one.trans_le (le_max_left _ _))]
  exact le_max_right _ _

theorem length_nonneg' {Z : ℝ} (X : ℝ) (hZ : 1 < Z) : 0 ≤ length Z X := by
  unfold length
  exact Real.logb_nonneg hZ (le_max_left _ _)

theorem le_rpow_of_length_le' {Z X L : ℝ} (hZ : 1 < Z) (h : length Z X ≤ L) : X ≤ Z^L :=
  (le_rpow_length hZ).trans (Real.rpow_le_rpow_of_exponent_le hZ.le h)

section
variable (rayM : Ideal O) [NeZero rayM]
local instance leafHighRowMarkedQuotientFinite : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- **Plain factors of a HIGH row.** The constants `K`, `S` come first (after the parameters and
the height scale `τ`), then the anchor `η₀`, then the threshold in `Z`; then the state, the row,
its bin value `a` with the upper guard, the slot data, the ordinary profiles and lengths. -/
theorem high_row_plain_factor (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (hW : ContDiff ℝ ∞ W) (bΦ Mcap Lplain d τ εslot ε₁ e κ : ℝ)
    (hbΦ : 0 ≤ bΦ) (hL : 0 ≤ Lplain) (hd : 0 < d) (hdsupply : Mcap + 0 + 1 ≤ d)
    (hτ : 0 < τ) (hεs : 0 < εslot) (hε₁ : 0 < ε₁) (he : 0 < e) (he' : e < 1/1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hslotBudget : 8*e*1 + κ ≤ εslot)
    (hplainBudget : 12*e*(Lplain/d+2) + 8*κ + 2*(ε₁/8) ≤ ε₁)
    (hτd : 128*τ ≤ d*ε₁) :
    ∃ K : ℝ, 0 < K ∧ ∃ S : Finset (ℕ×ℕ), ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ st : NaturalState Z 0 bΦ, st.width ≤ Mcap →
    ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
      (z : O) (hz : st.radial.keep z),
      st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 →
    ∀ (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 1 → (i:ℝ) ≤ Z^τ →
      Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz (3*(i+1 : ℕ)*Z^τ) <
        a + 2*e →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (pool : ι → Finset (Ideal O))
      (β : ι → Ideal O → ℂ) (P : ι → ℝ), (∀ k, 0 < P k) →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ t : ℝ), 0 < X₁ → 0 < X₂ →
      length Z X₁ ≤ Lplain → length Z X₂ ≤ Lplain →
      |t| + Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1) pool β P t X₁ X₂‖^2 ≤
        K * (p.control S)^2 *
          Z^((2*a-1)*(length Z X₁ + length Z X₂) + 2*ε₁*d) *
          (∏ k, max 1 ‖normalizedSlot st.character st.mask 1 z (pool k) (β k) t (P k)‖)^2 := by
  obtain ⟨bound, hbound, hsource⟩ :=
    OAI.SevenEighths.Record1252270103Source.eventual_natural_positive_raw rayM H hH (1/4) (9/4)
      (by norm_num)
  have hRp : 0 ≤ Lplain/d := div_nonneg hL hd.le
  let P := markedParameters W hWs hW bΦ Mcap (Lplain/d) d τ εslot ε₁ e κ bound
    (fun k => (hbound k).le) hbΦ hRp hd hdsupply hτ hεs hε₁ he he' hκ hκ' hslotBudget hplainBudget
  obtain ⟨T, C, hC, hraw⟩ := hsource P rfl (by change 8*τ ≤ d*(ε₁/8); nlinarith)
    (by change 16*τ ≤ d*(ε₁/8); nlinarith)
  refine ⟨C, hC, T, ?_⟩
  intro η₀
  filter_upwards [hraw η₀] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro st hst hQM hQη z hz hp a i ha ha' hi hup ι _ _ pool β Ps hPs p X₁ X₂ t hX₁ hX₂ hl₁ hl₂ hwin
  have hZ1 : 1 < Z := hZ.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hX : ∀ k, 0 < ![X₁, X₂] k := by
    intro k; fin_cases k
    · exact hX₁
    · exact hX₂
  have hcap : ∀ k, ![X₁, X₂] k ≤ Z^(P.d * P.Rplain) := by
    have h0 : P.d * P.Rplain = Lplain := by
      change d * (Lplain/d) = Lplain
      field_simp
    intro k; fin_cases k
    · exact (h0 ▸ le_rpow_of_length_le' hZ1 hl₁)
    · exact (h0 ▸ le_rpow_of_length_le' hZ1 hl₂)
  have hb := hZ.2 st hQM hQη z hz hst hp a i ha ha' hi hup pool β Ps hPs p ![X₁, X₂] t hX hcap hwin
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb
  have hν : 0 ≤ 2*a-1 := by linarith
  have hprod : (X₁ * X₂)^(2*a-1) ≤ Z^((2*a-1)*(length Z X₁ + length Z X₂)) := by
    have h1 : X₁ * X₂ ≤ Z^(length Z X₁ + length Z X₂) := by
      rw [Real.rpow_add hZ0]
      exact mul_le_mul (le_rpow_length hZ1) (le_rpow_length hZ1) hX₂.le (Real.rpow_nonneg hZ0.le _)
    calc (X₁ * X₂)^(2*a-1) ≤ (Z^(length Z X₁ + length Z X₂))^(2*a-1) :=
          Real.rpow_le_rpow (mul_pos hX₁ hX₂).le h1 hν
      _ = _ := by rw [← Real.rpow_mul hZ0.le]; ring_nf
  have hslot : ∀ k, naturalSlot (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character
        st.puncture) (pool k) (heightCoefficient (β k) t) (Ps k) =
      normalizedSlot st.character st.mask 1 z (pool k) (β k) t (Ps k) := fun k =>
    (OAI.SevenEighths.Record1252270103Source.positive_raw_natural_slot
      (naturalRow st.character z (st.row_ne_zero z hz)) st.puncture st.puncture_ne_zero (pool k)
      (β k) (Ps k) t).symm
  simp only [hslot] at hb
  refine hb.trans ?_
  have hctl := p.control_nonneg T
  have hpow : (X₁ * X₂)^(2*a-1) * Z^(2*P.εplain*P.d) ≤
      Z^((2*a-1)*(length Z X₁ + length Z X₂) + 2*ε₁*d) := by
    rw [Real.rpow_add hZ0]
    exact mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hZ0.le _)
  have hrest : 0 ≤ (∏ k, max 1 ‖normalizedSlot st.character st.mask 1 z (pool k) (β k) t (Ps k)‖)^2 :=
    sq_nonneg _
  calc C * (p.control T)^2 * (X₁ * X₂)^(2*a-1) * Z^(2*P.εplain*P.d) *
        (∏ k, max 1 ‖normalizedSlot st.character st.mask 1 z (pool k) (β k) t (Ps k)‖)^2
      = C * (p.control T)^2 * ((X₁ * X₂)^(2*a-1) * Z^(2*P.εplain*P.d)) *
        (∏ k, max 1 ‖normalizedSlot st.character st.mask 1 z (pool k) (β k) t (Ps k)‖)^2 := by ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hrest
        exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- **One slot at full amplitude.** For a row with the upper guard `< a + 2e` at the supplier
height, a single prime slot of width `w ≤ 1` and amplitude `σ = 33/50` has
`(max 1 ‖slot‖)² ≤ Cs · Z^{2ε_s d + (2a-1) w}`. -/
theorem high_slot_bound (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (hW : ContDiff ℝ ∞ W) (bΦ Mcap d τ εslot ε₁ e κ : ℝ)
    (hbΦ : 0 ≤ bΦ) (hMcap : 0 ≤ Mcap) (hd : 0 < d) (hdsupply : Mcap + 0 + 1 ≤ d)
    (hτ : 0 < τ) (hεs : 0 < εslot) (hε₁ : 0 < ε₁) (he : 0 < e) (he' : e < 1/1000)
    (hκ : 0 < κ) (hslotBudget : 8*e*1 + κ ≤ εslot) (hτd : 48*τ ≤ d*ε₁) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ st : NaturalState Z 0 bΦ, st.width ≤ Mcap →
    ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
      (z : O) (hz : st.radial.keep z),
      st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 →
    ∀ (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 1 → (i:ℝ) ≤ Z^τ →
      Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz (3*(i+1 : ℕ)*Z^τ) <
        a + 2*e →
    ∀ (w σ t v : ℝ) (θ : RayQuotient.Characters rayM H), 0 ≤ w → w ≤ 1 →
      (33/50:ℝ) ≤ σ → σ ≤ 33/50 → |t+v| + Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (max 1 ‖normalizedSlot st.character st.mask 1 z (primePool rayM H 2 (Z^w))
        (fun I => idealCoeff (relativeCharacter rayM H hH η₀ θ) I *
          HeckePrimeAnnular.annularWeight W (Z^w) σ v I) t (Z^w)‖)^2 ≤
        Cs * Z^(2*εslot*d + (2*a-1)*w) := by
  obtain ⟨C, hC, hslots⟩ := actual_high_slots rayM H hH W 1 2 one_pos hWs hW 1 d τ εslot e κ
    (ε₁/8) (33/50) (33/50) bΦ Mcap 0 1 d zero_le_one hd.le hτ hεs he he' hκ (by positivity)
    hslotBudget hbΦ one_pos hd hdsupply le_rfl
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro η₀
  have hgate : ∀ᶠ Z : ℝ in atTop, ∀ i : ℕ, (i:ℝ) ≤ Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^(ε₁/8) := by
    filter_upwards [(tendsto_rpow_atTop hτ).eventually (eventually_ge_atTop (8:ℝ)),
      eventually_gt_atTop (1:ℝ)] with Z hy hZ
    intro i hi
    have hZ0 : 0 < Z := zero_lt_one.trans hZ
    have hy0 : (0:ℝ) ≤ Z^τ := Real.rpow_nonneg hZ0.le _
    have h1 : (3+(3*i+2 : ℕ)*Z^τ) ≤ (Z^τ)^3 := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hi hy0, sq_nonneg (Z^τ - 8)]
    have h6 : ((Z^τ)^3)^2 = Z^(τ*6) := by
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
      norm_num
    calc (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ ((Z^τ)^3)^2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = Z^(τ*6) := h6
      _ ≤ Z^(d*(ε₁/8)) := Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)
      _ = (Z^d)^(ε₁/8) := by rw [← Real.rpow_mul hZ0.le]
  filter_upwards [hslots η₀, hgate] with Z hZ hg
  refine ⟨hZ.1, ?_⟩
  intro st hst hQM hQη z hz hp a i ha ha' hi hup w σ t v θ hw0 hw1 hσ hσ' hwin
  have hZ1 : 1 < Z := hZ.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hAL : LowBranch.ActualLow rayM H hH st η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ) z :=
    whole_source_upper_actual_low rayM H hH st η₀ hQM hQη z hz a e _ hp hup
  have hd1 : 1 ≤ d := by linarith
  have hb := hZ.2 st hst hQM hQη a i ha ha' w σ t v hw0 (by rw [div_le_one hd]; linarith) hσ hσ'
    hwin (hg i hi) z hz hAL θ
  have hν : 0 ≤ 2*a-1 := by linarith
  have hexp : 0 ≤ 2*εslot*d + (2*a-1)*w := by positivity
  have hU : 1 ≤ Z^(2*εslot*d + (2*a-1)*w) := Real.one_le_rpow hZ1.le hexp
  have hU0 : 0 ≤ Z^(2*εslot*d + (2*a-1)*w) := Real.rpow_nonneg hZ0.le _
  rw [← OAI.SevenEighths.Record1252270103Source.positive_raw_max_square _ (norm_nonneg _)]
  have hb' : ‖normalizedSlot st.character st.mask 1 z (primePool rayM H 2 (Z^w))
      (fun I => idealCoeff (relativeCharacter rayM H hH η₀ θ) I *
        HeckePrimeAnnular.annularWeight W (Z^w) σ v I) t (Z^w)‖^2 ≤
      C * Z^(2*εslot*d + (2*a-1)*w) := by
    rw [Real.rpow_add hZ0, ← mul_assoc]
    exact hb
  calc max 1 (‖normalizedSlot st.character st.mask 1 z (primePool rayM H 2 (Z^w))
        (fun I => idealCoeff (relativeCharacter rayM H hH η₀ θ) I *
          HeckePrimeAnnular.annularWeight W (Z^w) σ v I) t (Z^w)‖^2)
      ≤ max 1 (C * Z^(2*εslot*d + (2*a-1)*w)) := max_le_max le_rfl hb'
    _ ≤ max 1 C * Z^(2*εslot*d + (2*a-1)*w) :=
        max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hU)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hU0)

end
end
end QRH.ArviDensity.Density
