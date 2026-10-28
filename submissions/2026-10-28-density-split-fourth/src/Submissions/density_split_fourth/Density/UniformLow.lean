/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform-in-`q` LOW slot and erasure suppliers.

The packaged PR69 LOW suppliers (`actual_low_slots_parent_mask`,
`actual_restricted_erasure_supplier`) fix the cut `q` before their constant.
Here the constant and the eventual threshold are taken from the already
`a`-uniform HIGH slot bound `Cycle61Moment.actual_high_slots`; the cut `q` is
quantified only after `∀ᶠ Z`. Per row the guard is
`ActualLow … (a r) e (3(i r+1)Z^τ) (z r)` with `51/100 ≤ a r ≤ (1+q)/2`
(in particular `a r := (q+1)/2`, as supplied by `retained_zero_bin_low`).
The exponent `(2a-1)w` is bounded by `q w` since `2a-1 ≤ q`, `w ≥ 0`, `Z ≥ 1`;
the enlarged puncture is removed by `normalized_slot_puncture`. -/
import Submissions.hailey_collet_1252270103.Cycle61.Moment.HighSlots
import Submissions.hailey_collet_1252270103.Record1252270103Source.LowErasure.Slots
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalLowErasurePartition
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.DensitySplitThird.Density
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths
open Cycle61Moment.LowBranch QRH.Record1252270103Source.LowErasure
open QRH.Record1252270103Source.High.GlobalPhysical
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open ConcretePrimeRowBridge Record1252270103Second
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance uniformLowQuotientFinite : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Uniform-in-`q` LOW slots at the parent mask. One constant `C`, then the
anchor `η₀`, then one eventual threshold in `Z`, and only then the cut `q ≤ 1`
and the row gate `51/100 ≤ a ≤ (1+q)/2` with `ActualLow … a e …`. -/
theorem uniform_low_slots_parent_mask
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ q : ℝ, q ≤ 1 →
      ∀ s : NaturalState Z Bmask bΦ, s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
        (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ (1+q)/2 →
      ∀ w σ t v : ℝ, 0 ≤ w → w/d ≤ Rwidth → σmin ≤ σ → σ ≤ σmax →
        |t+v|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
        (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ z : O, s.radial.keep z → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*Z^τ) z → ∀ θ : RayQuotient.Characters M H,
      ∀ R extra : Ideal O, s.puncture=R*extra →
      (∀ I∈primePool M H B (Z^w), IsCoprime I extra) →
      ‖normalizedSlot s.character (fixedBadMask*idealGenerator R) 1 z (primePool M H B (Z^w))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ θ) I*
          annularWeight W (Z^w) σ v I) t (Z^w)‖^2 ≤
        (C*Z^(2*ε*d))*Z^(q*w) := by
  obtain ⟨C,hC,hslots⟩ := Cycle61Moment.actual_high_slots M H hH
    W A B hA hWs hW Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hε he he' hκ hη hbudget hbΦ hmargin hd hdsupply hdm
  refine ⟨C,hC,?_⟩
  intro η₀
  filter_upwards [hslots η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro q hq1 s hs hQM hQη a i ha ha' w σ t v hw hwr hσ hσ' hfreq hheight z hz hlow θ
    R extra hpuncture havoid
  have ha1 : a ≤ 1 := by linarith
  have hh := hZ.2 s hs hQM hQη a i ha ha1 w σ t v hw hwr hσ hσ' hfreq hheight z hz hlow θ
  have hm : s.mask=fixedBadMask*idealGenerator (R*extra) := by
    change fixedBadMask*idealGenerator s.puncture=_
    rw [hpuncture]
  rw [hm, normalized_slot_puncture _ R extra _ _ _ _ _ _ havoid] at hh
  have hexp : (2*a-1)*w ≤ q*w := mul_le_mul_of_nonneg_right (by linarith) hw
  have hZ0 : 0 < Z := zero_lt_one.trans hZ.1
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le hexp) (by positivity))

/-- Uniform-in-`q` restricted LOW erasure supplier: the conclusion of PR69's
`actual_restricted_erasure_supplier`, with `Cslot` and the eventual threshold
chosen before the cut `q`. Rows of nonzero weight carry the guard
`ActualLow … (a r) e (3(i r+1)Z^τ) (z r)` with `51/100 ≤ a r ≤ (1+q)/2`. -/
theorem uniform_restricted_erasure_supplier
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ Cslot : ℝ, 1≤Cslot ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀ q : ℝ, q ≤ 1 →
    ∀ {Row Slot : Type*} (rows : Finset Row) (T : Finset Slot)
      (weight : Row→ℝ) (D : Row→ℂ) (st : Row→NaturalState Z Bmask bΦ)
      (hQM : ∀r,(st r).fixedModulus≤M) (hQη : ∀r,(st r).fixedModulus≤η₀.modulus)
      (z : Row→O) (t a : Row→ℝ) (i : Row→ℕ) (parentR extraR : Row→Ideal O)
      (θ : Slot→RayQuotient.Characters M H) (w σ v : Slot→ℝ),
    (∀r∈rows,0≤weight r) →
    (∀r∈rows,(st r).width≤Mcap) →
    (∀r∈rows,(st r).puncture=parentR r*extraR r) →
    (∀r∈rows,51/100≤a r) → (∀r∈rows,a r≤(1+q)/2) →
    (∀j∈T,0≤w j) → (∀j∈T,w j/d≤Rwidth) →
    (∀j∈T,σmin≤σ j) → (∀j∈T,σ j≤σmax) →
    (∀r∈rows,∀j∈T,|t r+v j|+Z^τ/2≤(3*i r+2:ℕ)*Z^τ) →
    (∀r∈rows,(3+(3*i r+2:ℕ)*Z^τ)^2≤(Z^d)^η) →
    (∀r∈rows,∀j∈T,∀I∈primePool M H B (Z^(w j)),IsCoprime I (extraR r)) →
    (∀r∈rows,weight r≠0 → (st r).radial.keep (z r)) →
    (∀r∈rows,weight r≠0 → ActualLow M H hH (st r) η₀ (hQM r) (hQη r) (a r) e
      (3*(i r+1:ℕ)*Z^τ) (z r)) →
    let slot := fun r j => normalizedSlot (st r).character (fixedBadMask*idealGenerator (parentR r))
      1 (z r) (primePool M H B (Z^(w j)))
      (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
        annularWeight W (Z^(w j)) (σ j) (v j) I) (t r) (Z^(w j))
    let pay := Cslot*Z^(2*ε*d)
    (∀ F : Finset Slot, F⊆T → retainedNorm rows weight D slot T≤
      erasurePayment Z q pay w T F*retainedNorm rows weight D slot F) ∧
    (∀ select : Row→Finset Slot, (∀r∈rows,select r⊆T) →
      retainedNorm rows weight D slot T≤
        ∑F∈T.powerset,erasurePayment Z q pay w T F*
          retainedNorm (rows.filter (fun r=>select r=F)) weight D slot F) := by
  obtain ⟨C,hC,hslots⟩ := uniform_low_slots_parent_mask M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hε he he' hκ hη hbudget hbΦ hmargin hd hdsupply hdm
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro η₀
  filter_upwards [hslots η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro q hq1 Row Slot rows T weight D st hQM hQη z t a i parentR extraR θ w σ v
    hweight hwidth hpuncture ha ha' hw hwr hσ hσ' hfreq hheight havoid hkeep hlow slot pay
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  have hslot : ∀r∈rows,weight r≠0 → ∀j∈T,‖slot r j‖^2≤pay*Z^(q*w j) := by
    intro r hr hn j hj
    have hh := hZ.2 q hq1 (st r) (hwidth r hr) (hQM r) (hQη r) (a r) (i r) (ha r hr)
      (ha' r hr) (w j) (σ j) (t r) (v j) (hw j hj) (hwr j hj) (hσ j hj) (hσ' j hj)
      (hfreq r hr j hj) (hheight r hr) (z r) (hkeep r hr hn) (hlow r hr hn) (θ j)
      (parentR r) (extraR r) (hpuncture r hr) (havoid r hr j hj)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 C) (Real.rpow_nonneg hZ0.le _))
      (Real.rpow_nonneg hZ0.le _))
  constructor
  · intro F hF
    exact fixed_retained_norm rows weight D slot T F hF hweight Z q pay w hZ0
      (fun r hr hn j hj=>hslot r hr hn j (Finset.mem_sdiff.mp hj).1)
  · intro select hs
    exact restricted_varying_retained_norm rows weight D slot T select hs hweight Z q pay w hZ0
      (fun r hr hn j hj=>hslot r hr hn j (Finset.mem_sdiff.mp hj).1)

end
end QRH.DensitySplitThird.Density
