/- Mixed source step, L3: new in this submission; uses the collision lemmas (Collision/), the
transfer's lemmas (Transfer/, Residual/) and the baseline's `idealRowHom_zero_of_dvd` by import.

The transfer inside a collision family.

* `tc_mark_elim`: on a tuple whose product is coprime to the colliding product `D = D₀ D₁`, the
  family coefficient with the marks `A_k·D_k` and the coprimality `R·D` equals the coefficient
  with the marks `A_k` and `R` (when `D` is squarefree, coprime to `A₁A₂` and has no small prime).
* `famEnergy_elim`: so the family energy (row twist `idealRowHom (δ³)`) is at most the energy of
  the plainly marked family under the twisted character `twistChar τ (δ³)`: on a column that
  shares a prime with `D` the twist vanishes, on the other columns the coefficients agree, and a
  small prime in `D` kills the family. -/
import Submissions.arvi_mixed_step.Residual.CollisionFamilies
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.GaussNormalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.RowCompletion.SupportBounds

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

universe u

namespace QRH.MixedStep.Collision
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentRectangle
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103TwoIdeal
open QRH.Record1252270103Source.High QRH.MixedStep.Transfer
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentSecondHeightFamily CenteredMomentLiveDomain RayFourExpansion
open CenteredMomentChildRows CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstColumns CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open Candidate.FourthPower CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- `D` has no small prime. -/
def SmallFree (D₀ D₁ : Ideal O) : Prop :=
  ∀ P ∈ QRH.Record1252270103KernelMass.smallPrimes,
    QRH.Record1252270103KernelMass.valuation D₀ P.val = 0 ∧
      QRH.Record1252270103KernelMass.valuation D₁ P.val = 0

theorem hole_mark_iff (A₁ A₂ D₀ D₁ a₀ a₁ : Ideal O) (hA₁ : A₁ ≠ 0) (hA₂ : A₂ ≠ 0)
    (hD₀ : D₀ ≠ 0) (hD₁ : D₁ ≠ 0) (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0) (hs : SmallFree D₀ D₁) :
    QRH.Record1252270103Restoration.ordinarySmallHole (A₁ * D₀ * a₀) (A₂ * D₁ * a₁) ↔
      QRH.Record1252270103Restoration.ordinarySmallHole (A₁ * a₀) (A₂ * a₁) := by
  unfold QRH.Record1252270103Restoration.ordinarySmallHole
  have h1 : ∀ P : Ideal O, QRH.Record1252270103KernelMass.valuation (A₁ * D₀ * a₀) P =
      QRH.Record1252270103KernelMass.valuation (A₁ * a₀) P +
        QRH.Record1252270103KernelMass.valuation D₀ P := by
    intro P
    rw [QRH.Record1252270103KernelMass.valuation_mul (mul_ne_zero hA₁ hD₀) ha₀,
      QRH.Record1252270103KernelMass.valuation_mul hA₁ hD₀,
      QRH.Record1252270103KernelMass.valuation_mul hA₁ ha₀]
    ring
  have h2 : ∀ P : Ideal O, QRH.Record1252270103KernelMass.valuation (A₂ * D₁ * a₁) P =
      QRH.Record1252270103KernelMass.valuation (A₂ * a₁) P +
        QRH.Record1252270103KernelMass.valuation D₁ P := by
    intro P
    rw [QRH.Record1252270103KernelMass.valuation_mul (mul_ne_zero hA₂ hD₁) ha₁,
      QRH.Record1252270103KernelMass.valuation_mul hA₂ hD₁,
      QRH.Record1252270103KernelMass.valuation_mul hA₂ ha₁]
    ring
  constructor
  · intro h P hP
    have := h P hP
    rw [h1, h2] at this
    omega
  · intro h P hP
    have := h P hP
    have hsP := hs P hP
    rw [h1, h2]
    omega

theorem hole_mark_false (A₁ A₂ D₀ D₁ a₀ a₁ : Ideal O) (hA₁ : A₁ ≠ 0) (hA₂ : A₂ ≠ 0)
    (hD₀ : D₀ ≠ 0) (hD₁ : D₁ ≠ 0) (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0) (hs : ¬SmallFree D₀ D₁) :
    ¬QRH.Record1252270103Restoration.ordinarySmallHole (A₁ * D₀ * a₀) (A₂ * D₁ * a₁) := by
  unfold SmallFree at hs
  push Not at hs
  obtain ⟨P, hP, hne⟩ := hs
  unfold QRH.Record1252270103Restoration.ordinarySmallHole
  push Not
  refine ⟨P, hP, ?_⟩
  intro h0
  rw [QRH.Record1252270103KernelMass.valuation_mul (mul_ne_zero hA₁ hD₀) ha₀,
    QRH.Record1252270103KernelMass.valuation_mul hA₁ hD₀] at h0
  rw [QRH.Record1252270103KernelMass.valuation_mul (mul_ne_zero hA₂ hD₁) ha₁,
    QRH.Record1252270103KernelMass.valuation_mul hA₂ hD₁]
  intro h1
  apply hne (by omega)
  omega

/-- **Mark elimination on one tuple.** -/
theorem tc_mark_elim {μ : Type*} [Fintype μ] [DecidableEq μ] (s' : Input μ) (A₁ A₂ D₀ D₁ D Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (a : Tuple μ) (ha : a ∈ Fintype.piFinset s'.pools) (hD : D₀ * D₁ = D)
    (hcop : IsCoprime (finiteTupleProduct a) (D₀ * D₁)) (hsq : Squarefree (D₀ * D₁))
    (hDA : IsCoprime (D₀ * D₁) (A₁ * A₂)) (hs : SmallFree D₀ D₁) (hA₁ : A₁ ≠ 0) (hA₂ : A₂ ≠ 0) :
    CoupledFirst.tupleCoefficient s' (markedSourceModifier (A₁ * D₀) (A₂ * D₁) Dc K F)
        (R * D) L a =
      CoupledFirst.tupleCoefficient s' (markedSourceModifier A₁ A₂ Dc K F) R L a := by
  subst hD
  have ha' := (mem_pools_iff s' a).mp (Fintype.mem_piFinset.mp ha)
  have ha₀ : a (Sum.inr 0) ≠ 0 := s'.plain₁_ne _ ha'.2.1
  have ha₁ : a (Sum.inr 1) ≠ 0 := s'.plain₂_ne _ ha'.2.2
  have hD₀ : D₀ ≠ 0 := left_ne_zero_of_mul hsq.ne_zero
  have hD₁ : D₁ ≠ 0 := right_ne_zero_of_mul hsq.ne_zero
  -- the hole
  have hhole := hole_mark_iff A₁ A₂ D₀ D₁ (a (Sum.inr 0)) (a (Sum.inr 1)) hA₁ hA₂ hD₀ hD₁ ha₀ ha₁ hs
  -- the squarefree projector
  have hplain : IsCoprime (D₀ * D₁) (a (Sum.inr 0) * a (Sum.inr 1)) := by
    have h : a (Sum.inr 0) * a (Sum.inr 1) ∣ finiteTupleProduct a := by
      rw [finiteTupleProduct_split]
      exact dvd_mul_left _ _
    exact (hcop.symm).of_isCoprime_of_dvd_right h
  have hsqiff : Squarefree (A₁ * D₀ * a (Sum.inr 0) * (A₂ * D₁) * a (Sum.inr 1)) ↔
      Squarefree (A₁ * a (Sum.inr 0) * A₂ * a (Sum.inr 1)) := by
    have he : A₁ * D₀ * a (Sum.inr 0) * (A₂ * D₁) * a (Sum.inr 1) =
        (D₀ * D₁) * (A₁ * a (Sum.inr 0) * A₂ * a (Sum.inr 1)) := by ring
    have hc : IsCoprime (D₀ * D₁) (A₁ * a (Sum.inr 0) * A₂ * a (Sum.inr 1)) := by
      have he2 : A₁ * a (Sum.inr 0) * A₂ * a (Sum.inr 1) =
          (A₁ * A₂) * (a (Sum.inr 0) * a (Sum.inr 1)) := by ring
      rw [he2]
      exact hDA.mul_right hplain
    rw [he, squarefree_mul_iff]
    constructor
    · exact fun h => h.2.2
    · exact fun h => ⟨hc.isRelPrime, hsq, h⟩
  have hmod : markedSourceModifier (A₁ * D₀) (A₂ * D₁) Dc K F a =
      markedSourceModifier A₁ A₂ Dc K F a := by
    unfold markedSourceModifier sourceModifier coupledFactor ordinaryHoleIndicator squarefreeIndicator
    rw [if_congr hhole rfl rfl, if_congr hsqiff rfl rfl]
  have hprof : profileCoefficient (R * (D₀ * D₁)) s'.ν s'.W s'.P s'.W₁ s'.W₂ s'.X₁ s'.X₂ s'.Y₁
      s'.Y₂ 1 1 L a =
      profileCoefficient R s'.ν s'.W s'.P s'.W₁ s'.W₂ s'.X₁ s'.X₂ s'.Y₁ s'.Y₂ 1 1 L a := by
    unfold profileCoefficient
    have hiff : IsCoprime (finiteTupleProduct a) (R * (D₀ * D₁)) ↔
        IsCoprime (finiteTupleProduct a) R := by
      rw [IsCoprime.mul_right_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, hcop⟩⟩
    rw [if_congr hiff rfl rfl]
  unfold CoupledFirst.tupleCoefficient
  rw [hmod, hprof]

/-- With a small prime in `D` the family coefficient vanishes. -/
theorem tc_mark_small {μ : Type*} [Fintype μ] [DecidableEq μ] (s' : Input μ) (A₁ A₂ D₀ D₁ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (a : Tuple μ) (ha : a ∈ Fintype.piFinset s'.pools) (hD₀ : D₀ ≠ 0)
    (hD₁ : D₁ ≠ 0) (hs : ¬SmallFree D₀ D₁) (hA₁ : A₁ ≠ 0) (hA₂ : A₂ ≠ 0) :
    CoupledFirst.tupleCoefficient s' (markedSourceModifier (A₁ * D₀) (A₂ * D₁) Dc K F) R L a = 0 := by
  have ha' := (mem_pools_iff s' a).mp (Fintype.mem_piFinset.mp ha)
  have ha₀ : a (Sum.inr 0) ≠ 0 := s'.plain₁_ne _ ha'.2.1
  have ha₁ : a (Sum.inr 1) ≠ 0 := s'.plain₂_ne _ ha'.2.2
  have h := hole_mark_false A₁ A₂ D₀ D₁ _ _ hA₁ hA₂ hD₀ hD₁ ha₀ ha₁ hs
  unfold CoupledFirst.tupleCoefficient markedSourceModifier sourceModifier ordinaryHoleIndicator
  simp only [h, ↓reduceIte, mul_zero, zero_mul]

/-! ### The family energy -/

/-- The family energy with the plain marks `A_k`, the coprimality `R`, and the row twist absorbed
into the character `twistChar τ (δ³)`. -/
def famEnergyT (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (x : {u // u ∈ selBox s Q})
    (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T H : ℝ) : ℝ :=
  (gaussEnergy Finset.univ
    (sourceGenerator (finiteColumns (collBox s Q σ x)))
    (sourceGenerator_supported (finiteColumns (collBox s Q σ x)))
    (fun I : supportedColumns (finiteColumns (collBox s Q σ x)) =>
      finiteColumnCoefficient (collBox s Q σ x)
        (noColPart (restBlock J Q)
          (CoupledFirst.tupleCoefficient (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1))
            (markedSourceModifier A₁ A₂ Dc K F) R (residualSeed Q L x.1))) I *
        ((Real.sqrt T : ℂ)⁻¹ *
          rowWeight (twistChar τ (primaryGenerator (selProduct Q x.1) ^ 3)) fixedBadMask 1 1 t I))
    ballProfile H).re

theorem gaussEnergy_zero_coeff {β : Type*} (S : Finset β) (a : β → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) :
    gaussEnergy S a ha (fun _ => (0 : ℂ)) W K = 0 := by
  have h := CenteredMomentGaussNormalization.gaussEnergy_const_mul S a ha (fun _ => (0 : ℂ)) 0 W K
  simp only [mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Complex.ofReal_zero, zero_mul] at h
  exact h

theorem selWeight_coprime (s : Input κ) (Q : Finset κ) (K R : Ideal O) (u : Q → Ideal O)
    (hw : selWeight s Q K R u ≠ 0) : IsCoprime (selProduct Q u) R := by
  by_contra hn
  apply hw
  simp only [selWeight, hn, ↓reduceIte, mul_zero]

/-- **The family energy is at most the plainly marked family energy under the twisted
character.** -/
theorem famEnergy_elim (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (x : {u // u ∈ selBox s Q})
    (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T H : ℝ)
    (hH : 0 < H) (hD : Supported (selProduct Q x.1)) (hw : selWeight s Q K R x.1 ≠ 0)
    (hA₁ : A₁ ≠ 0) (hA₂ : A₂ ≠ 0) (hAR : A₁ * A₂ ∣ R) :
    famEnergy s J Q σ x A₁ A₂ Dc K R L F τ t T H ≤
      famEnergyT s J Q σ x A₁ A₂ Dc K R L F τ t T H := by
  have hsq : Squarefree (selProduct Q x.1) := selWeight_squarefree s Q K R x.1 hw
  have hDA : IsCoprime (sideProd σ x.1 0 * sideProd σ x.1 1) (A₁ * A₂) := by
    rw [sideProd_mul]
    exact (selWeight_coprime s Q K R x.1 hw).of_isCoprime_of_dvd_right hAR
  have hu : ∀ j, Prime (x.1 j) := fun j => s.prime j.val (x.1 j) (Fintype.mem_piFinset.mp x.2 j)
  have hδ : primaryGenerator (selProduct Q x.1) ≠ 0 := supported_primaryGenerator_ne_zero _ hD
  have hδ3 : primaryGenerator (selProduct Q x.1) ^ 3 ≠ 0 := pow_ne_zero 3 hδ
  have hδmem : ∀ j, primaryGenerator (selProduct Q x.1) ^ 3 ∈ x.1 j := by
    intro j
    have h1 : primaryGenerator (selProduct Q x.1) ∈ selProduct Q x.1 := by
      have h := Ideal.mem_span_singleton_self (primaryGenerator (selProduct Q x.1))
      rwa [primary_span_supported _ hD] at h
    have h2 : selProduct Q x.1 ≤ x.1 j :=
      Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
    exact Ideal.pow_mem_of_mem _ (h2 h1) 3 (by norm_num)
  by_cases hs : SmallFree (sideProd σ x.1 0) (sideProd σ x.1 1)
  · apply le_of_eq
    unfold famEnergy famEnergyT
    congr 2
    funext I
    have hI : Supported I.val := (Finset.mem_filter.mp I.property).2
    rw [twistChar_rowWeight τ _ hδ3 t I hI]
    by_cases hdiv : ∃ j, x.1 j ∣ I.val
    · obtain ⟨j, hj⟩ := hdiv
      have h0 : rowWeight τ fixedBadMask 1 (primaryGenerator (selProduct Q x.1) ^ 3) t I = 0 := by
        rw [rowWeight_twist_eq, idealRowHom_zero_of_dvd _ (hu j) hj (hδmem j), mul_zero]
      rw [h0, mul_zero, mul_zero, mul_zero]
    · push Not at hdiv
      have hcop : IsCoprime (selProduct Q x.1) I.val :=
        IsCoprime.prod_left (fun j _ => coprime_of_prime_not_dvd (hu j) (hdiv j))
      congr 1
      unfold finiteColumnCoefficient
      apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨ham, hprod⟩ := Finset.mem_filter.mp ha
      unfold noColPart
      congr 1
      exact tc_mark_elim _ A₁ A₂ _ _ (selProduct Q x.1) Dc K R _ F a ham (sideProd_mul σ x.1)
        (by rw [hprod, sideProd_mul]; exact hcop.symm) (by rw [sideProd_mul]; exact hsq) hDA hs
        hA₁ hA₂
  · have hc : ∀ I : supportedColumns (finiteColumns (collBox s Q σ x)),
        finiteColumnCoefficient (collBox s Q σ x)
          (noColPart (restBlock J Q)
            (CoupledFirst.tupleCoefficient (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1))
              (markedSourceModifier (A₁ * sideProd σ x.1 0) (A₂ * sideProd σ x.1 1) Dc K F)
              (R * selProduct Q x.1) (residualSeed Q L x.1))) I = 0 := by
      intro I
      unfold finiteColumnCoefficient
      apply Finset.sum_eq_zero
      intro a ha
      unfold noColPart
      rw [tc_mark_small _ A₁ A₂ _ _ Dc K _ _ F a (Finset.mem_filter.mp ha).1 (collH s Q σ x 0)
        (collH s Q σ x 1) hs hA₁ hA₂, zero_mul]
    have hz : famEnergy s J Q σ x A₁ A₂ Dc K R L F τ t T H = 0 := by
      unfold famEnergy
      simp only [hc, zero_mul]
      rw [gaussEnergy_zero_coeff, Complex.zero_re]
    rw [hz]
    exact ball_energy_nonneg _ _ _ _ H hH

/-! ### The transfer inside the families -/

/-- The residual energy of a collision family at the residual seed `L'` and the ray `ξ`: the
residual input of the family on `J \ Q`, the plain marks, the twisted character with the ray. -/
def famResidual (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (x : {u // u ∈ selBox s Q})
    (A₁ A₂ Dc K R L' : Ideal O) (F : Ideal O → ℂ) (τ : HeckeFamily.Character)
    (ξ : RayCharacter) (t T H' : ℝ) : ℝ :=
  (gaussEnergy Finset.univ
    (sourceGenerator (finiteColumns (Fintype.piFinset
      (residualInput (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1)) (restBlock J Q)).pools)))
    (sourceGenerator_supported (finiteColumns (Fintype.piFinset
      (residualInput (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1)) (restBlock J Q)).pools)))
    (fun I : supportedColumns (finiteColumns (Fintype.piFinset
        (residualInput (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1))
          (restBlock J Q)).pools)) =>
      CoupledFirst.coefficient
          (residualInput (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1)) (restBlock J Q))
          (markedSourceModifier A₁ A₂ Dc K F) R L' I *
        ((Real.sqrt (T / ∏ j ∈ restBlock J Q,
            (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1)).P j) : ℂ)⁻¹ *
          rowWeight (childCharacter (twistChar τ (primaryGenerator (selProduct Q x.1) ^ 3)) ξ)
            fixedBadMask 1 1 t I))
    ballProfile H').re

/-- **The transfer inside one collision family.** -/
theorem fam_transfer (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {κ : Type u} [Fintype κ] [DecidableEq κ], Fintype.card κ ≤ N →
    ∀ (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (x : {u // u ∈ selBox s Q})
      (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T H H' : ℝ),
      0 < H → 0 < H' → Squarefree L → (∀ j ∈ J, 0 ≤ s.hi j) →
      Supported (selProduct Q x.1) → selWeight s Q K R x.1 ≠ 0 →
      A₁ ≠ 0 → A₂ ≠ 0 → A₁ * A₂ ∣ R →
      (∀ v ∈ Fintype.piFinset (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1)).pools,
        F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart (restBlock J Q) v))) →
      2 * H * (∏ j ∈ restBlock J Q, s.hi j.val * s.P j.val) ^ 4 ≤ H' →
      ∃ seeds : Finset (Ideal O), (∀ L' ∈ seeds, L' ∣ L) ∧
        famEnergy s J Q σ x A₁ A₂ Dc K R L F τ t T H ≤
          C * (∏ j ∈ restBlock J Q, s.hi j.val * s.M j.val ^ 2) * (max 1 H') ^ ε *
            ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
              famResidual s J Q σ x A₁ A₂ Dc K R L' F τ ξ t T H' := by
  obtain ⟨C, hC, htr⟩ := collet_main_selected_transfer_supplier_ball_nocol.{u} ε hε N
  refine ⟨C, hC, ?_⟩
  intro κ _ _ hcard s J Q σ x A₁ A₂ Dc K R L F τ t T H H' hH hH' hLsq hhi hD hw hA₁ hA₂ hAR hF hrad
  have hcard' : Fintype.card {i // i ∉ Q} ≤ N := (Fintype.card_subtype_le _).trans hcard
  have hinj := sel_injective_of_weight s Q K R x.1 x.2 hw
  have hLdvd : residualSeed Q L x.1 ∣ L := residualSeed_dvd s Q L x.1 x.2 hinj
  have hLx : Squarefree (residualSeed Q L x.1) := Squarefree.squarefree_of_dvd hLdvd hLsq
  have hhi' : ∀ j ∈ restBlock J Q,
      0 ≤ (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1)).hi j :=
    fun j hj => hhi j.val (Finset.mem_subtype.mp hj)
  obtain ⟨seeds, hseeds, hb⟩ := htr hcard' (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1))
    (restBlock J Q) A₁ A₂ Dc K R (residualSeed Q L x.1) F
    (twistChar τ (primaryGenerator (selProduct Q x.1) ^ 3)) t T H H' hH hH' hrad hhi' hLx hF
  refine ⟨seeds, fun L' hL' => (hseeds L' hL').trans hLdvd, ?_⟩
  exact (famEnergy_elim s J Q σ x A₁ A₂ Dc K R L F τ t T H hH hD hw hA₁ hA₂ hAR).trans hb

/-- **The collision part, transferred inside its families.** -/
theorem collision_transfer (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {κ : Type u} [Fintype κ] [DecidableEq κ], Fintype.card κ ≤ N →
    ∀ (s : Input κ) (J : Finset κ) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T H : ℝ)
      (H' : (p : Σ Q : Finset κ, Q → Fin 2) → {u // u ∈ selBox s p.1} → ℝ),
      0 < H → Squarefree L → (∀ j ∈ J, 0 ≤ s.hi j) → A₁ ≠ 0 → A₂ ≠ 0 → A₁ * A₂ ∣ R →
      (∀ (Q : Finset κ) (u : Q → Ideal O), u ∈ selBox s Q → ∀ n : Ideal O,
        F (Dc * (selProduct Q u ^ 2 * n)) = F (Dc * n)) →
      (∀ p ∈ patterns J, ∀ x : {u // u ∈ selBox s p.1},
        ∀ v ∈ Fintype.piFinset
          (collInput s p.1 p.2 x.1 (collH s p.1 p.2 x 0) (collH s p.1 p.2 x 1)).pools,
          F (Dc * finiteTupleProduct v) =
            F (Dc * finiteTupleProduct (restPart (restBlock J p.1) v))) →
      (∀ p ∈ patterns J, ∀ x : {u // u ∈ selBox s p.1}, 0 < H' p x ∧
        2 * (2 * H / (Ideal.absNorm (selProduct p.1 x.1) : ℝ)) *
          (∏ j ∈ restBlock J p.1, s.hi j.val * s.P j.val) ^ 4 ≤ H' p x) →
      ∃ seeds : (p : Σ Q : Finset κ, Q → Fin 2) → {u // u ∈ selBox s p.1} → Finset (Ideal O),
        (∀ p x, ∀ L' ∈ seeds p x, L' ∣ L) ∧
        (gaussEnergy Finset.univ (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
            (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
            (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
              finiteColumnCoefficient (Fintype.piFinset s.pools)
                (colPart J (CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L)) I *
                ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H).re ≤
          C * (max 1 (2 * H)) ^ ε *
            ∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach,
              if Supported (selProduct p.1 x.1) then
                ‖selWeight s p.1 K R x.1‖ ^ 2 * (Ideal.absNorm (selProduct p.1 x.1) : ℝ) *
                  ((∏ j ∈ restBlock J p.1, s.hi j.val * s.M j.val ^ 2) * (max 1 (H' p x)) ^ ε *
                    ∑ ξ : RayCharacter, ∑ L' ∈ seeds p x,
                      famResidual s J p.1 p.2 x A₁ A₂ Dc K R L' F τ ξ t T (H' p x))
              else 0 := by
  obtain ⟨C₁, hC₁, hcoll⟩ := collision_energy_families.{u} ε hε N
  obtain ⟨C₂, hC₂, hfam⟩ := fam_transfer.{u} ε hε N
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  intro κ _ _ hcard s J A₁ A₂ Dc K R L F τ t T H H' hH hLsq hhi hA₁ hA₂ hAR hF2 hFf hH'
  have hex : ∀ (p : Σ Q : Finset κ, Q → Fin 2) (x : {u // u ∈ selBox s p.1}),
      ∃ S : Finset (Ideal O), (∀ L' ∈ S, L' ∣ L) ∧
        (p ∈ patterns J → Supported (selProduct p.1 x.1) → selWeight s p.1 K R x.1 ≠ 0 →
          famEnergy s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T
              (2 * H / (Ideal.absNorm (selProduct p.1 x.1) : ℝ)) ≤
            C₂ * (∏ j ∈ restBlock J p.1, s.hi j.val * s.M j.val ^ 2) * (max 1 (H' p x)) ^ ε *
              ∑ ξ : RayCharacter, ∑ L' ∈ S,
                famResidual s J p.1 p.2 x A₁ A₂ Dc K R L' F τ ξ t T (H' p x)) := by
    intro p x
    by_cases hp : p ∈ patterns J ∧ Supported (selProduct p.1 x.1) ∧ selWeight s p.1 K R x.1 ≠ 0
    · obtain ⟨hpJ, hD, hw⟩ := hp
      have hD0 : selProduct p.1 x.1 ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ =>
        (s.prime j.val (x.1 j) (Fintype.mem_piFinset.mp x.2 j)).ne_zero)
      have hN : (0 : ℝ) < Ideal.absNorm (selProduct p.1 x.1) := by
        exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
      obtain ⟨S, hS, hb⟩ := hfam hcard s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T _ (H' p x)
        (by positivity) (hH' p hpJ x).1 hLsq hhi hD hw hA₁ hA₂ hAR (hFf p hpJ x) (hH' p hpJ x).2
      exact ⟨S, hS, fun _ _ _ => hb⟩
    · refine ⟨∅, fun L' h => absurd h (Finset.notMem_empty L'), ?_⟩
      intro hpJ hD hw
      exact absurd ⟨hpJ, hD, hw⟩ hp
  choose seeds hseeds hbound using hex
  refine ⟨seeds, hseeds, ?_⟩
  refine (hcoll hcard s J A₁ A₂ Dc K R L F τ t T H hH hLsq hF2).trans ?_
  have hM : 0 ≤ (max 1 (2 * H)) ^ ε := Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  have hterm : ∀ p ∈ patterns J, ∀ x ∈ (selBox s p.1).attach,
      (if Supported (selProduct p.1 x.1) then
          ‖selWeight s p.1 K R x.1‖ ^ 2 * (Ideal.absNorm (selProduct p.1 x.1) : ℝ) *
            famEnergy s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T
              (2 * H / (Ideal.absNorm (selProduct p.1 x.1) : ℝ))
        else 0) ≤
      C₂ * (if Supported (selProduct p.1 x.1) then
          ‖selWeight s p.1 K R x.1‖ ^ 2 * (Ideal.absNorm (selProduct p.1 x.1) : ℝ) *
            ((∏ j ∈ restBlock J p.1, s.hi j.val * s.M j.val ^ 2) * (max 1 (H' p x)) ^ ε *
              ∑ ξ : RayCharacter, ∑ L' ∈ seeds p x,
                famResidual s J p.1 p.2 x A₁ A₂ Dc K R L' F τ ξ t T (H' p x))
        else 0) := by
    intro p hp x _
    by_cases hD : Supported (selProduct p.1 x.1)
    · simp only [hD, ↓reduceIte]
      by_cases hw : selWeight s p.1 K R x.1 = 0
      · simp only [hw, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          zero_mul, mul_zero, le_refl]
      · have hb := hbound p x hp hD hw
        have h0 : 0 ≤ ‖selWeight s p.1 K R x.1‖ ^ 2 * (Ideal.absNorm (selProduct p.1 x.1) : ℝ) :=
          by positivity
        calc ‖selWeight s p.1 K R x.1‖ ^ 2 * (Ideal.absNorm (selProduct p.1 x.1) : ℝ) *
              famEnergy s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T
                (2 * H / (Ideal.absNorm (selProduct p.1 x.1) : ℝ))
            ≤ ‖selWeight s p.1 K R x.1‖ ^ 2 * (Ideal.absNorm (selProduct p.1 x.1) : ℝ) *
              (C₂ * (∏ j ∈ restBlock J p.1, s.hi j.val * s.M j.val ^ 2) * (max 1 (H' p x)) ^ ε *
                ∑ ξ : RayCharacter, ∑ L' ∈ seeds p x,
                  famResidual s J p.1 p.2 x A₁ A₂ Dc K R L' F τ ξ t T (H' p x)) :=
              mul_le_mul_of_nonneg_left hb h0
          _ = _ := by ring
    · simp only [hD, ↓reduceIte, mul_zero, le_refl]
  calc C₁ * (max 1 (2 * H)) ^ ε * ∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach,
        (if Supported (selProduct p.1 x.1) then
          ‖selWeight s p.1 K R x.1‖ ^ 2 * (Ideal.absNorm (selProduct p.1 x.1) : ℝ) *
            famEnergy s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T
              (2 * H / (Ideal.absNorm (selProduct p.1 x.1) : ℝ))
        else 0)
      ≤ C₁ * (max 1 (2 * H)) ^ ε * ∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach,
        C₂ * (if Supported (selProduct p.1 x.1) then
          ‖selWeight s p.1 K R x.1‖ ^ 2 * (Ideal.absNorm (selProduct p.1 x.1) : ℝ) *
            ((∏ j ∈ restBlock J p.1, s.hi j.val * s.M j.val ^ 2) * (max 1 (H' p x)) ^ ε *
              ∑ ξ : RayCharacter, ∑ L' ∈ seeds p x,
                famResidual s J p.1 p.2 x A₁ A₂ Dc K R L' F τ ξ t T (H' p x))
        else 0) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun x hx => hterm p hp x hx))
    _ = _ := by
        simp only [← Finset.mul_sum]
        ring

end
end QRH.MixedStep.Collision

#print axioms QRH.MixedStep.Collision.collision_transfer
#print axioms QRH.MixedStep.Collision.fam_transfer
#print axioms QRH.MixedStep.Collision.famEnergy_elim
#print axioms QRH.MixedStep.Collision.tc_mark_elim
#print axioms QRH.MixedStep.Collision.tc_mark_small
