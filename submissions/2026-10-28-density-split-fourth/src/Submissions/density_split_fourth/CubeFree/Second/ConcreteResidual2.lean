/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M (a), part 2: factorization of an original tuple at a selected/residual split. -/
import Submissions.density_split_fourth.CubeFree.Second.ConcreteResidual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiteralAllocation
open MixedCommonRestriction MixedCommonCoefficient MixedCommonAllocation MixedOriginalSecondZero
open MixedTupleRows MixedFirstLiveSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-! ### Distinct primes -/

theorem prime_dvd_prime_eq {P Q : Id} (hP : Prime P) (hQ : Prime Q) (h : P ∣ Q) : P = Q :=
  associated_iff_eq.mp ((hP.dvd_prime_iff_associated hQ).mp h)

theorem prime_coprime_iff_ne {P Q : Id} (hP : Prime P) (hQ : Prime Q) : IsCoprime P Q ↔ P ≠ Q := by
  rw [prime_coprime ⟨P, hP⟩ Q]
  constructor
  · intro h he; exact h (he ▸ dvd_refl P)
  · intro h hd; exact h (prime_dvd_prime_eq hP hQ hd)

theorem prod_prime_coprime_iff {κ μ : Type*} [Fintype κ] [Fintype μ] (y : κ → Id) (r : μ → Id)
    (hy : ∀ j, Prime (y j)) (hr : ∀ k, Prime (r k)) :
    IsCoprime (∏ j, y j) (∏ k, r k) ↔ ∀ j k, y j ≠ r k := by
  rw [IsCoprime.prod_left_iff]
  simp only [Finset.mem_univ, forall_const]
  apply forall_congr'
  intro j
  rw [IsCoprime.prod_right_iff]
  simp only [Finset.mem_univ, forall_const]
  exact forall_congr' (fun k => prime_coprime_iff_ne (hy j) (hr k))

/-! ### The restriction at a split -/

theorem slots_join_injective (J : Finset ι) (y : J → Id) (r : Tuple (Rest J)) :
    Function.Injective (fun i => joinTuple J y r (Sum.inl i)) ↔
      Function.Injective y ∧ Function.Injective (fun k => r (Sum.inl k)) ∧
        ∀ j k, y j ≠ r (Sum.inl k) := by
  constructor
  · intro h
    refine ⟨fun j₁ j₂ he => ?_, fun k₁ k₂ he => ?_, fun j k he => ?_⟩
    · apply Subtype.ext
      apply h
      simpa [joinTuple, j₁.property, j₂.property] using he
    · apply Subtype.ext
      apply h
      simpa [joinTuple, k₁.property, k₂.property] using he
    · have := h (show joinTuple J y r (Sum.inl j.val) = joinTuple J y r (Sum.inl k.val) by
        simpa [joinTuple, j.property, k.property] using he)
      exact k.property (this ▸ j.property)
  · rintro ⟨hy, hr, hd⟩ i₁ i₂ he
    by_cases h₁ : i₁ ∈ J <;> by_cases h₂ : i₂ ∈ J
    · simp only [joinTuple, Sum.elim_inl, dif_pos h₁, dif_pos h₂] at he
      exact congrArg Subtype.val (hy he)
    · simp only [joinTuple, Sum.elim_inl, dif_pos h₁, dif_neg h₂] at he
      exact (hd ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ he).elim
    · simp only [joinTuple, Sum.elim_inl, dif_neg h₁, dif_pos h₂] at he
      exact (hd ⟨i₂, h₂⟩ ⟨i₁, h₁⟩ he.symm).elim
    · simp only [joinTuple, Sum.elim_inl, dif_neg h₁, dif_neg h₂] at he
      exact congrArg Subtype.val (hr he)

theorem tupleRestriction_join (H : Id) (J : Finset ι) (y : J → Id) (r : Tuple (Rest J))
    (hy : ∀ j, Prime (y j)) (hr : ∀ k, Prime (r (Sum.inl k))) :
    tupleRestriction H (joinTuple J y r) ↔
      Function.Injective y ∧ IsCoprime (∏ j, y j) (finiteTupleProduct r) ∧ tupleRestriction H r := by
  have hD : IsCoprime (∏ j, y j) (finiteTupleProduct r) ↔
      (∀ j k, y j ≠ r (Sum.inl k)) ∧ IsCoprime (∏ j, y j) (r (Sum.inr 0) * r (Sum.inr 1)) := by
    rw [finiteTupleProduct_split, IsCoprime.mul_right_iff]
    exact and_congr_left' (prod_prime_coprime_iff y (fun k => r (Sum.inl k)) hy hr)
  unfold tupleRestriction restriction
  rw [slots_join_injective, slotProduct_join, hD]
  simp only [joinTuple, Sum.elim_inr]
  rw [show H * ((∏ j, y j) * slotProduct r) = (∏ j, y j) * (H * slotProduct r) by ring,
    IsCoprime.mul_left_iff]
  tauto

/-! ### The original tuple at a split -/

/-- The selected slot amplitude. -/
def selAmp (s : Source ι a b) (J : Finset ι) (y : J → Id) : ℂ :=
  ∏ j : J, s.ν j.val (y j) * s.Wslot j.val ((Ideal.absNorm (y j) : ℝ) / s.P j.val)

theorem slotAmp_join (s : Source ι a b) (J : Finset ι) (y : J → Id) (r : Tuple (Rest J)) :
    (∏ i, s.ν i (joinTuple J y r (Sum.inl i)) *
      s.Wslot i ((Ideal.absNorm (joinTuple J y r (Sum.inl i)) : ℝ) / s.P i)) =
    selAmp s J y * ∏ k : Rest J, s.ν k.val (r (Sum.inl k)) *
      s.Wslot k.val ((Ideal.absNorm (r (Sum.inl k)) : ℝ) / s.P k.val) := by
  rw [prod_split_subtype J]
  unfold selAmp
  congr 1
  · exact Finset.prod_congr rfl (fun j _ => by simp [joinTuple, j.property])
  · exact Finset.prod_congr rfl (fun j _ => by simp [joinTuple, j.property])

theorem originalTuple_join (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (ha : 0 < a)
    (u : Id) (y : J → Id) (r : Tuple (Rest J))
    (hy : ∀ j, Prime (y j)) (hr : ∀ k, Prime (r (Sum.inl k))) :
    originalTuple s ha u (joinTuple J y r) =
      ((if Function.Injective y then 1 else 0) * selAmp s J y *
        (if IsCoprime (∏ j, y j) s.R then 1 else 0)) *
      ((if IsCoprime (∏ j, y j) (finiteTupleProduct r) then 1 else 0) *
        (if u ∣ (∏ j, y j) * finiteTupleProduct r then 1 else 0)) *
      originalTuple (restSource s hB1 J) ha 1 r := by
  unfold originalTuple tupleWeight profileCoefficient
  rw [finiteTupleProduct_join, slotAmp_join]
  have hjr : joinTuple J y r (Sum.inr 0) = r (Sum.inr 0) := rfl
  have hjr' : joinTuple J y r (Sum.inr 1) = r (Sum.inr 1) := rfl
  rw [hjr, hjr']
  have hcop : IsCoprime ((∏ j, y j) * finiteTupleProduct r) s.R ↔
      IsCoprime (∏ j, y j) s.R ∧ IsCoprime (finiteTupleProduct r) s.R := IsCoprime.mul_left_iff
  have hres := tupleRestriction_join (punctureProduct s.S s.H) J y r hy hr
  change ((if tupleRestriction (punctureProduct s.S s.H) (joinTuple J y r) then (1:ℂ) else 0) * _) = _
  by_cases h1 : Function.Injective y <;>
    by_cases h2 : IsCoprime (∏ j, y j) (finiteTupleProduct r) <;>
    by_cases h3 : tupleRestriction (punctureProduct s.S s.H) r <;>
    by_cases h4 : IsCoprime (∏ j, y j) s.R <;>
    by_cases h5 : IsCoprime (finiteTupleProduct r) s.R <;>
    by_cases h6 : u ∣ (∏ j, y j) * finiteTupleProduct r <;>
    simp only [hres, hcop, h1, h2, h3, h4, h5, h6, and_self, and_true, true_and, and_false,
      false_and, ite_true, ite_false, one_dvd, mul_one, one_mul, mul_zero, zero_mul] <;>
    simp only [restSource, h3, h5, ite_true, ite_false, one_dvd, mul_one, one_mul, mul_zero,
      zero_mul] <;> ring

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
