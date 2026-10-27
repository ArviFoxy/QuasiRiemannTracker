/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform absolute mass of actual extracted ideal pairs and frozen marked labels.
The kernel at a supplying prime is exactly the marked correction. Arbitrary
finite cutoffs and restrictions are allowed without changing the constant.
Modified by Sil (2026-10-26): central forward sigma 3/2 (FP 5/2); the reflected critical mass ForwardCriticalMass has sigma = 1, paid by the PrimeHarmonic enclosure N(P) <= X (selected_subpower_critical); statements of the three subpower theorems unchanged.
-/
import Submissions.density_split_third_20261026.CubeFree.FP.KernelSelectedLocal
import Submissions.density_split_third_20261026.CubeFree.KernelForwardMass3

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.FP.KernelActualMass
open Candidate.FourthPower
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelAllocationIdentity KernelLabelledSlots KernelSelectedMass KernelSelectedLocal
open KernelForwardMass SieveDescent
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

def frozenMass (S : Finset PrimeIdeal) (A B : LocalSeries) (s t v : ℝ)
    (slot : α → S) (d : Id × Id) : ℝ :=
  idealWeight S (fun P => if marked S slot P then B else A) s t d *
    ∏ i : α, normWeight v (slot i).val.val

theorem frozenMass_nonneg (S : Finset PrimeIdeal) (A B : LocalSeries) (s t v : ℝ)
    (slot : α → S) (d : Id × Id) : 0 ≤ frozenMass S A B s t v slot d := by
  apply mul_nonneg (idealWeight_nonneg _ _ _ _ _)
  exact Finset.prod_nonneg (fun _ _ => by unfold normWeight; positivity)

/-- The fixed-label estimate uses the same kernelOn as the exact row identity,
not a separately declared configuration with an assumed matching weight. -/
theorem fixed_labels_bound (S : Finset PrimeIdeal) (hS : ∀ P ∈ S, Supported P.val)
    (A B : LocalSeries) (s t u v σ C K : ℝ)
    (hσ : 1 < σ) (hC : 0 ≤ C) (hK : 0 ≤ K) (huv : u+v=1)
    (hA : ∀ P ∈ S, ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight A s t P ij) ≤ 1+C*(Ideal.absNorm P.val : ℝ)^(-σ))
    (hB : ∀ P ∈ S, ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight B s t P ij) ≤ K*(Ideal.absNorm P.val : ℝ)^(-u))
    (slot : α → S) (hinj : Function.Injective slot) (D : Finset (Id × Id))
    (hd : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs : ∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) :
    (∑ d ∈ D, frozenMass S A B s t v slot d) ≤
      Real.exp (C*rootMass σ)*∏ i : α, K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹ := by
  have he (P : S) : K*(Ideal.absNorm P.val.val : ℝ)^(-u)*normWeight v P.val.val =
      K*(Ideal.absNorm P.val.val : ℝ)⁻¹ := by
    have hp : (0 : ℝ) < Ideal.absNorm P.val.val :=
      zero_lt_one.trans_le (ideal_norm_one_le P.val.property.ne_zero)
    unfold normWeight
    rw [mul_assoc,← Real.rpow_add hp,show -u + -v = -1 by linarith [huv],Real.rpow_neg_one]
  have hh := selected_ideal_mass S slot hinj A B s t
    (fun P => 1+C*(Ideal.absNorm P.val.val : ℝ)^(-σ))
    (fun P => K*(Ideal.absNorm P.val.val : ℝ)^(-u))
    (fun P => normWeight v P.val.val)
    (fun P => le_add_of_nonneg_right (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    (fun P => by positivity) (fun P => by unfold normWeight; positivity)
    (fun P T => hA P.val P.property T) (fun P T => hB P.val P.property T) D hd hs
  simp_rw [he] at hh
  have ho : (∏ P : S, (1+C*(Ideal.absNorm P.val.val : ℝ)^(-σ))) ≤ Real.exp (C*rootMass σ) := by
    have hx : (∏ P : S, (1+C*(Ideal.absNorm P.val.val : ℝ)^(-σ))) =
        ∏ P ∈ primeValues S, (1+C*(Ideal.absNorm P : ℝ)^(-σ)) := by
      unfold primeValues
      rw [Finset.prod_image (by intro P _ Q _ h; exact Subtype.val_injective h)]
      exact (Finset.prod_subtype (p := fun P => P ∈ S) S (by simp)
        (fun P : PrimeIdeal => 1+C*(Ideal.absNorm P.val : ℝ)^(-σ))).symm
    rw [hx]
    apply finite_euler_mass σ C hσ hC (primeValues S)
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    exact hS Q hQ
  unfold frozenMass
  rw [← Finset.sum_mul]
  exact hh.trans (mul_le_mul_of_nonneg_right ho (Finset.prod_nonneg (fun i _ => by positivity)))

/-- The same C works for every injective marked pool, and every residual
ideal cutoff that may depend on the frozen assignment. -/
theorem selected_subpower (A B : LocalSeries) (s t u v σ C K ε : ℝ)
    (hσ : 1 < σ) (hC : 0 ≤ C) (hK : 0 ≤ K) (huv : u+v=1) (hε : 0 < ε)
    (hA : ∀ P : PrimeIdeal, Supported P.val → ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight A s t P ij) ≤ 1+C*(Ideal.absNorm P.val : ℝ)^(-σ))
    (hB : ∀ P : PrimeIdeal, Supported P.val → ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight B s t P ij) ≤ K*(Ideal.absNorm P.val : ℝ)^(-u)) :
    ∃ M : ℝ, 0 < M ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot, frozenMass S A B s t v slot d) ≤ M*X^ε := by
  obtain ⟨M,hM,hbound⟩ := prime_assignments_subpower (α := α) K ε hK hε
  refine ⟨Real.exp (C*rootMass σ)*M,mul_pos (Real.exp_pos _) hM,?_⟩
  intro X hX S hS F hinj D hd hs
  calc
    _ ≤ ∑ slot ∈ F, Real.exp (C*rootMass σ)*∏ i : α,
        K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹ := Finset.sum_le_sum (fun slot hslot =>
      fixed_labels_bound S (fun P hP => (hS P hP).1) A B s t u v σ C K hσ hC hK huv
        (fun P hP T => hA P (hS P hP).1 T) (fun P hP T => hB P (hS P hP).1 T)
        slot (hinj slot hslot) (D slot) (hd slot hslot) (hs slot hslot))
    _ = Real.exp (C*rootMass σ)*(∑ slot ∈ F, ∏ i : α,
        K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (C*rootMass σ)*(∑ slot : α → S, ∏ i : α,
        K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
        (fun slot _ _ => Finset.prod_nonneg (fun i _ => by positivity))) (Real.exp_pos _).le
    _ ≤ Real.exp (C*rootMass σ)*(M*X^ε) :=
      mul_le_mul_of_nonneg_left (hbound X hX S hS) (Real.exp_pos _).le
    _ = _ := by ring

/-- Generic form of `fixed_labels_bound` keeping the ordinary truncated Euler product
(no condition on σ): used at the cube-free critical exponent σ = 1. -/
theorem fixed_labels_product (S : Finset PrimeIdeal)
    (A B : LocalSeries) (s t u v σ C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) (huv : u+v=1)
    (hA : ∀ P ∈ S, ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight A s t P ij) ≤ 1+C*(Ideal.absNorm P.val : ℝ)^(-σ))
    (hB : ∀ P ∈ S, ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight B s t P ij) ≤ K*(Ideal.absNorm P.val : ℝ)^(-u))
    (slot : α → S) (hinj : Function.Injective slot) (D : Finset (Id × Id))
    (hd : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs : ∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) :
    (∑ d ∈ D, frozenMass S A B s t v slot d) ≤
      (∏ P : S, (1+C*(Ideal.absNorm P.val.val : ℝ)^(-σ)))*
        ∏ i : α, K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹ := by
  have he (P : S) : K*(Ideal.absNorm P.val.val : ℝ)^(-u)*normWeight v P.val.val =
      K*(Ideal.absNorm P.val.val : ℝ)⁻¹ := by
    have hp : (0 : ℝ) < Ideal.absNorm P.val.val :=
      zero_lt_one.trans_le (ideal_norm_one_le P.val.property.ne_zero)
    unfold normWeight
    rw [mul_assoc,← Real.rpow_add hp,show -u + -v = -1 by linarith [huv],Real.rpow_neg_one]
  have hh := selected_ideal_mass S slot hinj A B s t
    (fun P => 1+C*(Ideal.absNorm P.val.val : ℝ)^(-σ))
    (fun P => K*(Ideal.absNorm P.val.val : ℝ)^(-u))
    (fun P => normWeight v P.val.val)
    (fun P => le_add_of_nonneg_right (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    (fun P => by positivity) (fun P => by unfold normWeight; positivity)
    (fun P T => hA P.val P.property T) (fun P T => hB P.val P.property T) D hd hs
  simp_rw [he] at hh
  unfold frozenMass
  rw [← Finset.sum_mul]
  exact hh

/-- Cube-free critical ordinary product (σ = 1): over an enclosed prime pool `N(P) ≤ X`
it is `≤ K₀·X^δ` (Analysis.PrimeHarmonic); FP used `finite_euler_mass`, which needs σ > 1. -/
theorem critical_ordinary_product (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, (Ideal.absNorm P.val : ℝ) ≤ X) →
      (∏ P : S, (1+C*(Ideal.absNorm P.val.val : ℝ)^(-(1 : ℝ)))) ≤ K₀*X^δ := by
  obtain ⟨X0,hX0,h⟩ := PrimeHarmonic.euler_product_subpower C 0 δ hC hδ
  have hX00 : 0 < X0 := by linarith
  refine ⟨X0^δ,Real.rpow_pos_of_pos hX00 _,?_⟩
  intro X hX S hS
  have hx : (∏ P : S, (1+C*(Ideal.absNorm P.val.val : ℝ)^(-(1 : ℝ)))) =
      ∏ P ∈ primeValues S, (1+C*(Ideal.absNorm P : ℝ)^(-(1 : ℝ))) := by
    unfold primeValues
    rw [Finset.prod_image (by intro P _ Q _ h; exact Subtype.val_injective h)]
    exact (Finset.prod_subtype (p := fun P => P ∈ S) S (by simp)
      (fun P : PrimeIdeal => 1+C*(Ideal.absNorm P.val : ℝ)^(-(1 : ℝ)))).symm
  rw [hx]
  have hb := h (max X X0) (le_max_right _ _) (primeValues S)
    (fun P hP => by
      obtain ⟨Q,_,rfl⟩ := Finset.mem_image.mp hP
      exact KernelForwardMass3.prime_data Q.property)
    (fun P hP => by
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
      exact (hS Q hQ).trans (le_max_left _ _))
    (fun P => 1+C*(Ideal.absNorm P : ℝ)^(-(1 : ℝ))) (fun _ => 0)
    (fun P _ => by positivity)
    (fun P _ => by rw [Real.rpow_neg_one,div_eq_mul_inv,add_zero])
    (by simp)
  have hmax : max X X0 ≤ X0*X := max_le (by nlinarith) (by nlinarith)
  calc
    _ ≤ (max X X0)^δ := hb
    _ ≤ (X0*X)^δ := Real.rpow_le_rpow (le_trans (by linarith) (le_max_left X X0)) hmax hδ.le
    _ = X0^δ*X^δ := Real.mul_rpow hX00.le (by linarith)

/-- `selected_subpower` at the critical ordinary exponent σ = 1. The conclusion is the same:
the enclosure `N(P) ≤ X` already present in it pays the truncated Euler product. -/
theorem selected_subpower_critical (A B : LocalSeries) (s t u v C K ε : ℝ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (huv : u+v=1) (hε : 0 < ε)
    (hA : ∀ P : PrimeIdeal, Supported P.val → ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight A s t P ij) ≤ 1+C*(Ideal.absNorm P.val : ℝ)^(-(1 : ℝ)))
    (hB : ∀ P : PrimeIdeal, Supported P.val → ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight B s t P ij) ≤ K*(Ideal.absNorm P.val : ℝ)^(-u)) :
    ∃ M : ℝ, 0 < M ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot, frozenMass S A B s t v slot d) ≤ M*X^ε := by
  obtain ⟨M,hM,hbound⟩ := prime_assignments_subpower (α := α) K (ε/2) hK (half_pos hε)
  obtain ⟨K₀,hK₀,hord⟩ := critical_ordinary_product C (ε/2) hC (half_pos hε)
  refine ⟨K₀*M,mul_pos hK₀ hM,?_⟩
  intro X hX S hS F hinj D hd hs
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hO := hord X hX S (fun P hP => (hS P hP).2)
  have hpow : X^(ε/2)*X^(ε/2) = X^ε := by rw [← Real.rpow_add hX0]; ring_nf
  calc
    _ ≤ ∑ slot ∈ F, (∏ P : S, (1+C*(Ideal.absNorm P.val.val : ℝ)^(-(1 : ℝ))))*∏ i : α,
        K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹ := Finset.sum_le_sum (fun slot hslot =>
      fixed_labels_product S A B s t u v 1 C K hC hK huv
        (fun P hP T => hA P (hS P hP).1 T) (fun P hP T => hB P (hS P hP).1 T)
        slot (hinj slot hslot) (D slot) (hd slot hslot) (hs slot hslot))
    _ = (∏ P : S, (1+C*(Ideal.absNorm P.val.val : ℝ)^(-(1 : ℝ))))*(∑ slot ∈ F, ∏ i : α,
        K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹) := (Finset.mul_sum _ _ _).symm
    _ ≤ (K₀*X^(ε/2))*(∑ slot : α → S, ∏ i : α, K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹) :=
      mul_le_mul hO (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
        (fun slot _ _ => Finset.prod_nonneg (fun i _ => by positivity)))
        (Finset.sum_nonneg (fun slot _ => Finset.prod_nonneg (fun i _ => by positivity))) (by positivity)
    _ ≤ (K₀*X^(ε/2))*(M*X^(ε/2)) := mul_le_mul_of_nonneg_left (hbound X hX S hS) (by positivity)
    _ = K₀*M*X^ε := by rw [← hpow]; ring

def ForwardCentralMass (S : Finset PrimeIdeal) (slot : α → S) (d : Id × Id) : ℝ :=
  frozenMass S kernelSeries (LocalKernels.base formalX formalY-kernelSeries) (1/2) (1/2) (1/2) slot d

def ForwardCriticalMass (S : Finset PrimeIdeal) (slot : α → S) (d : Id × Id) : ℝ :=
  frozenMass S kernelSeries (LocalKernels.base formalX formalY-kernelSeries) (2/3) (1/3) (2/3) slot d

def InverseCentralMass (S : Finset PrimeIdeal) (slot : α → S) (d : Id × Id) : ℝ :=
  frozenMass S reciprocalSeries KernelInverseMarkedMass.markedSeries (1/2) (1/2) (1/2) slot d

/-- The complete actual central forward mass, including all frozen labels. -/
theorem forward_central_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot, ForwardCentralMass S slot d) ≤ M*X^ε := by
  apply selected_subpower kernelSeries (LocalKernels.base formalX formalY-kernelSeries)
    (1/2) (1/2) (1/2) (1/2) (3/2) 7 14 ε (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hε
  · intro P _ T
    convert ordinary_local P (1/2) (1/2) (1/2) (by norm_num) le_rfl le_rfl T using 1; norm_num
  · intro P _ T
    exact marked_local P (1/2) (1/2) (1/2) (by norm_num) le_rfl le_rfl T

/-- The reflected critical ratio is paid with actual exponents 2/3,1/3,2/3.
Cube-free: the ordinary exponent is 3·(1/3) = 1 (critical); `selected_subpower_critical`. -/
theorem forward_critical_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot, ForwardCriticalMass S slot d) ≤ M*X^ε := by
  apply selected_subpower_critical kernelSeries (LocalKernels.base formalX formalY-kernelSeries)
    (2/3) (1/3) (1/3) (2/3) 7 14 ε (by norm_num) (by norm_num) (by norm_num) hε
  · intro P _ T
    convert ordinary_local P (2/3) (1/3) (1/3) (by norm_num) (by norm_num) le_rfl T using 1; norm_num
  · intro P _ T
    exact marked_local P (2/3) (1/3) (1/3) (by norm_num) (by norm_num) le_rfl T

/-- The infinite inverse local series is fully included, with finite arbitrary
ideal cutoffs. Its supplying primes retain the correct inverse marked series. -/
theorem inverse_central_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot, InverseCentralMass S slot d) ≤ M*X^ε := by
  exact selected_subpower reciprocalSeries KernelInverseMarkedMass.markedSeries
    (1/2) (1/2) (1/2) (1/2) (3/2) 400 10206 ε (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hε inverse_ordinary_local inverse_marked_local

end
end QRH.DensitySplitThird.CubeFree.FP.KernelActualMass
