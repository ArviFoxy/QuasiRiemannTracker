import Mathlib

/-!
# The dispersion inequality for the prime-pool face (research file, D1)

For row weights `b z` (in D1, `b z = Φ(z)|A(z)|²`, a plain fourth-moment density) and a pool
`Q z = Σ_P a_P ψ_P(z)` with unimodular characters `ψ_P`, expanding `|Q|²` gives the diagonal `‖a‖²·Σ b` plus
the twisted moments `T(P, P') = Σ_z b z ψ_P(z) conj ψ_{P'}(z)`, `P ≠ P'`. If the twists obey a large sieve
`Σ_{P ≠ P'} |Σ_z c z ψ_P conj ψ_{P'}|² ≤ Δ Σ_z |c z|²` (Huxley's large sieve over `Q(ω)` gives `Δ ≪ Z + P₀⁴`
for `ψ_P = (·/P)₆`, since distinct ordered pairs give distinct primitive characters), then (`dispersion`)
  `Σ_z b z |Q z|² ≤ ‖a‖² (Σ_z b z + √(Δ Σ_z b z²))`.
In D1 the last term is the plain **eighth** moment; with Lindelöf on average for it the face is diagonal.
-/

namespace QRH.ArviPrimeFace

open Finset
open scoped ComplexConjugate

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

omit [DecidableEq κ] in
/-- The expansion of the weighted second moment of the pool into twisted moments. -/
theorem pool_expand (S : Finset κ) (a : κ → ℂ) (ψ : κ → ι → ℂ) (b : ι → ℝ) :
    ((∑ z, b z * ‖∑ P ∈ S, a P * ψ P z‖ ^ 2 : ℝ) : ℂ) =
      ∑ P ∈ S, ∑ P' ∈ S, a P * conj (a P') * ∑ z, (b z : ℂ) * (ψ P z * conj (ψ P' z)) := by
  push_cast
  have h1 : ∀ z, ((‖∑ P ∈ S, a P * ψ P z‖ : ℝ) : ℂ) ^ 2 =
      (∑ P ∈ S, a P * ψ P z) * conj (∑ P' ∈ S, a P' * ψ P' z) := fun z => (Complex.mul_conj' _).symm
  simp_rw [h1, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P' _ => Finset.sum_congr rfl (fun z _ => ?_))
  ring

/-- **Dispersion inequality.** -/
theorem dispersion (S : Finset κ) (a : κ → ℂ) (ψ : κ → ι → ℂ) (hψ : ∀ P z, ‖ψ P z‖ = 1)
    (b : ι → ℝ) {Δ : ℝ}
    (hLS : ∀ c : ι → ℂ, ∑ P ∈ S, ∑ P' ∈ S.erase P, ‖∑ z, c z * (ψ P z * conj (ψ P' z))‖ ^ 2 ≤
      Δ * ∑ z, ‖c z‖ ^ 2) :
    ∑ z, b z * ‖∑ P ∈ S, a P * ψ P z‖ ^ 2 ≤
      (∑ P ∈ S, ‖a P‖ ^ 2) * (∑ z, b z + Real.sqrt (Δ * ∑ z, b z ^ 2)) := by
  set T : κ → κ → ℂ := fun P P' => ∑ z, (b z : ℂ) * (ψ P z * conj (ψ P' z)) with hT
  set A2 : ℝ := ∑ P ∈ S, ‖a P‖ ^ 2 with hA2
  -- diagonal twisted moments
  have hdiag : ∀ P, T P P = ((∑ z, b z : ℝ) : ℂ) := by
    intro P
    simp only [hT]
    push_cast
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Complex.mul_conj', hψ P z]; simp
  -- split the double sum
  set OD : ℂ := ∑ P ∈ S, ∑ P' ∈ S.erase P, a P * conj (a P') * T P P' with hOD
  have hsplit : ((∑ z, b z * ‖∑ P ∈ S, a P * ψ P z‖ ^ 2 : ℝ) : ℂ) =
      ((A2 * ∑ z, b z : ℝ) : ℂ) + OD := by
    rw [pool_expand]
    have : ∀ P ∈ S, ∑ P' ∈ S, a P * conj (a P') * T P P' =
        a P * conj (a P) * T P P + ∑ P' ∈ S.erase P, a P * conj (a P') * T P P' :=
      fun P hP => (Finset.add_sum_erase S (fun P' => a P * conj (a P') * T P P') hP).symm
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    congr 1
    rw [hA2]; push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [hdiag P, Complex.mul_conj']; push_cast; ring
  -- bound the off-diagonal
  have hOD_le : ‖OD‖ ≤ A2 * Real.sqrt (Δ * ∑ z, b z ^ 2) := by
    have h1 : ‖OD‖ ≤ ∑ P ∈ S, ∑ P' ∈ S.erase P, (‖a P‖ * ‖a P'‖) * ‖T P P'‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun P _ => (norm_sum_le _ _).trans ?_))
      refine Finset.sum_le_sum (fun P' _ => le_of_eq ?_)
      rw [norm_mul, norm_mul, Complex.norm_conj]
    set Sg := S.sigma (fun P => S.erase P) with hSg
    have e1 : ∑ x ∈ Sg, (‖a x.1‖ * ‖a x.2‖) * ‖T x.1 x.2‖ =
        ∑ P ∈ S, ∑ P' ∈ S.erase P, ‖a P‖ * ‖a P'‖ * ‖T P P'‖ :=
      (Finset.sum_sigma' S (fun P => S.erase P) (fun P P' => ‖a P‖ * ‖a P'‖ * ‖T P P'‖)).symm
    have e2 : ∑ x ∈ Sg, (‖a x.1‖ * ‖a x.2‖) ^ 2 = ∑ P ∈ S, ∑ P' ∈ S.erase P, (‖a P‖ * ‖a P'‖) ^ 2 :=
      (Finset.sum_sigma' S (fun P => S.erase P) (fun P P' => (‖a P‖ * ‖a P'‖) ^ 2)).symm
    have e3 : ∑ x ∈ Sg, ‖T x.1 x.2‖ ^ 2 = ∑ P ∈ S, ∑ P' ∈ S.erase P, ‖T P P'‖ ^ 2 :=
      (Finset.sum_sigma' S (fun P => S.erase P) (fun P P' => ‖T P P'‖ ^ 2)).symm
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt Sg (fun x => ‖a x.1‖ * ‖a x.2‖) (fun x => ‖T x.1 x.2‖)
    rw [e1, e2, e3] at h2
    have hA0 : 0 ≤ A2 := Finset.sum_nonneg (fun P _ => sq_nonneg _)
    have ha : Real.sqrt (∑ P ∈ S, ∑ P' ∈ S.erase P, (‖a P‖ * ‖a P'‖) ^ 2) ≤ A2 := by
      have hle : ∑ P ∈ S, ∑ P' ∈ S.erase P, (‖a P‖ * ‖a P'‖) ^ 2 ≤ A2 ^ 2 := by
        calc ∑ P ∈ S, ∑ P' ∈ S.erase P, (‖a P‖ * ‖a P'‖) ^ 2
            ≤ ∑ P ∈ S, ∑ P' ∈ S, (‖a P‖ * ‖a P'‖) ^ 2 :=
              Finset.sum_le_sum (fun P _ => Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.erase_subset P S) (fun _ _ _ => sq_nonneg _))
          _ = A2 ^ 2 := by
              rw [hA2, sq, Finset.sum_mul]
              refine Finset.sum_congr rfl (fun P _ => ?_)
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun P' _ => by ring)
      calc Real.sqrt _ ≤ Real.sqrt (A2 ^ 2) := Real.sqrt_le_sqrt hle
        _ = A2 := Real.sqrt_sq hA0
    have hb : Real.sqrt (∑ P ∈ S, ∑ P' ∈ S.erase P, ‖T P P'‖ ^ 2) ≤ Real.sqrt (Δ * ∑ z, b z ^ 2) := by
      apply Real.sqrt_le_sqrt
      have := hLS (fun z => (b z : ℂ))
      simpa [hT, Complex.norm_real, Real.norm_eq_abs, sq_abs] using this
    calc ‖OD‖ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ A2 * Real.sqrt (Δ * ∑ z, b z ^ 2) :=
          mul_le_mul ha hb (Real.sqrt_nonneg _) hA0
  have hre := congrArg Complex.re hsplit
  rw [Complex.ofReal_re, Complex.add_re, Complex.ofReal_re] at hre
  rw [hre]
  have : OD.re ≤ ‖OD‖ := Complex.re_le_norm OD
  nlinarith [hOD_le, this]

end QRH.ArviPrimeFace
#print axioms QRH.ArviPrimeFace.dispersion
