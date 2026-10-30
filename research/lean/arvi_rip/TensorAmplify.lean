import Submissions.arvi_rip.WideFeatures

/-!
# Tensoring the rows with other data is amplification

Research file (QRH, RIP program (4)). A natural way to build a "different" dictionary is to pair
each row's atom `x_z ∈ ℂ^{d₁}` with other data of the row, `y_z ∈ ℂ^{d₂}`, through the product
atom `x_z ⊗ y_z`. The product Gram is the Hadamard product of the two Grams, so it can be far
more incoherent than the rows. Detection through the product uses `a ⊗ e`, with value
`⟨a, x_z⟩⟨e, y_z⟩`.

`tensor_ge_amplified`: for every coefficient vector `c`,
`‖∑ c_z x_z ⊗ y_z‖² ≥ ‖∑ c_z ⟨e, y_z⟩ x_z‖² / ‖e‖²`.

So any RIP bound for the product dictionary on `W` is also an *amplified* degree-one bound: the
rows `x_z` weighted by the amplifier `w_z = ⟨e, y_z⟩`. Product designs are amplification by the
second factor, priced by whatever certifies the product's RIP (e.g. pointwise coherence
`μ_x μ_y` via Gershgorin, which is outside the amplify–reflect closure of `arvi_kwall`).
-/

namespace QRH.ArviRIP

open Finset
open scoped BigOperators ComplexConjugate

variable {d₁ d₂ : ℕ}

/-- The product atom in coordinates. -/
def tens (x : Fin d₁ → ℂ) (y : Fin d₂ → ℂ) : Fin d₁ × Fin d₂ → ℂ := fun p => x p.1 * y p.2

/-- `‖v‖²` in coordinates. -/
noncomputable def nsq {κ : Type*} [Fintype κ] (v : κ → ℂ) : ℝ := ∑ k, ‖v k‖ ^ 2

/-- Cauchy–Schwarz in coordinates: `|⟨e, v⟩|² ≤ ‖e‖² ‖v‖²`. -/
theorem norm_inner_sq_le {κ : Type*} [Fintype κ] (e v : κ → ℂ) :
    ‖∑ k, conj (e k) * v k‖ ^ 2 ≤ nsq e * nsq v := by
  have h1 : ‖∑ k, conj (e k) * v k‖ ≤ ∑ k, ‖e k‖ * ‖v k‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [norm_mul, Complex.norm_conj]
  have h3 : (∑ k, ‖e k‖ * ‖v k‖) ^ 2 ≤ nsq e * nsq v := by
    have := Finset.sum_mul_sq_le_sq_mul_sq univ (fun k => ‖e k‖) (fun k => ‖v k‖)
    simpa [nsq] using this
  have h0 : 0 ≤ ‖∑ k, conj (e k) * v k‖ := norm_nonneg _
  exact (pow_le_pow_left₀ h0 h1 2).trans h3

/-- **Tensoring is amplification.** Projecting the second factor of `∑ c_z x_z ⊗ y_z` onto `e`
shows `‖∑ c_z ⟨e,y_z⟩ x_z‖² ≤ ‖e‖² ‖∑ c_z x_z ⊗ y_z‖²`. -/
theorem tensor_ge_amplified {ι : Type*} (S : Finset ι) (c : ι → ℂ) (x : ι → Fin d₁ → ℂ)
    (y : ι → Fin d₂ → ℂ) (e : Fin d₂ → ℂ) :
    nsq (fun a => ∑ z ∈ S, c z * (∑ b, conj (e b) * y z b) * x z a) ≤
      nsq e * nsq (fun p : Fin d₁ × Fin d₂ => ∑ z ∈ S, c z * tens (x z) (y z) p) := by
  -- for each first coordinate a, the amplified entry is ⟨e, v_a⟩ with v_a(b) = ∑ c_z x_z(a) y_z(b)
  have hrow : ∀ a : Fin d₁, (∑ z ∈ S, c z * (∑ b, conj (e b) * y z b) * x z a) =
      ∑ b, conj (e b) * (∑ z ∈ S, c z * tens (x z) (y z) (a, b)) := by
    intro a
    simp only [tens, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun z _ => ?_
    ring
  have hle : ∀ a : Fin d₁, ‖∑ z ∈ S, c z * (∑ b, conj (e b) * y z b) * x z a‖ ^ 2 ≤
      nsq e * ∑ b, ‖∑ z ∈ S, c z * tens (x z) (y z) (a, b)‖ ^ 2 := by
    intro a
    rw [hrow a]
    exact norm_inner_sq_le e (fun b => ∑ z ∈ S, c z * tens (x z) (y z) (a, b))
  calc nsq (fun a => ∑ z ∈ S, c z * (∑ b, conj (e b) * y z b) * x z a)
      ≤ ∑ a, nsq e * ∑ b, ‖∑ z ∈ S, c z * tens (x z) (y z) (a, b)‖ ^ 2 :=
        Finset.sum_le_sum fun a _ => hle a
    _ = nsq e * nsq (fun p : Fin d₁ × Fin d₂ => ∑ z ∈ S, c z * tens (x z) (y z) p) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [nsq, Fintype.sum_prod_type]

end QRH.ArviRIP

#print axioms QRH.ArviRIP.tensor_ge_amplified
