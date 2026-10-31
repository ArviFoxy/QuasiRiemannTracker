import Mathlib

/-!
# Corrected large-sieve bounds transpose with explicit image corrections

Research file (QRH, K-wall; journal 2026-10-31, "The weighted corrected bound transposes with explicit image
corrections"). Sil's formal sieve bounds the dual problem through the swap `θ(L, N) = θ(N, L)`, an operator-norm
identity. A corrected bound is a statement about vectors, so the swap needs a vector form. This file proves it:

* `transpose_corrected`: if `‖E λ‖² ≤ Δ‖λ‖² + Σ_f w_f |⟨λ, f⟩|²` for every `λ`, then for every `x`,
  `‖Eᴴ x‖² ≤ 2Δ‖x‖² + Δ⁻¹ Σ_f w_f |⟨x, E f⟩|²`;
* `transpose_orthogonal`: the precondition form, `λ ⊥ F ⇒ ‖E λ‖² ≤ Δ‖λ‖²` gives `x ⊥ E(F) ⇒ ‖Eᴴ x‖² ≤ Δ‖x‖²`.

The corrections of the transposed statement are the images `E f`, explicit vectors, not polar-decomposition vectors.
Plain finite sums; `ip u v = Σ u i * conj (v i)`.
-/

namespace QRH.ArviKWall.TransposeCorrection

open Finset ComplexConjugate

variable {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι]

/-- The inner product `Σ u i · conj (v i)`. -/
noncomputable def ip {k : Type*} [Fintype k] (u v : k → ℂ) : ℂ := ∑ i, u i * conj (v i)

/-- The squared norm `Σ ‖u i‖²`. -/
noncomputable def nsq {k : Type*} [Fintype k] (u : k → ℂ) : ℝ := ∑ i, ‖u i‖ ^ 2

/-- `E λ`. -/
noncomputable def app (E : m → n → ℂ) (v : n → ℂ) : m → ℂ := fun i => ∑ j, E i j * v j

/-- `Eᴴ x`. -/
noncomputable def adj (E : m → n → ℂ) (x : m → ℂ) : n → ℂ := fun j => ∑ i, conj (E i j) * x i

theorem nsq_nonneg {k : Type*} [Fintype k] (u : k → ℂ) : 0 ≤ nsq u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem ip_self {k : Type*} [Fintype k] (u : k → ℂ) : ip u u = (nsq u : ℂ) := by
  unfold ip nsq
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- The adjoint identity `⟨Eᴴ x, v⟩ = ⟨x, E v⟩`. -/
theorem ip_adj (E : m → n → ℂ) (x : m → ℂ) (v : n → ℂ) : ip (adj E x) v = ip x (app E v) := by
  unfold ip adj app
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Cauchy–Schwarz for `ip`. -/
theorem norm_ip_sq_le {k : Type*} [Fintype k] (u v : k → ℂ) : ‖ip u v‖ ^ 2 ≤ nsq u * nsq v := by
  unfold ip nsq
  calc ‖∑ i, u i * conj (v i)‖ ^ 2 ≤ (∑ i, ‖u i‖ * ‖v i‖) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _)
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, Complex.norm_conj]
    _ ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The real inequality behind the transposition: `y² ≤ aΔy + aS` forces `y ≤ 2aΔ + S/Δ`. -/
theorem quad_bound {y a Δ S : ℝ} (hy : 0 ≤ y) (ha : 0 ≤ a) (hΔ : 0 < Δ) (hS : 0 ≤ S)
    (h : y ^ 2 ≤ a * Δ * y + a * S) : y ≤ 2 * a * Δ + S / Δ := by
  by_contra hc
  push Not at hc
  have hSΔ : 0 ≤ S / Δ := div_nonneg hS hΔ.le
  have hy2 : a * Δ ≤ y := by nlinarith
  have h1 : a * S ≤ y * (S / Δ) := by
    have : a * S = (a * Δ) * (S / Δ) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hy2 hSΔ
  have h2 : y * (2 * a * Δ + S / Δ) < y * y := by
    apply mul_lt_mul_of_pos_left hc
    nlinarith
  have h3 : 0 ≤ a * Δ * y := by positivity
  have e1 : y * (2 * a * Δ + S / Δ) = 2 * (a * Δ * y) + y * (S / Δ) := by ring
  have e2 : y ^ 2 = y * y := by ring
  linarith [h, h1, h2, h3, e1, e2]

/-- **Transposition of a weighted corrected bound.** The corrections of `Eᴴ` are the images `E f`. -/
theorem transpose_corrected (E : m → n → ℂ) (Δ : ℝ) (hΔ : 0 < Δ) (f : ι → n → ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (h : ∀ v : n → ℂ, nsq (app E v) ≤ Δ * nsq v + ∑ i, w i * ‖ip v (f i)‖ ^ 2)
    (x : m → ℂ) :
    nsq (adj E x) ≤ 2 * Δ * nsq x + (∑ i, w i * ‖ip x (app E (f i))‖ ^ 2) / Δ := by
  set y := adj E x with hydef
  set S := ∑ i, w i * ‖ip x (app E (f i))‖ ^ 2 with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  -- ⟨x, E Eᴴ x⟩ = ‖Eᴴ x‖²
  have hself : ip x (app E y) = (nsq y : ℂ) := by
    rw [← ip_adj, ← hydef, ip_self]
  -- ‖Eᴴ x‖⁴ ≤ ‖x‖² ‖E Eᴴ x‖²
  have hcs : nsq y ^ 2 ≤ nsq x * nsq (app E y) := by
    have := norm_ip_sq_le x (app E y)
    rw [hself, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nsq_nonneg y)] at this
    exact this
  -- the hypothesis at v = Eᴴ x, with ⟨Eᴴ x, f⟩ = ⟨x, E f⟩
  have hhyp : nsq (app E y) ≤ Δ * nsq y + S := by
    have := h y
    have he : ∀ i, ip y (f i) = ip x (app E (f i)) := fun i => by rw [hydef, ip_adj]
    simp_rw [he] at this
    exact this
  have hq : nsq y ^ 2 ≤ nsq x * Δ * nsq y + nsq x * S := by
    calc nsq y ^ 2 ≤ nsq x * nsq (app E y) := hcs
      _ ≤ nsq x * (Δ * nsq y + S) := mul_le_mul_of_nonneg_left hhyp (nsq_nonneg x)
      _ = nsq x * Δ * nsq y + nsq x * S := by ring
  calc nsq y ≤ 2 * nsq x * Δ + S / Δ := quad_bound (nsq_nonneg y) (nsq_nonneg x) hΔ hS hq
    _ = 2 * Δ * nsq x + S / Δ := by ring

omit [Fintype ι] in
/-- **Precondition form.** If every `λ ⊥ F` has `‖E λ‖² ≤ Δ‖λ‖²`, then every `x ⊥ E(F)` has `‖Eᴴ x‖² ≤ Δ‖x‖²`. -/
theorem transpose_orthogonal (E : m → n → ℂ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (f : ι → n → ℂ)
    (h : ∀ v : n → ℂ, (∀ i, ip v (f i) = 0) → nsq (app E v) ≤ Δ * nsq v)
    (x : m → ℂ) (hx : ∀ i, ip x (app E (f i)) = 0) :
    nsq (adj E x) ≤ Δ * nsq x := by
  set y := adj E x with hydef
  have horth : ∀ i, ip y (f i) = 0 := fun i => by rw [hydef, ip_adj]; exact hx i
  have hself : ip x (app E y) = (nsq y : ℂ) := by
    rw [← ip_adj, ← hydef, ip_self]
  have hcs : nsq y ^ 2 ≤ nsq x * nsq (app E y) := by
    have := norm_ip_sq_le x (app E y)
    rw [hself, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nsq_nonneg y)] at this
    exact this
  have hq : nsq y ^ 2 ≤ nsq x * (Δ * nsq y) :=
    hcs.trans (mul_le_mul_of_nonneg_left (h y horth) (nsq_nonneg x))
  have hy0 := nsq_nonneg y
  have hx0 := nsq_nonneg x
  by_cases hz : nsq y = 0
  · rw [hz]
    positivity
  · have hpos : 0 < nsq y := lt_of_le_of_ne hy0 (Ne.symm hz)
    nlinarith

end QRH.ArviKWall.TransposeCorrection

#print axioms QRH.ArviKWall.TransposeCorrection.transpose_corrected
#print axioms QRH.ArviKWall.TransposeCorrection.transpose_orthogonal
