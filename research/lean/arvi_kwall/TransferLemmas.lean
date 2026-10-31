import Mathlib

/-!
# Transfer lemmas for randomized dictionaries

Research file (QRH, RIP program (4); the fresh look's §1.1–1.3, `rip/wide/FRESH_LOOK.md`). These are the
elementary facts behind "a random dictionary cannot carry the degree-1 part across by coherence".

* **Douglas, easy direction** (§1.2). If `X = A Y` with `‖A x‖ ≤ c ‖x‖` for all `x`, then
  `‖X v‖² ≤ c² ‖Y v‖²` for all `v` (`douglas_easy`), i.e. the Gram domination `Xᴴ X ≼ c² Yᴴ Y`
  (`douglas_gram`: the matrix `c² Yᴴ Y - Xᴴ X` is positive semidefinite). So a factorization tie of the
  sextic atoms to a model is a Gram domination, never weaker than the target.
* **Gram mixtures with independent rows** (§1.3(c)), in counting form. Let `Ω` be a finite type, `Z` the
  finite set of rows and `u : Z → Ω → (σ → ℂ)`. Over all assignments `ω : Z → Ω` (the counting measure on
  the product space, under which the rows `ω z` are independent and uniform), for `z ≠ z'`
  `∑_ω ⟨u z (ω z), u z' (ω z')⟩ = |Ω|^{|Z|-2} ⟨∑_t u z t, ∑_t u z' t⟩` (`gram_mixture_offdiag`). So the
  off-diagonal Gram of independent random rows averages to the Gram of the mean rows
  (`gram_mixture_offdiag_avg`): the randomness drops out.
* **Cross-coherence carries no information** (§1.1). The standard basis of `ℂ^S` has RIP constant `0` on
  every support (`stdBasis_ripOn_zero`). A flat vector (`|x_n|² = 1/S`) has `|⟨e_n, x⟩|² = 1/S` with every
  basis vector (`stdBasis_cross_coherence`), and `1/S` is the minimum possible
  (`exists_coherence_ge`, Parseval). Both facts hold for the family whose rows are all equal to one flat
  vector, whose RIP constant on a support `W` is at least `|W| - 1` (`equal_rows_not_rip`). They are
  gathered in `cross_coherence_no_information`: "the dictionary has RIP and is incoherent with the rows"
  gives no bound on `‖X_W‖`.
-/

set_option autoImplicit false

namespace QRH.ArviKWall

open Finset Matrix
open scoped BigOperators ComplexOrder ComplexConjugate Matrix

/-! ### Douglas, easy direction -/

section Douglas

variable {ρ τ σ : Type*} [Fintype ρ] [Fintype τ] [Fintype σ]

/-- **Douglas, easy direction.** If `X = A Y` with `‖A x‖² ≤ c² ‖x‖²` for all `x` (that is,
`‖A x‖ ≤ |c| ‖x‖`), then `‖X v‖² ≤ c² ‖Y v‖²` for all `v`. -/
theorem douglas_easy (X : Matrix ρ σ ℂ) (A : Matrix ρ τ ℂ) (Y : Matrix τ σ ℂ) (hXY : X = A * Y)
    {c : ℝ} (hA : ∀ x : τ → ℂ, ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ c ^ 2 * ∑ j, ‖x j‖ ^ 2) (v : σ → ℂ) :
    ∑ i, ‖(X *ᵥ v) i‖ ^ 2 ≤ c ^ 2 * ∑ j, ‖(Y *ᵥ v) j‖ ^ 2 := by
  rw [hXY, ← mulVec_mulVec]
  exact hA (Y *ᵥ v)

/-- The form of a Gram matrix is the squared norm: `⟨x, Xᴴ X x⟩ = ‖X x‖²`. -/
theorem form_gram (X : Matrix ρ σ ℂ) (x : σ → ℂ) :
    star x ⬝ᵥ ((Xᴴ * X) *ᵥ x) = ((∑ i, ‖(X *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  have : ∀ w : ρ → ℂ, star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    intro w
    have h : star w ⬝ᵥ w = ∑ i, star (w i) * w i := rfl
    rw [h, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  exact this (X *ᵥ x)

/-- **Gram domination.** Under the hypotheses of `douglas_easy`, `Xᴴ X ≼ c² Yᴴ Y`: the matrix
`c² Yᴴ Y - Xᴴ X` is positive semidefinite. -/
theorem douglas_gram (X : Matrix ρ σ ℂ) (A : Matrix ρ τ ℂ) (Y : Matrix τ σ ℂ) (hXY : X = A * Y)
    {c : ℝ} (hA : ∀ x : τ → ℂ, ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ c ^ 2 * ∑ j, ‖x j‖ ^ 2) :
    ((c ^ 2 : ℝ) • (Yᴴ * Y) - Xᴴ * X).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · exact (isHermitian_conjTranspose_mul_self Y |>.smul (IsSelfAdjoint.all _)).sub
      (isHermitian_conjTranspose_mul_self X)
  · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, form_gram,
      form_gram]
    have h := douglas_easy X A Y hXY hA x
    rw [Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    exact Complex.zero_le_real.mpr (sub_nonneg.mpr h)

end Douglas

/-! ### Gram mixtures with independent rows -/

section GramMixture

variable {Z Ω σ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Ω] [Fintype σ]

/-- **Two coordinates of a product space.** Summing a function of `(ω z, ω z')` over all `ω : Z → Ω` with
`z ≠ z'` counts each pair `|Ω|^{|Z|-2}` times:
`∑_ω Φ(ω z) Ψ(ω z') = |Ω|^{|Z|-2} (∑_t Φ t)(∑_t Ψ t)`. -/
theorem sum_pi_two {z z' : Z} (hzz : z ≠ z') (Φ Ψ : Ω → ℂ) :
    ∑ ω : Z → Ω, Φ (ω z) * Ψ (ω z') =
      (Fintype.card Ω : ℂ) ^ (Fintype.card Z - 2) * ((∑ t, Φ t) * ∑ t, Ψ t) := by
  let g : Z → Ω → ℂ := fun w t => if w = z then Φ t else if w = z' then Ψ t else 1
  have h1 : ∏ w, ∑ t, g w t = ∑ ω : Z → Ω, ∏ w, g w (ω w) := by
    rw [Finset.prod_univ_sum]
    simp
  have h2 : ∀ ω : Z → Ω, ∏ w, g w (ω w) = Φ (ω z) * Ψ (ω z') := by
    intro ω
    rw [Finset.prod_eq_mul z z' hzz]
    · simp [g, hzz.symm]
    · intro c _ hc
      simp [g, hc.1, hc.2]
    · intro h
      exact absurd (Finset.mem_univ z) h
    · intro h
      exact absurd (Finset.mem_univ z') h
  have h3 : ∏ w, ∑ t, g w t =
      (Fintype.card Ω : ℂ) ^ (Fintype.card Z - 2) * ((∑ t, Φ t) * ∑ t, Ψ t) := by
    have hz' : z' ∈ Finset.univ.erase z := Finset.mem_erase.mpr ⟨hzz.symm, Finset.mem_univ z'⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun w => ∑ t, g w t) (Finset.mem_univ z),
      ← Finset.mul_prod_erase (Finset.univ.erase z) (fun w => ∑ t, g w t) hz']
    have e1 : ∑ t, g z t = ∑ t, Φ t := by simp [g]
    have e2 : ∑ t, g z' t = ∑ t, Ψ t := by simp [g, hzz.symm]
    have e3 : ∀ w ∈ (Finset.univ.erase z).erase z', ∑ t, g w t = (Fintype.card Ω : ℂ) := by
      intro w hw
      have hw1 : w ≠ z' := (Finset.mem_erase.mp hw).1
      have hw2 : w ≠ z := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
      simp [g, hw1, hw2]
    have hcard : ((Finset.univ.erase z).erase z').card = Fintype.card Z - 2 := by
      rw [Finset.card_erase_of_mem hz', Finset.card_erase_of_mem (Finset.mem_univ z),
        Finset.card_univ]
      omega
    rw [e1, e2, Finset.prod_congr rfl e3, Finset.prod_const, hcard]
    ring
  calc ∑ ω : Z → Ω, Φ (ω z) * Ψ (ω z') = ∑ ω : Z → Ω, ∏ w, g w (ω w) :=
        Finset.sum_congr rfl fun ω _ => (h2 ω).symm
    _ = ∏ w, ∑ t, g w t := h1.symm
    _ = _ := h3

/-- **Gram mixtures with independent rows, in counting form.** Over all assignments `ω : Z → Ω` (counting
measure on the product space, so the rows are independent and uniform), for `z ≠ z'`:
`∑_ω ⟨u z (ω z), u z' (ω z')⟩ = |Ω|^{|Z|-2} · ⟨∑_t u z t, ∑_t u z' t⟩`, with `⟨p, q⟩ = ∑_n conj (p n) q n`. -/
theorem gram_mixture_offdiag (u : Z → Ω → σ → ℂ) {z z' : Z} (hzz : z ≠ z') :
    ∑ ω : Z → Ω, star (u z (ω z)) ⬝ᵥ u z' (ω z') =
      (Fintype.card Ω : ℂ) ^ (Fintype.card Z - 2) *
        (star (∑ t, u z t) ⬝ᵥ ∑ t, u z' t) := by
  have hL : ∀ ω : Z → Ω, star (u z (ω z)) ⬝ᵥ u z' (ω z') =
      ∑ n, star (u z (ω z) n) * u z' (ω z') n := fun ω => rfl
  have hR : star (∑ t, u z t) ⬝ᵥ ∑ t, u z' t =
      ∑ n, (∑ t, star (u z t n)) * ∑ t, u z' t n := by
    simp [dotProduct, Finset.sum_apply]
  simp_rw [hL]
  rw [Finset.sum_comm, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact sum_pi_two hzz (fun t => star (u z t n)) (fun t => u z' t n)

/-- The mean row of the dictionary `t ↦ u z t`. -/
noncomputable def meanRow (u : Z → Ω → σ → ℂ) (z : Z) : σ → ℂ :=
  (Fintype.card Ω : ℂ)⁻¹ • ∑ t, u z t

/-- **The averaged off-diagonal Gram is the Gram of the mean rows.** The expectation over independent
uniform rows of `⟨u z (ω z), u z' (ω z')⟩` is `⟨mean_z, mean_z'⟩`. -/
theorem gram_mixture_offdiag_avg [Nonempty Ω] (u : Z → Ω → σ → ℂ) {z z' : Z} (hzz : z ≠ z') :
    (∑ ω : Z → Ω, star (u z (ω z)) ⬝ᵥ u z' (ω z')) / (Fintype.card Ω : ℂ) ^ Fintype.card Z =
      star (meanRow u z) ⬝ᵥ meanRow u z' := by
  have hN : (Fintype.card Ω : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hZ : 2 ≤ Fintype.card Z := by
    have := Finset.card_le_univ ({z, z'} : Finset Z)
    rwa [Finset.card_pair hzz] at this
  have hpow : (Fintype.card Ω : ℂ) ^ Fintype.card Z =
      (Fintype.card Ω : ℂ) ^ (Fintype.card Z - 2) * (Fintype.card Ω : ℂ) ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hZ]
  rw [gram_mixture_offdiag u hzz, hpow]
  simp only [meanRow, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, star_inv₀,
    Complex.star_def, Complex.conj_natCast]
  field_simp

end GramMixture

/-! ### Cross-coherence carries no information -/

section CrossCoherence

/-- `u` has the restricted isometry property with constant `δ` on the support `T`:
`|‖∑_{i∈T} c_i u_i‖² - ∑_{i∈T} |c_i|²| ≤ δ ∑_{i∈T} |c_i|²` for all coefficients `c`. -/
def RIPOn {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u : ι → E) (T : Finset ι)
    (δ : ℝ) : Prop :=
  ∀ c : ι → ℂ, |‖∑ i ∈ T, c i • u i‖ ^ 2 - ∑ i ∈ T, ‖c i‖ ^ 2| ≤ δ * ∑ i ∈ T, ‖c i‖ ^ 2

/-- Orthonormal vectors are exact isometries: `‖∑_{i∈T} c_i u_i‖² = ∑_{i∈T} |c_i|²`. -/
theorem norm_sq_sum_orthonormal {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {u : ι → E} (hu : Orthonormal ℂ u) (T : Finset ι) (c : ι → ℂ) :
    ‖∑ i ∈ T, c i • u i‖ ^ 2 = ∑ i ∈ T, ‖c i‖ ^ 2 := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ, hu.inner_sum c c T, RCLike.re_to_complex,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The standard basis of `ℂ^S`. -/
noncomputable def stdBasis (i : S) : EuclideanSpace ℂ S := EuclideanSpace.single i (1 : ℂ)

/-- **The standard basis has RIP constant `0` on every support.** -/
theorem stdBasis_ripOn_zero (T : Finset S) : RIPOn (stdBasis (S := S)) T 0 := by
  intro c
  have h := norm_sq_sum_orthonormal (EuclideanSpace.orthonormal_single (ι := S) (𝕜 := ℂ)) T c
  have h' : ‖∑ i ∈ T, c i • stdBasis i‖ ^ 2 = ∑ i ∈ T, ‖c i‖ ^ 2 := h
  rw [h']
  simp

/-- The coherence of the basis vector `e_n` with a vector `x` is the `n`-th coordinate. -/
theorem stdBasis_inner (x : EuclideanSpace ℂ S) (n : S) :
    inner ℂ (stdBasis n) x = x.ofLp n := by
  simp [stdBasis, EuclideanSpace.inner_single_left]

/-- **Flat vectors have the cross-coherence `1/S` with every basis vector.** -/
theorem stdBasis_cross_coherence (x : EuclideanSpace ℂ S)
    (hx : ∀ n, ‖x.ofLp n‖ ^ 2 = 1 / (Fintype.card S : ℝ)) (n : S) :
    ‖inner ℂ (stdBasis n) x‖ ^ 2 = 1 / (Fintype.card S : ℝ) := by
  rw [stdBasis_inner, hx]

/-- **`1/S` is the minimum** (Parseval): every unit vector has a basis vector with
`|⟨e_n, x⟩|² ≥ 1/S`. -/
theorem exists_coherence_ge [Nonempty S] (x : EuclideanSpace ℂ S) (hx : ‖x‖ = 1) :
    ∃ n, 1 / (Fintype.card S : ℝ) ≤ ‖inner ℂ (stdBasis n) x‖ ^ 2 := by
  have hsum : ∑ n, ‖x.ofLp n‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hx, one_pow]
  have hcard : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  have h : ∑ _n : S, 1 / (Fintype.card S : ℝ) ≤ ∑ n, ‖x.ofLp n‖ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum]
    field_simp
    exact le_refl _
  obtain ⟨n, -, hn⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty h
  exact ⟨n, by rwa [stdBasis_inner]⟩

omit [DecidableEq S] in
/-- A flat vector (all `|x_n|² = 1/S`) is a unit vector. -/
theorem norm_eq_one_of_flat [Nonempty S] (x : EuclideanSpace ℂ S)
    (hx : ∀ n, ‖x.ofLp n‖ ^ 2 = 1 / (Fintype.card S : ℝ)) : ‖x‖ = 1 := by
  have hcard : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  have h : ‖x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [hx]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) two_ne_zero).mp h

/-- **Equal rows have no RIP.** If all the rows are equal to one unit vector `x`, then on a support `W`
the RIP constant is at least `|W| - 1`: `‖X_W‖² = |W|`, however flat the rows are. -/
theorem equal_rows_not_rip {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E)
    (hx : ‖x‖ = 1) (W : Finset Z) (hW : W.Nonempty) {δ : ℝ} (hδ : δ < (W.card : ℝ) - 1) :
    ¬ RIPOn (fun _ : Z => x) W δ := by
  intro h
  have h1 := h (fun _ => (1 : ℂ))
  simp only [one_smul, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
  have hc : (0 : ℝ) < W.card := Nat.cast_pos.mpr hW.card_pos
  have hn : ‖W.card • x‖ ^ 2 = (W.card : ℝ) ^ 2 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, norm_smul, mul_pow, hx]
    simp
  rw [hn] at h1
  have habs : (W.card : ℝ) ^ 2 - W.card ≤ δ * W.card := (le_abs_self _).trans h1
  have h2 : ((W.card : ℝ) - 1) * W.card ≤ δ * W.card := by linarith only [habs]
  have h3 : (W.card : ℝ) - 1 ≤ δ := le_of_mul_le_mul_right h2 hc
  linarith only [h3, hδ]

/-- **Cross-coherence carries no information.** Let `x₀` be a flat vector of `ℂ^S` (all
`|x₀_n|² = 1/S`) and take it as every row of a family on a support `W`. Then:
the standard basis has RIP constant `0` on every support; every row has the cross-coherence `1/S` with
every basis vector; `1/S` is the smallest value any unit vector can have; and yet the family of rows has
RIP constant at least `|W| - 1` on `W` (indeed `‖X_W‖² = |W|`). So "the dictionary has RIP and is
incoherent with the rows" holds for every flat family, including the worst one, and implies no bound
on `‖X_W‖`. -/
theorem cross_coherence_no_information [Nonempty S] {Z : Type*} (x₀ : EuclideanSpace ℂ S)
    (hx : ∀ n, ‖x₀.ofLp n‖ ^ 2 = 1 / (Fintype.card S : ℝ)) (W : Finset Z) (hW : W.Nonempty)
    {δ : ℝ} (hδ : δ < (W.card : ℝ) - 1) :
    (∀ T : Finset S, RIPOn (stdBasis (S := S)) T 0) ∧
    (∀ n, ‖inner ℂ (stdBasis n) x₀‖ ^ 2 = 1 / (Fintype.card S : ℝ)) ∧
    (∀ v : EuclideanSpace ℂ S, ‖v‖ = 1 →
      ∃ n, 1 / (Fintype.card S : ℝ) ≤ ‖inner ℂ (stdBasis n) v‖ ^ 2) ∧
    ¬ RIPOn (fun _ : Z => x₀) W δ :=
  ⟨stdBasis_ripOn_zero, stdBasis_cross_coherence x₀ hx, exists_coherence_ge,
    equal_rows_not_rip x₀ (norm_eq_one_of_flat x₀ hx) W hW hδ⟩

end CrossCoherence

end QRH.ArviKWall

#print axioms QRH.ArviKWall.douglas_easy
#print axioms QRH.ArviKWall.douglas_gram
#print axioms QRH.ArviKWall.gram_mixture_offdiag
#print axioms QRH.ArviKWall.gram_mixture_offdiag_avg
#print axioms QRH.ArviKWall.cross_coherence_no_information
