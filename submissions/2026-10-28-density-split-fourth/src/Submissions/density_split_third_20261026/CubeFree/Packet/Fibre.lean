/- Copyright (c) 2026 Sil. Apache-2.0.
Divisor-fibre bounds for the common-profile separation (common-profile lemma, Section 3(v)).

For a nonzero row ideal `r` with `N(r) ≤ Z^C`, every finite family of `k`-tuples of ideals
whose components divide `r` (in particular tuples whose product divides `r`, and the genuine
data `(G, V, u)` with `G·V ∣ r`, `u ∣ G`) has at most `τ(r)^k ≤ C_δ Z^δ` members, for every
`δ > 0`, uniformly in `Z ≥ 1`. The weighted form gives the fibre hypothesis `hD` of
`CommonProfile.weighted_separation`. The divisor bound `τ(I) ≪_ε N(I)^ε` is the OAI baseline's
`IdealDivisorBound.ideal_divisor_small_power`. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.Family

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.Packet.Fibre
noncomputable section
open scoped BigOperators Classical
open OAI OAI.IdealMobiusDivisorSum
local notation "O" => OAI.SevenEighths.HeckeFamily.O

/-- The `k`-tuples of divisors of `r`. -/
def divisorTuples (k : ℕ) (r : Ideal O) : Finset (Fin k → Ideal O) :=
  Fintype.piFinset fun _ => idealDivisors r

theorem card_divisorTuples (k : ℕ) (r : Ideal O) :
    (divisorTuples k r).card = (idealDivisors r).card ^ k := by
  simp [divisorTuples, Fintype.card_piFinset]

theorem mem_divisorTuples {k : ℕ} {r : Ideal O} (hr : r ≠ ⊥) (f : Fin k → Ideal O) :
    f ∈ divisorTuples k r ↔ ∀ i, f i ∣ r := by
  simp only [divisorTuples, Fintype.mem_piFinset]
  exact forall_congr' fun i => mem_idealDivisors hr

/-- Any family of tuples whose components divide `r` has at most `τ(r)^k` members. -/
theorem card_le_of_components_dvd {k : ℕ} {r : Ideal O} (hr : r ≠ ⊥)
    (T : Finset (Fin k → Ideal O)) (hT : ∀ f ∈ T, ∀ i, f i ∣ r) :
    T.card ≤ (idealDivisors r).card ^ k := by
  rw [← card_divisorTuples]
  exact Finset.card_le_card fun f hf => (mem_divisorTuples hr f).mpr (hT f hf)

/-- Tuples whose product divides `r`. -/
def prodDvdTuples (k : ℕ) (r : Ideal O) : Finset (Fin k → Ideal O) :=
  (divisorTuples k r).filter fun f => ∏ i, f i ∣ r

theorem mem_prodDvdTuples {k : ℕ} {r : Ideal O} (hr : r ≠ ⊥) (f : Fin k → Ideal O) :
    f ∈ prodDvdTuples k r ↔ ∏ i, f i ∣ r := by
  rw [prodDvdTuples, Finset.mem_filter, mem_divisorTuples hr]
  constructor
  · exact And.right
  · intro h
    exact ⟨fun i => (Finset.dvd_prod_of_mem f (Finset.mem_univ i)).trans h, h⟩

theorem card_prodDvdTuples_le {k : ℕ} {r : Ideal O} :
    (prodDvdTuples k r).card ≤ (idealDivisors r).card ^ k := by
  rw [← card_divisorTuples]
  exact Finset.card_filter_le _ _

/-- The genuine `(G, V, u)` data: `G·V ∣ r` and `u ∣ G` (squarefreeness of `u` is not needed
for the count). -/
theorem card_GVu_le {r : Ideal O} (hr : r ≠ ⊥) (T : Finset (Ideal O × Ideal O × Ideal O))
    (hT : ∀ x ∈ T, x.1 * x.2.1 ∣ r ∧ x.2.2 ∣ x.1) :
    T.card ≤ (idealDivisors r).card ^ 3 := by
  have hsub : T ⊆ idealDivisors r ×ˢ (idealDivisors r ×ˢ idealDivisors r) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hT x hx
    have hG : x.1 ∣ r := (dvd_mul_right _ _).trans h1
    have hV : x.2.1 ∣ r := (dvd_mul_left _ _).trans h1
    simp only [Finset.mem_product, mem_idealDivisors hr]
    exact ⟨hG, hV, h2.trans hG⟩
  calc T.card ≤ (idealDivisors r ×ˢ (idealDivisors r ×ˢ idealDivisors r)).card :=
        Finset.card_le_card hsub
    _ = (idealDivisors r).card ^ 3 := by
        rw [Finset.card_product, Finset.card_product]; ring

/-- **Subpower divisor powers.** For every exponent `k`, polynomial range `N(r) ≤ Z^C` and
`δ > 0`: `τ(r)^k ≤ C_δ Z^δ`, uniformly in `Z ≥ 1`. -/
theorem divisor_power_subpower (k : ℕ) (Cexp δ : ℝ) (hCexp : 0 ≤ Cexp) (hδ : 0 < δ) :
    ∃ Cδ : ℝ, 0 < Cδ ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ r : Ideal O, r ≠ ⊥ →
      (Ideal.absNorm r : ℝ) ≤ Z ^ Cexp →
        ((idealDivisors r).card : ℝ) ^ k ≤ Cδ * Z ^ δ := by
  set ε : ℝ := δ / ((k : ℝ) * Cexp + 1) with hεdef
  have hden : 0 < (k : ℝ) * Cexp + 1 := by positivity
  have hε : 0 < ε := div_pos hδ hden
  obtain ⟨C, hC, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  set C' : ℝ := max C 1
  have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨C' ^ k, pow_pos hC' k, ?_⟩
  intro Z hZ r hr hN
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hexp : Cexp * ε * k ≤ δ := by
    have h1 : Cexp * ε * k = δ * ((k : ℝ) * Cexp / ((k : ℝ) * Cexp + 1)) := by
      rw [hεdef]; field_simp
    have h2 : (k : ℝ) * Cexp / ((k : ℝ) * Cexp + 1) ≤ 1 := by
      rw [div_le_one hden]; linarith
    rw [h1]
    calc δ * ((k : ℝ) * Cexp / ((k : ℝ) * Cexp + 1)) ≤ δ * 1 :=
          mul_le_mul_of_nonneg_left h2 hδ.le
      _ = δ := mul_one δ
  have hτ : ((idealDivisors r).card : ℝ) ≤ C' * Z ^ (Cexp * ε) := by
    calc ((idealDivisors r).card : ℝ) ≤ C * (Ideal.absNorm r : ℝ) ^ ε := hdiv r hr
      _ ≤ C' * (Z ^ Cexp) ^ ε := by
          apply mul_le_mul (le_max_left _ _)
            (Real.rpow_le_rpow (Nat.cast_nonneg _) hN hε.le) (by positivity) hC'.le
      _ = C' * Z ^ (Cexp * ε) := by rw [← Real.rpow_mul hZ0]
  calc ((idealDivisors r).card : ℝ) ^ k ≤ (C' * Z ^ (Cexp * ε)) ^ k :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hτ k
    _ = C' ^ k * Z ^ (Cexp * ε * k) := by
        rw [mul_pow, Real.rpow_mul_natCast hZ0]
    _ ≤ C' ^ k * Z ^ δ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) (by positivity)

/-- **Fibre count for `k`-tuples.** -/
theorem tuple_count_subpower (k : ℕ) (Cexp δ : ℝ) (hCexp : 0 ≤ Cexp) (hδ : 0 < δ) :
    ∃ Cδ : ℝ, 0 < Cδ ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ r : Ideal O, r ≠ ⊥ →
      (Ideal.absNorm r : ℝ) ≤ Z ^ Cexp →
      ∀ T : Finset (Fin k → Ideal O), (∀ f ∈ T, ∀ i, f i ∣ r) →
        (T.card : ℝ) ≤ Cδ * Z ^ δ := by
  obtain ⟨Cδ, hCδ, h⟩ := divisor_power_subpower k Cexp δ hCexp hδ
  refine ⟨Cδ, hCδ, fun Z hZ r hr hN T hT => ?_⟩
  calc (T.card : ℝ) ≤ ((idealDivisors r).card ^ k : ℕ) := by
        exact_mod_cast card_le_of_components_dvd hr T hT
    _ = ((idealDivisors r).card : ℝ) ^ k := by push_cast; ring
    _ ≤ Cδ * Z ^ δ := h Z hZ r hr hN

/-- **Fibre count for tuples whose product divides `r`.** -/
theorem prodDvd_count_subpower (k : ℕ) (Cexp δ : ℝ) (hCexp : 0 ≤ Cexp) (hδ : 0 < δ) :
    ∃ Cδ : ℝ, 0 < Cδ ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ r : Ideal O, r ≠ ⊥ →
      (Ideal.absNorm r : ℝ) ≤ Z ^ Cexp →
        ((prodDvdTuples k r).card : ℝ) ≤ Cδ * Z ^ δ := by
  obtain ⟨Cδ, hCδ, h⟩ := tuple_count_subpower k Cexp δ hCexp hδ
  refine ⟨Cδ, hCδ, fun Z hZ r hr hN => h Z hZ r hr hN _ fun f hf i => ?_⟩
  exact (Finset.dvd_prod_of_mem f (Finset.mem_univ i)).trans ((mem_prodDvdTuples hr f).mp hf)

/-- **Fibre count for the genuine `(G, V, u)` data.** -/
theorem GVu_count_subpower (Cexp δ : ℝ) (hCexp : 0 ≤ Cexp) (hδ : 0 < δ) :
    ∃ Cδ : ℝ, 0 < Cδ ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ r : Ideal O, r ≠ ⊥ →
      (Ideal.absNorm r : ℝ) ≤ Z ^ Cexp →
      ∀ T : Finset (Ideal O × Ideal O × Ideal O), (∀ x ∈ T, x.1 * x.2.1 ∣ r ∧ x.2.2 ∣ x.1) →
        (T.card : ℝ) ≤ Cδ * Z ^ δ := by
  obtain ⟨Cδ, hCδ, h⟩ := divisor_power_subpower 3 Cexp δ hCexp hδ
  refine ⟨Cδ, hCδ, fun Z hZ r hr hN T hT => ?_⟩
  calc (T.card : ℝ) ≤ ((idealDivisors r).card ^ 3 : ℕ) := by
        exact_mod_cast card_GVu_le hr T hT
    _ = ((idealDivisors r).card : ℝ) ^ 3 := by push_cast; ring
    _ ≤ Cδ * Z ^ δ := h Z hZ r hr hN

/-- **Weighted fibre bound (`hD`).** If the labels over `r` are encoded injectively by
`k`-tuples of divisors of `r` (e.g. `G`, `V`, allocations, first artificial divisors, frozen
assignments) and every weight is at most `Wmax` (e.g. a fixed divisor power of `r` such as
`ρ(G) ≤ τ(r)`, already absorbed into `Wmax`), the fibre weight is `≤ Wmax · C_δ Z^δ`. -/
theorem weighted_fibre_subpower {Λ : Type*} (k : ℕ) (Cexp δ : ℝ) (hCexp : 0 ≤ Cexp)
    (hδ : 0 < δ) :
    ∃ Cδ : ℝ, 0 < Cδ ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ r : Ideal O, r ≠ ⊥ →
      (Ideal.absNorm r : ℝ) ≤ Z ^ Cexp →
      ∀ (labels : Finset Λ) (code : Λ → Fin k → Ideal O),
        Set.InjOn code labels → (∀ l ∈ labels, ∀ i, code l i ∣ r) →
      ∀ (w : Λ → ℝ) (Wmax : ℝ), (∀ l ∈ labels, w l ≤ Wmax) → 0 ≤ Wmax →
        ∑ l ∈ labels, w l ≤ Wmax * (Cδ * Z ^ δ) := by
  obtain ⟨Cδ, hCδ, h⟩ := tuple_count_subpower k Cexp δ hCexp hδ
  refine ⟨Cδ, hCδ, ?_⟩
  intro Z hZ r hr hN labels code hinj hcode w Wmax hw hWmax
  have hcard : (labels.card : ℝ) ≤ Cδ * Z ^ δ := by
    have himg := h Z hZ r hr hN (labels.image code) (by
      intro f hf i
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hf
      exact hcode l hl i)
    rwa [Finset.card_image_of_injOn hinj] at himg
  calc ∑ l ∈ labels, w l ≤ ∑ _l ∈ labels, Wmax := Finset.sum_le_sum hw
    _ = labels.card * Wmax := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Cδ * Z ^ δ) * Wmax := mul_le_mul_of_nonneg_right hcard hWmax
    _ = Wmax * (Cδ * Z ^ δ) := mul_comm _ _

end
end QRH.DensitySplitThird.CubeFree.Packet.Fibre
