import Mathlib

/-!
# Lemma F as ordinary source steps (see `../cap-induction/README.md`, §5)

A self step `(B, Λ, c) → (B, Λ, c')` of Lemma F has crossing `0/0` in the fork's finite predicate,
which computes `crossing n low = (low.B − n.B)/(low.L − n.L)`. Rotating the child by a tiny `η > 0`
gives an ordinary step:
- `crossing_rotated`: the crossing is exactly the parent's cap `c`;
- `budget_rotated`: Collet's budget `B − B₀ + (Λ₀ − Λ)·cross ≤ 0` holds with equality;
- `excess_rotated`: the LOW excess `b + (t − B₀)/Λ₀` is `(η(b − c) + Λe)/Λ₀`, i.e. Lemma F's `e` up to
  `O(η)`, so the amplifier is Lemma F's `a'` up to `O(η)`;
- `line_gap_rotated`: the child's line lies below the parent's for `z < c` and above it beyond.

All are exact identities over `ℚ`, the field the certificates use.
-/

namespace Lab.RotatedSelfParent

theorem crossing_rotated (B₀ Λ₀ c η : ℚ) (hη : η ≠ 0) :
    (B₀ - (B₀ - η * c)) / (Λ₀ - (Λ₀ - η)) = c := by
  have h1 : B₀ - (B₀ - η * c) = η * c := by ring
  have h2 : Λ₀ - (Λ₀ - η) = η := by ring
  rw [h1, h2, mul_div_assoc, mul_comm, div_mul_cancel₀ c hη]

theorem budget_rotated (B₀ Λ₀ c η : ℚ) :
    (B₀ - η * c) - B₀ + (Λ₀ - (Λ₀ - η)) * c = 0 := by ring

theorem excess_rotated (B₀ Λ₀ c η b e : ℚ) (hΛ₀ : Λ₀ ≠ 0) :
    b + (((B₀ - η * c) - (Λ₀ - η) * (b - e)) - B₀) / Λ₀
      = (η * (b - c) + (Λ₀ - η) * e) / Λ₀ := by
  field_simp
  ring

theorem line_gap_rotated (B₀ Λ₀ c η z : ℚ) :
    ((B₀ - η * c) - (Λ₀ - η) * z) - (B₀ - Λ₀ * z) = η * (z - c) := by ring

/-- At `η = 0` the excess is exactly Lemma F's mesh `e` (scaled by `Λ/Λ₀ = 1`). -/
theorem excess_selfparent (B Λ b e : ℚ) (hΛ : Λ ≠ 0) :
    b + ((B - Λ * (b - e)) - B) / Λ = e := by
  field_simp
  ring

end Lab.RotatedSelfParent
