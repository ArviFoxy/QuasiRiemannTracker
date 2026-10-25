/-
The faces of the source chain are the supporting lines of the envelope (research/chain-ode/README.md,
"The faces are tangent lines of one explicit curve"; research/chain-structure/README.md §1).

A face `(B, Λ)` certifies the plain moment on `m + Λz ≤ B`. With pivots dense along the chain the
face at pivot `s` is the tangent of the envelope `E`: `Λ = −E′(s)`, `B = E(s) + Λs`. The envelope
is convex (the faces get flatter along the chain).

* `face_below`: for a convex envelope, every tangent face lies below it, `B − Λt ≤ E(t)` on the whole
  domain, with equality at the pivot (`face_touches`).
* `legendre`: hence `B = min_t (E(t) + Λt)`: the face set is the Legendre transform of the envelope,
  and the envelope is the pointwise maximum of its faces.
Status: proved.
-/
import Mathlib

namespace ChainLegendre

open Set

/-- A tangent face of a convex envelope lies below the envelope. -/
theorem face_below {E : ℝ → ℝ} {S : Set ℝ} {s Λ : ℝ} (hconv : ConvexOn ℝ S E) (hs : s ∈ S)
    (hd : HasDerivAt E (-Λ) s) {t : ℝ} (ht : t ∈ S) :
    (E s + Λ * s) - Λ * t ≤ E t := by
  rcases lt_trichotomy s t with h | h | h
  · have hsl := hconv.le_slope_of_hasDerivAt hs ht h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at hsl
    linarith
  · subst h; linarith
  · have hsl := hconv.slope_le_of_hasDerivAt ht hs h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at hsl
    linarith

/-- The face touches the envelope at its pivot. -/
theorem face_touches (E : ℝ → ℝ) (s Λ : ℝ) : (E s + Λ * s) - Λ * s = E s := by ring

/-- **Legendre duality.** The intercept of the tangent face is the minimum of `E(t) + Λt` over the
domain, attained at the pivot. -/
theorem legendre {E : ℝ → ℝ} {S : Set ℝ} {s Λ : ℝ} (hconv : ConvexOn ℝ S E) (hs : s ∈ S)
    (hd : HasDerivAt E (-Λ) s) :
    IsLeast ((fun t => E t + Λ * t) '' S) (E s + Λ * s) := by
  refine ⟨⟨s, hs, rfl⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have := face_below hconv hs hd ht
  simp only
  linarith

/-- The envelope is the pointwise maximum of its tangent faces: at every point of the domain the
face pivoting there attains it, and every other tangent face lies below. -/
theorem envelope_is_max_of_faces {E Λ : ℝ → ℝ} {S : Set ℝ} (hconv : ConvexOn ℝ S E)
    (hd : ∀ s ∈ S, HasDerivAt E (-Λ s) s) {t : ℝ} (ht : t ∈ S) :
    IsGreatest ((fun s => (E s + Λ s * s) - Λ s * t) '' S) (E t) := by
  refine ⟨⟨t, ht, by simp only; ring⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact face_below hconv hs (hd s hs) ht

end ChainLegendre
