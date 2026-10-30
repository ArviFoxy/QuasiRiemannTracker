# arvi_primeface: a face proved outside Sil's packing (research, D1 of fresh look 2)

Lean prefix `Submissions.arvi_primeface`, namespace `QRH.ArviPrimeFace`. Mathlib only. The theorems depend
only on `propext`, `Classical.choice` and `Quot.sound` (no `sorry`, `admit`, `axiom` or `native_decide`).

## Why this package exists

Direction D1 (`../../fresh-look/second/directions.md`) asks for the twisted fourth moment of the sextic family,
two plain sums times a zero-forced prime pool, to be diagonal at prime cost Λ ≤ 1.82. That would give
Δθ ≈ −3e-4 and would bypass both of Sil's walls (the K-wall and the root reference). Its first reduction:
- at a prime, the sextic Gauss sum is a conjugate cubic Gauss sum times a Hecke-character factor;
- so prime sums of sextic Gauss sums inherit the Heath-Brown–Patterson cancellation and the Dunn–Radziwiłł
  dispersion of the cubic family.

## Files

| file | content |
|---|---|
| `Duplication.lean` | The quadratic Davenport–Hasse relation over a finite field of odd characteristic. `card_quad_fiber`: #{x : x(1 − x) = b} = η(1 − 4b) + 1, via x ↦ 2x − 1. `jacobiSum_self_eq`: J(χ, χ) = Σ_b χ(b)η(1 − 4b). `chi_four_mul_jacobiSum_self`: χ(4)·J(χ, χ) = J(χ, η). `gaussSum_duplication`: χ(4)·g(χ)g(χη) = g(χ²)g(η), with values in a field and ψ primitive. `sextic_duplication`: if χ³ = η, then χ(4)·g(χ)g(χ⁴) = g(χ²)g(χ³). |

| `RowSplit.lean` | Exponent bookkeeping for splitting the rows of the face Σ_z\|A\|²\|Q\|² by the pool's amplitude class \|Q(z)\|² ≈ ‖a‖²Z^{σs}. `class_le_of_fixPt`: a class at the selected-norm fixed point max(μ, 1 − σ + σμ) is harmless on the ideal face μ + s ≤ 1. `ideal_face_of_fixPt`: fixed points at every slope give the face at Λ = 1. `low_class_excess`, `low_class_excess_le`: with only the full-family bound below slope 1/2, the excess is σs ≤ s/2. So row-splitting proofs of D1 reduce to the K-wall (PR 93 covers σ > 1/2). |

**Reading.** With g(χ⁴) = conj g(χ²) and g(χ²)² = J(χ², χ²)·g(χ⁴), the sextic case gives
g̃₆(π) = χ̄(4)·(J(χ², χ²)/√p)·conj(g̃₃(π))·g̃₂(π) at a split prime π of norm p. This is checked numerically for
p ≤ 109 (`../../fresh-look/second/checks/hd_check.py`, error < 3e-12).

Build: `lake env lean Submissions/arvi_primeface/Duplication.lean` (≈ 8 s on a warm cache).
