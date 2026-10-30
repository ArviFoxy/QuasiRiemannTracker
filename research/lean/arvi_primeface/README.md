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

| `Dispersion.lean` | `pool_expand`: Σ_z b(z)\|Σ_P a_Pψ_P(z)\|² = Σ_{P,P'} a_P ā_{P'}·T(P, P'). **`dispersion`**: if the twisted moments obey a large sieve Σ_{P≠P'}\|Σ_z c(z)ψ_P conj ψ_{P'}\|² ≤ Δ·Σ\|c\|² (Huxley over Q(ω): Δ ≪ Z + P₀⁴), then Σ_z b(z)\|Q(z)\|² ≤ ‖a‖²·(Σ_z b + √(Δ·Σ_z b²)). With b = Φ\|A\|², the last term is the plain eighth moment. |

| `Dismissed.lean` | Exponent bookkeeping for dismissed routes. `holder_loses` and `holder_worse_than_trivial`: Hölder decoupling with p ≤ 1/(2s) loses ≥ 2sμ, worse than the trivial s once μ > 1/2. `interpolation_loses`: interpolation through a pointwise bound beats the trivial loss only if τ < 1/2. `bootstrap_rule_loses` and `bootstrap_rule_loss_pos`: the pointwise bootstrap rule loses (2β − 1 − δ)m in the binding regime. |
| `Exponents.lean` | `label_line_optimal`: υ = 1/2 minimizes the Hölder label price iff d ≥ y. `label_pointwise_worse`: at the newTop binding the pointwise bootstrap price stays above it for every υ ≥ 1 − β. `dr_diagonal_iff` and `dr_slot_cost`: Dunn–Radziwiłł's five terms are diagonal exactly for log_A B ≤ 3/5, i.e. slot cost 5/3. `kwall_corner`: the K-wall corner condition γ ≤ δ(1 − X). |

**Reading.** With g(χ⁴) = conj g(χ²) and g(χ²)² = J(χ², χ²)·g(χ⁴), the sextic case gives
g̃₆(π) = χ̄(4)·(J(χ², χ²)/√p)·conj(g̃₃(π))·g̃₂(π) at a split prime π of norm p. This is checked numerically for
p ≤ 109 (`../../fresh-look/second/checks/hd_check.py`, error < 3e-12).

Build: `lake env lean Submissions/arvi_primeface/Duplication.lean` (≈ 8 s on a warm cache).
