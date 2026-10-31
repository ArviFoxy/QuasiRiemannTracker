/-
SKETCH package (see `Polar.lean`). No `sorry`; nothing is assumed in this file.

**The two walls at the bar's face, as scalar gates of the selected-leaf line.**

The banked line (`QRH.ArviBank.e5_gates`) stops at `Λ = 2.0001` for two reasons:
* the **overshoot** gate `0 < 1 − K(6B − Λ₀)/Λ₀`, i.e. `Λ₀ > 6BK/(1 + K)`, which is `≈ 2` at the banked cut
  `K = 0.500001` (the K-wall);
* the **principal** gate `0 < Λ − 2 − 9a/2`, the first clause of Sil's `ReferenceAt` (the reference wall).

**The reference wall is a constant, not a slope.** In `CubeFree/RootParameters.lean` the centred root exponent must
lie below `upperOne = (P − S − 1/2)/2`, where `1/2` is the short reference's threshold (its sieve is diagonal for
`B ≤ A^{1/2}`). With a threshold `γ` the endpoint is `(P − S − (1 − γ))/2`; the interval condition becomes
`P + 2S + 9u/2 < 3/4 + γ/2`, and with the face relation `P + L S ≤ B` the first clause of the reserves reads
`(3/4 + γ/2 − B) + (L − 2) S − (9/2) sel S` (`ReferenceAtγ`). The `2` in front of `S` does not move; the extra
`(γ − 1/2)/2` pays for `(2 − L)·cap` at faces below 2.

**What this file proves (scalar only).** Along the banked line's cap `c(Λ) = 1/10 + (3/50)(5143/2000 − Λ)`, with the
cut `K₀ = 0.4869` and threshold `γ₀ = 0.51`, every step of length `≤ 1/400000000` between faces in
`[1.965, 5143/2000]` satisfies the gates (`walls_gates`), and Sil's reserves hold with the `γ₀`-reference
(`walls_reference`). At `Λ = 1.965` the float model of the newTop row (`h = 0.8097`) gives `θ* = 0.87332836`,
`3.6e-6` below the bar.

**What it does not prove.** That such steps exist. That needs:
* R1 at `K₀` (`RootEnergyFrom.selectedRootEnergy_of_cellNormFrom` reduces it to the cell norm at slopes `≥ 0.4869`);
* Sil's root reference forked to `ReferenceAtγ`, with the short reference diagonal for `B ≤ A^{0.51}` on its
  vectors (input B, a small case of target 2);
* the ledger's two uses of `principal`, which need only `selOne` and `selTwo` below (a small fork of `e5_ledger`).
-/
import Submissions.arvi_bank.Curve

set_option autoImplicit false
namespace QRH.ArviPolarSketch.Walls
noncomputable section
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree Set QRH.ArviSelectedLeaf QRH.ArviBank

/-- Sil's reference reserves (`ReferenceAt`) with the short-reference threshold `γ` in place of `1/2`: the first
clause's constant `1 − B` becomes `3/4 + γ/2 − B`. -/
def ReferenceAtγ (D : StepData) (γ ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ ε > 0, ∀ S, D.s₀ ≤ S → S ≤ D.c →
    ρ ≤ (3/4 + γ/2 - D.B) + (D.L-2)*S - 9/2*D.sel ε S ∧
    ρ ≤ 1/20 + 3/2*(1-D.B) + (3/2*D.L-5/2)*S - 9/2*D.sel ε S ∧
    ρ ≤ (1-D.B) + (D.L-1)*S - 4*D.sel ε S ∧
    ρ ≤ 1/3 - 2*S - 3*D.sel ε S

/-- At `γ = 1/2` the reserves are Sil's. -/
theorem referenceAtγ_half (D : StepData) (ρ : ℝ) : ReferenceAtγ D (1/2) ρ ↔ ReferenceAt D ρ := by
  have e : (3/4 + (1/2:ℝ)/2 - D.B) = 1 - D.B := by ring
  unfold ReferenceAtγ ReferenceAt
  rw [e]

/-- The step data of a selected-leaf native step (`e5Data` without the gates). -/
def wallData (p n : Face) (a K : ℝ) (hK : 0 ≤ K) (hL₀ : 0 < p.L) : StepData where
  B₀ := p.B
  L₀ := p.L
  c₀ := p.c
  B := n.B
  L := n.L
  c := n.c
  κ := 3/4
  s₀ := 0
  Hmin := (1 - 6*a*n.c)/2
  Hmax := 3
  sel := fun _ w => a * w
  price := e5Price K p.B p.L p.c hK hL₀

/-- The gates of one step past both walls: `E5Gates` with `principal` replaced by the `γ`-reference at both ends
of `S ∈ [0, c]`, plus the two consequences of `principal` that the ledger's selected branch uses. -/
structure WallGates (p n : Face) (a K γ : ℝ) : Prop where
  retention : 0 < a - K * (p.L - n.L + (6*p.B - p.L)*a) / p.L
  cap : 0 < p.c*(1 - 6*a*n.c) - (1-a)*n.c
  refZero : 0 < 3/4 + γ/2 - n.B
  refCap : 0 < (3/4 + γ/2 - n.B) + (n.L - 2 - 9/2*a)*n.c
  selOne : 4*a < n.L - 1
  selTwo : 14/5*a < 4/5*n.L - 1
  secondRef : 0 < 3/2*n.L - 5/2 - 9/2*a
  refPos : 0 < 1/6 - (1+3/2*a)*n.c
  H : 0 < 1 - 6*a*n.c
  overshoot : 0 < 1 - K*(6*p.B - p.L)/p.L
  B_le : n.B ≤ p.B
  B_lt : p.B < 1
  cap_lt : p.c < 1/6
  cap_pos : 0 < n.c
  a_pos : 0 < a
  a_lt : a < 1
  L_lt : n.L < p.L
  K_pos : 0 < K
  K_le : K ≤ 3/4

/-- The cut of the walls' line. -/
def wK : ℝ := 4869/10000
/-- The short-reference threshold of the walls' line. -/
def wγ : ℝ := 51/100

/-- **The walls' line**: every step of length `≤ 1/400000000` between faces of the banked cap line in
`[1.965, 5143/2000]` passes the gates at `K₀ = 0.4869`, `γ₀ = 0.51`. -/
theorem walls_gates {Λ₀ Λ : ℝ} (hΛ₀ : Λ₀ ∈ Icc (393/200 : ℝ) (5143/2000))
    (hΛ : Λ ∈ Icc (393/200 : ℝ) (5143/2000)) (hlt : Λ < Λ₀) (hle : Λ₀ - Λ ≤ 1/400000000) :
    WallGates (sFace Λ₀) (sFace Λ) sA wK wγ := by
  obtain ⟨a0, a1⟩ := hΛ₀
  obtain ⟨b0, b1⟩ := hΛ
  have hc0 : 1/10 ≤ sCap Λ₀ := sCap_ge a1
  have hc1 : sCap Λ₀ ≤ 3/20 := by unfold sCap; linarith only [a0]
  have hcy0 : 1/10 ≤ sCap Λ := sCap_ge b1
  have hcy1 : sCap Λ ≤ 3/20 := by unfold sCap; linarith only [b0]
  have hL0 : (0:ℝ) < Λ₀ := by linarith only [a0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < sA - wK * (Λ₀ - Λ + (6 * sB - Λ₀) * sA) / Λ₀
    unfold sA wK sB; rw [sub_pos, div_lt_iff₀ hL0]; linarith only [a0, hle]
  · show 0 < sCap Λ₀ * (1 - 6 * sA * sCap Λ) - (1 - sA) * sCap Λ
    rw [sCap_step Λ₀ Λ]
    exact cap_gate_aux hc0 hc1 (sub_nonneg.2 hlt.le) hle
  · show 0 < 3/4 + wγ/2 - sB
    unfold wγ sB; norm_num
  · show 0 < (3/4 + wγ/2 - sB) + (Λ - 2 - 9/2*sA) * sCap Λ
    unfold wγ sB sA sCap
    nlinarith [mul_nonneg (sub_nonneg.2 b0) (sub_nonneg.2 b1)]
  · show 4 * sA < Λ - 1
    unfold sA; linarith only [b0]
  · show 14/5 * sA < 4/5 * Λ - 1
    unfold sA; linarith only [b0]
  · show 0 < 3/2 * Λ - 5/2 - 9/2 * sA
    unfold sA; linarith only [b0]
  · show 0 < 1/6 - (1 + 3/2 * sA) * sCap Λ
    unfold sA; linarith only [hcy1]
  · show 0 < 1 - 6 * sA * sCap Λ
    unfold sA; linarith only [hcy1]
  · show 0 < 1 - wK * (6 * sB - Λ₀) / Λ₀
    unfold wK sB; rw [sub_pos, div_lt_iff₀ hL0]; linarith only [a0]
  · show sB < 1
    unfold sB; norm_num
  · show sCap Λ₀ < 1/6
    linarith only [hc1]
  · show 0 < sCap Λ
    linarith only [hcy0]
  · show 0 < sA
    unfold sA; norm_num
  · show sA < 1
    unfold sA; norm_num
  · show Λ < Λ₀
    exact hlt
  · show 0 < wK
    unfold wK; norm_num
  · show wK ≤ 3/4
    unfold wK; norm_num

theorem WallGates.L₀_pos {p n : Face} {a K γ : ℝ} (h : WallGates p n a K γ) : 0 < p.L := by
  have := h.selOne; have := h.L_lt; have := h.a_pos; linarith

/-- **The reserves past the reference wall.** Under the gates, Sil's reserves hold with the `γ`-reference, with
reserve the least of the first clause at `S = 0` and `S = c`, `1 − B`, and `1/3 − (2 + 3a)c`. -/
theorem walls_reference {p n : Face} {a K γ : ℝ} (h : WallGates p n a K γ) :
    ReferenceAtγ (wallData p n a K h.K_pos.le h.L₀_pos) γ
      (min (min (3/4 + γ/2 - n.B) ((3/4 + γ/2 - n.B) + (n.L - 2 - 9/2*a)*n.c))
        (min (1 - n.B) (1/3 - (2 + 3*a)*n.c))) := by
  have hB : n.B < 1 := lt_of_le_of_lt h.B_le h.B_lt
  have hr0 := h.refZero
  have hrc := h.refCap
  have hsr := h.secondRef
  have hs1 := h.selOne
  have hrp := h.refPos
  have ha := h.a_pos
  have hc := h.cap_pos
  refine ⟨lt_min (lt_min hr0 hrc) (lt_min (by linarith) (by nlinarith)), ?_⟩
  intro ε _ S hS0 hSc
  simp only [wallData] at hS0 hSc ⊢
  set r0 := 3/4 + γ/2 - n.B
  have m1 : min (min r0 (r0 + (n.L - 2 - 9/2*a)*n.c)) (min (1 - n.B) (1/3 - (2 + 3*a)*n.c)) ≤
      min r0 (r0 + (n.L - 2 - 9/2*a)*n.c) := min_le_left _ _
  have m2 : min (min r0 (r0 + (n.L - 2 - 9/2*a)*n.c)) (min (1 - n.B) (1/3 - (2 + 3*a)*n.c)) ≤
      min (1 - n.B) (1/3 - (2 + 3*a)*n.c) := min_le_right _ _
  have m11 := min_le_left r0 (r0 + (n.L - 2 - 9/2*a)*n.c)
  have m12 := min_le_right r0 (r0 + (n.L - 2 - 9/2*a)*n.c)
  have m21 := min_le_left (1 - n.B) (1/3 - (2 + 3*a)*n.c)
  have m22 := min_le_right (1 - n.B) (1/3 - (2 + 3*a)*n.c)
  have e2 : 0 ≤ (3/2*n.L - 5/2 - 9/2*a)*S := mul_nonneg hsr.le hS0
  have e3 : 0 ≤ (n.L - 1 - 4*a)*S := mul_nonneg (by linarith) hS0
  have e4 : (2 + 3*a)*S ≤ (2 + 3*a)*n.c := mul_le_mul_of_nonneg_left hSc (by linarith)
  refine ⟨?_, by nlinarith, by nlinarith, by nlinarith⟩
  -- the first clause is linear in `S`: its least value on `[0, c]` is at an end
  rcases le_total 0 (n.L - 2 - 9/2*a) with hpos | hneg
  · have := mul_nonneg hpos hS0
    nlinarith
  · have := mul_le_mul_of_nonpos_left hSc hneg
    nlinarith

/-- The end face of the walls' line: `(B, Λ, c) = (0.99999, 1.965, c(1.965))`, `c(1.965) = 0.13639`. -/
theorem walls_end_cap : sCap (393/200) = 1/10 + 3/50 * (5143/2000 - 393/200) := rfl

end
end QRH.ArviPolarSketch.Walls

#print axioms QRH.ArviPolarSketch.Walls.walls_gates
#print axioms QRH.ArviPolarSketch.Walls.walls_reference
#print axioms QRH.ArviPolarSketch.Walls.referenceAtγ_half
