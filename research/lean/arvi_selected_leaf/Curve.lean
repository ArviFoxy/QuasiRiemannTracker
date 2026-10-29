/-
The selected-leaf native line, as a continuous curve.

From the end of the native line `G(99999/100000, 5143/2000, 1/10)` (`ArviOdeShape.native_end`), the
selected-leaf native step (`e5_step`, deletion cut `K = 501/1000`, selected fraction `a = 1/250`) is valid
from every face `(B, Λ₀, c(Λ₀))` of the line `c(Λ) = 1/10 + γ (5143/2000 - Λ)` to every face at most
`10⁻⁵` further down. So every face of the line, `Λ ∈ [101/50, 5143/2000]`, is proven by one induction,
given the selected root energy (R1).
-/
import Submissions.arvi_selected_leaf.Step
import Submissions.arvi_selected_leaf.Leaf
import Submissions.arvi_ode_shape.NativeCurve

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf
noncomputable section
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree Set
open OAI.SevenEighths QRH.Record1252270103Source

/-- The selected-leaf line: budget `99999/100000`, cap `c(Λ) = 1/10 + (3/50)(5143/2000 - Λ)`. -/
def sB : ℝ := 99999/100000
def sCap (Λ : ℝ) : ℝ := 1/10 + 3/50 * (5143/2000 - Λ)
def sFace (Λ : ℝ) : Face := ⟨sB, Λ, sCap Λ⟩
def sA : ℝ := 1/250
def sK : ℝ := 501/1000

/-- **The selected-leaf generator**: one step along the line. -/
theorem e5_gates {Λ₀ Λ : ℝ} (hΛ₀ : Λ₀ ∈ Icc (101/50 : ℝ) (5143/2000))
    (hΛ : Λ ∈ Icc (101/50 : ℝ) (5143/2000)) (hlt : Λ < Λ₀) (hle : Λ₀ - Λ ≤ 1/100000) :
    E5Gates (sFace Λ₀) (sFace Λ) sA sK := by
  obtain ⟨a0, a1⟩ := hΛ₀
  obtain ⟨b0, b1⟩ := hΛ
  have hc0 : 1/10 ≤ sCap Λ₀ := by unfold sCap; nlinarith
  have hc1 : sCap Λ₀ ≤ 3/20 := by unfold sCap; nlinarith
  have hc' : sCap Λ = sCap Λ₀ + 3/50 * (Λ₀ - Λ) := by unfold sCap; ring
  have hc'1 : sCap Λ ≤ 3/20 := by unfold sCap; nlinarith
  have hc'0 : 1/10 ≤ sCap Λ := by unfold sCap; nlinarith
  have hL0 : (0:ℝ) < Λ₀ := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < sA - sK * (Λ₀ - Λ + (6 * sB - Λ₀) * sA) / Λ₀
    simp only [sA, sK, sB]; rw [sub_pos, div_lt_iff₀ hL0]; nlinarith
  · show 0 < sCap Λ₀ * (1 - 6 * sA * sCap Λ) - (1 - sA) * sCap Λ
    simp only [sA]; rw [hc']; nlinarith
  · show 0 < Λ - 2 - 9/2 * sA
    simp only [sA]; linarith
  · show 0 < Λ - 1 - 4 * sA
    simp only [sA]; linarith
  · show 0 < 3/2 * Λ - 5/2 - 9/2 * sA
    simp only [sA]; linarith
  · show 0 < 1/6 - (1 + 3/2 * sA) * sCap Λ
    simp only [sA]; nlinarith
  · show 0 < 1 - 6 * sA * sCap Λ
    simp only [sA]; nlinarith
  · show 0 < 1 - sK * (6 * sB - Λ₀) / Λ₀
    simp only [sK, sB]; rw [sub_pos, div_lt_iff₀ hL0]; nlinarith
  · show sB < 1
    simp only [sB]; norm_num
  · show sCap Λ₀ < 1/6
    linarith
  · show 0 < sCap Λ
    linarith
  · show 0 < sA
    simp only [sA]; norm_num
  · show sA < 1
    simp only [sA]; norm_num
  · show Λ < Λ₀
    exact hlt
  · show 0 < sK
    simp only [sK]; norm_num
  · show sK ≤ 3/4
    simp only [sK]; norm_num

/-- The selected leaf for every step of the line, from the selected root energy (R1). -/
theorem line_leaf (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {Λ₀ Λ : ℝ} (hΛ₀ : Λ₀ ∈ Icc (101/50 : ℝ) (5143/2000)) (h : E5Gates (sFace Λ₀) (sFace Λ) sA sK) :
    E5Leaf (sFace Λ₀) (sFace Λ) sA sK h := by
  intro hp
  have hc0 : 0 < sCap Λ₀ := by unfold sCap; nlinarith [hΛ₀.2]
  exact e5_priced_source sK h.K_pos h.K_le hR1 sB Λ₀ (sCap Λ₀) ((1 - 6*sA*sCap Λ)/2) (3 + 1) hβ
    ⟨h.L₀_pos, by simp only [sB]; norm_num, by simp only [sB]; norm_num, hc0⟩
    (by have := h.H; simp only [sFace] at this ⊢; linarith) (by
      have := h.H; have := h.a_pos; have := h.cap_pos; simp only [sFace] at *; nlinarith) hp

/-- **Every face of the selected-leaf line is proven**, from the end of the native line, by one
induction, given the selected root energy (R1). -/
theorem e5_sources (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∀ Λ ∈ Icc (101/50 : ℝ) (5143/2000), GlobalSource sB Λ (sCap Λ) := by
  have htop : GlobalSource sB (5143/2000) (sCap (5143/2000)) := by
    have h := ArviOdeShape.native_end hβ
    have e : sCap (5143/2000) = 1/10 := by unfold sCap; norm_num
    rw [e]; simpa only [sB] using h
  exact ArviOdeShape.curve_induction (fun Λ => GlobalSource sB Λ (sCap Λ))
    (by norm_num : (0:ℝ) < 1/100000) htop
    (fun Λ₀ hΛ₀ Λ hΛ hlt hle hsrc => by
      have hg := e5_gates hΛ₀ hΛ hlt hle
      exact e5_step (p := sFace Λ₀) (n := sFace Λ) hg (line_leaf hR1 hβ hΛ₀ hg) hβ hsrc)

/-- The end of the selected-leaf line: `G(99999/100000, 101/50, c(101/50))`, `c = 1/10 + 3309/100000`. -/
theorem e5_end (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99999/100000) (101/50) (1/10 + 3/50 * (5143/2000 - 101/50)) := by
  have h := e5_sources hR1 hβ (101/50) ⟨le_rfl, by norm_num⟩
  simpa only [sB, sCap] using h

end
end QRH.ArviSelectedLeaf
