/-
The native bootstrap as a continuous curve.

From PR 76's fourth-power source `G(99999/100000, 93/25, 3/50)` (`face0_source`), the native cube-free step
(`K15.nativeStep`) is valid from every face `(B, Λ₀, c(Λ₀))` of the line `c(Λ) = 3/50 + (80/2297)(93/25 - Λ)` to
every face at most `10⁻⁵` further down, with the selection `a = 1/10`. So every face of the line,
`Λ ∈ [5143/2000, 93/25]`, is proven by one induction; at `Λ = 5143/2000` the cap is `1/10`.
-/
import Submissions.arvi_ode_shape.Induction
import Submissions.sil_density_split_20261026.Source.Assembly
import Submissions.sil_density_split_20261026.CubeFree.Assembly.Provider
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderGeoSupply
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9

set_option autoImplicit false

namespace QRH.ArviOdeShape
open Set OAI OAI.SevenEighths QRH.SilDensitySplit

/-- Sil's generic native step with the diagonal supplier (as in PR 86's `ChainK15.nativeStep`). -/
theorem nativeInputs : CubeFree.NativeInputs := fun _ _ _ h =>
  ⟨4, CubeFree.Assembly.step_inputs_of_provider _ _ 4 (fun _ hleaf =>
    CubeFree.Second.Provider.contrary_raw_side_provider (CubeFree.stepGates_of_native h) 4 le_rfl hleaf
      (CubeFree.Second.ProviderDiag.diag_supply _))⟩

theorem nativeStep : NativeStepStatement :=
  fun p n a h hβ hp => CubeFree.native_step nativeInputs p n a h hβ hp

/-- The native line: budget `99999/100000`, cap `c(Λ) = 3/50 + (80/2297)(93/25 - Λ)`. -/
noncomputable def nB : ℝ := 99999/100000
noncomputable def nCap (Λ : ℝ) : ℝ := 3/50 + 80/2297 * (93/25 - Λ)
noncomputable def nFace (Λ : ℝ) : Face := ⟨nB, Λ, nCap Λ⟩

/-- **The native generator**: one native step along the line, for every parent `Λ₀ ∈ [5143/2000, 93/25]` and
every step `0 < h ≤ 10⁻⁵` with the child on the line. -/
theorem native_gates {Λ₀ Λ : ℝ} (hΛ₀ : Λ₀ ∈ Icc (5143/2000 : ℝ) (93/25)) (hΛ : Λ ∈ Icc (5143/2000 : ℝ) (93/25))
    (hlt : Λ < Λ₀) (hle : Λ₀ - Λ ≤ 1/100000) : NativeGates (nFace Λ₀) (nFace Λ) (1/10) := by
  obtain ⟨a0, a1⟩ := hΛ₀
  obtain ⟨b0, b1⟩ := hΛ
  have hc0 : 3/50 ≤ nCap Λ₀ := by unfold nCap; nlinarith
  have hc1 : nCap Λ₀ ≤ 1/10 := by unfold nCap; nlinarith
  have hc' : nCap Λ = nCap Λ₀ + 80/2297 * (Λ₀ - Λ) := by unfold nCap; ring
  have hc'1 : nCap Λ ≤ 1/10 := by unfold nCap; nlinarith
  have hc'0 : 3/50 ≤ nCap Λ := by unfold nCap; nlinarith
  have hL0 : (0:ℝ) < Λ₀ := by linarith
  have g1 : 0 < (1/10 : ℝ) - nativeK * (Λ₀ - Λ + (6 * nB - Λ₀) * (1/10)) / Λ₀ := by
    simp only [nB, nativeK]; rw [sub_pos, div_lt_iff₀ hL0]; nlinarith
  have g2 : 0 < nCap Λ₀ * (1 - 6 * (1/10) * nCap Λ) - (1 - 1/10) * nCap Λ := by rw [hc']; nlinarith
  have g6 : 0 < (1/6 : ℝ) - (1 + 3/2 * (1/10)) * nCap Λ := by nlinarith
  have g7 : 0 < (1 : ℝ) - 6 * (1/10) * nCap Λ := by nlinarith
  have g8 : 0 < (1 : ℝ) - nativeK * (6 * nB - Λ₀) / Λ₀ := by
    simp only [nB, nativeK]; rw [sub_pos, div_lt_iff₀ hL0]; nlinarith
  have g9 : nCap Λ₀ < 1/6 := by linarith
  exact ⟨g1, g2, by simp only [nFace]; linarith, by simp only [nFace]; linarith,
    by simp only [nFace]; linarith, g6, g7, g8, le_rfl, by simp only [nFace, nB]; norm_num, g9,
    by simp only [nFace]; linarith, by norm_num, hlt⟩

/-- **Every face of the native line is proven**, from the fourth-power source, by one induction. -/
theorem native_sources (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∀ Λ ∈ Icc (5143/2000 : ℝ) (93/25), (nFace Λ).Source := by
  have htop : (nFace (93/25)).Source := by
    have h := face0_source hβ
    have e : nFace (93/25) = face0 := by
      simp only [nFace, nB, nCap, face0]; norm_num
    rw [e]; exact h
  exact curve_induction (fun Λ => (nFace Λ).Source) (by norm_num : (0:ℝ) < 1/100000) htop
    (fun Λ₀ hΛ₀ Λ hΛ hlt hle hsrc => nativeStep _ _ _ (native_gates hΛ₀ hΛ hlt hle) hβ hsrc)

/-- The end of the native line: `G(99999/100000, 5143/2000, 1/10)`. -/
theorem native_end (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    QRH.Record1252270103Source.GlobalSource (99999/100000) (5143/2000) (1/10) := by
  have h := native_sources hβ (5143/2000) ⟨le_rfl, by norm_num⟩
  have e : nCap (5143/2000) = 1/10 := by unfold nCap; norm_num
  simpa only [Face.Source, nFace, nB, e] using h

end QRH.ArviOdeShape

#print axioms QRH.ArviOdeShape.native_end
