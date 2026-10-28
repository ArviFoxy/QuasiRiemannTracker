/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.NaturalUniformNear
import Candidate.Local.Qrh.JointDetector.FineCanonicalFromNorm
import Candidate.Local.Qrh.JointDetector.FinePackedProvider
import Candidate.Local.Qrh.JointDetector.FineSourceChains.Count
import Candidate.Local.Qrh.JointDetector.FineSourceChains.Physical
import Candidate.Local.Qrh.JointDetector.FineReturn.Endpoint
import Submissions.density_split_fine_chain.Source.ChainK15

/-! Canonical composition of the smaller-gap norm, actual detector and
supplier, finite fine source chain and complete physical return. -/
namespace Qrh.JointDetector.FineBestEndpoint
noncomputable section
set_option autoImplicit false
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.Record12518109Source QRH.Record12518109Existence

/-- The certified generic return actually closes at its exact geometry
boundary. This strengthens the requested rounded target without changing
the sources, windows, physical schedule or analytic estimates. -/
theorem best_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (87393379/100000000:ℝ) < s.re) (hpole : ¬ (χ=1 ∧ s=1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  have hn := FineCanonicalFromNorm.actual_norm
    NaturalSelectedNorm.natural_selected_cell_norm
  have hp := FinePackedProvider.provider hn
  have hGC : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record12518109Existence.UniformUnitFaceSource FineReturn.countSourceFace := by
    intro hβ
    exact FineSourceChains.Count.source hp hβ (QRH.SilDensitySplit.K15.final_source hβ)
  have hGP : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record12518109Existence.UniformUnitFaceSource FineReturn.physicalSourceFace := by
    intro hβ
    exact FineSourceChains.Physical.source hp hβ (QRH.SilDensitySplit.K15.final_source hβ)
  exact Cycle25.dirichlet_of_hecke (θ := FineReturn.theta)
    (by norm_num [FineReturn.theta]) (FineReturn.hecke_nonvanishing hGC hGP)
    χ s (by simpa only [FineReturn.theta] using hs) hpole

theorem bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4369669/5000000:ℝ) < s.re) (hpole : ¬ (χ=1 ∧ s=1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  have hn := FineCanonicalFromNorm.actual_norm
    NaturalSelectedNorm.natural_selected_cell_norm
  have hp := FinePackedProvider.provider hn
  apply FineReturn.bound (hGC := ?_) (hGP := ?_) χ hs hpole
  · intro hβ
    exact FineSourceChains.Count.source hp hβ (QRH.SilDensitySplit.K15.final_source hβ)
  · intro hβ
    exact FineSourceChains.Physical.source hp hβ (QRH.SilDensitySplit.K15.final_source hβ)

end
end Qrh.JointDetector.FineBestEndpoint

#print axioms Qrh.JointDetector.FineBestEndpoint.bound
#print axioms Qrh.JointDetector.FineBestEndpoint.best_bound
