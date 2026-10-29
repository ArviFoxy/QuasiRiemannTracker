/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.FineReturn.Geometry
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows

import Candidate.Local.Qrh.JointDetector.FinePhysical.PhysicalDirect.ChosenSource
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.IncumbentInput
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract

/-!
# Canonical .87393380 return from explicit source providers

This instantiates the admitted generic physical return at new signal geometry,
using the newly instantiated mixed count scheme and rational geometry.
Both complete source providers are explicit; the return and all certificates are closed.
The analytic source and return machinery is due to OpenAI, Hailey Collet,
Sil and ArviFoxy. Two full source providers are explicit premises here.
-/

namespace Qrh.JointDetector.FineReturn

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

open QRH.Record1252270103Return
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

local instance : Geometry.Parameters := parameters
local instance : Qrh.JointDetector.FinePhysical.Return.Geometry.BoundsN := bounds
local instance : CountScheme := finalCountScheme

/-- One fixed conductor schedule, certified at the new reference kappa. -/
@[instance_reducible] def physicalSchedule :
    Qrh.JointDetector.FinePhysical.Return.GenericArithmetic.PhysicalSchedule where
  cap := numeratorCap
  cap_nonneg := by norm_num [numeratorCap]
  cap_lt_fifth := by norm_num [numeratorCap]
  dMinus := dm
  physicalB := physicalB
  physicalLambda := physicalLambda
  dMinus_lower := by norm_num [dm]
  dMinus_before_top := by
    change dm ≤ @Geometry.dPlus parameters
    rw [parameters_dPlus]
    norm_num [dm, dp, h]
  y_before_switch := by
    change y < dm
    norm_num [y, ell, theta, h, dm]
  switch_before_twoy := by
    change dm < 2 * y
    norm_num [dm, y, ell, theta, h]
  lambda_bounds := by norm_num [physicalLambda]
  B_bounds := by norm_num [physicalB]
  small_plain_global := by norm_num [physicalB, physicalLambda, numeratorCap]
  prime_supply := by
    change (1/5 : ℝ) < ell / (@Geometry.dPlus parameters)
    rw [parameters_dPlus]
    norm_num [ell, theta, dp, h]
  incumbent := by
    change kappa ≤ (9/2 : ℝ) / 6
    norm_num [kappa, theta]
  old_rows := by
    intro d δ p hd hδ hp
    exact Qrh.JointDetector.FineReturn.old_rows hd hδ hp
  new_rows := by
    intro d δ p hd hδ hp
    have hd' : d ∈ Set.Icc dm dp := by
      simpa only [Qrh.JointDetector.FinePhysical.Return.GenericArithmetic.dp, parameters_dPlus] using hd
    exact Qrh.JointDetector.FineReturn.new_rows hd' hδ hp

local instance : Qrh.JointDetector.FinePhysical.Return.GenericArithmetic.PhysicalSchedule := physicalSchedule

abbrev countSourceFace : SourceFace :=
  QRH.Record1252270103Source.globalFace countCB countCL (1/10)
abbrev physicalSourceFace : SourceFace :=
  QRH.Record1252270103Source.globalFace physicalB physicalLambda (1/10)

private theorem source_restricts_count :
    countSourceFace.Restricts countGlobal := by
  constructor <;> norm_num [countSourceFace, QRH.Record1252270103Source.globalFace,
    countGlobal, QRH.Record1252270103Return.globalFace,
    countCB, countCL,
    countCap]

private theorem source_restricts_count_physical :
    physicalSourceFace.Restricts physicalGlobal := by
  constructor <;> norm_num [physicalSourceFace, QRH.Record1252270103Source.globalFace,
    physicalGlobal, QRH.Record1252270103Return.globalFace,
    physicalB, physicalLambda,
    physicalCap,countCap]

private theorem source_restricts_physical :
    physicalSourceFace.Restricts
      Qrh.JointDetector.FinePhysical.Return.GenericPhysical.PhysicalDirect.physicalFace := by
  change physicalSourceFace.Restricts ⟨physicalB, physicalLambda, 0, 1/2, 0, numeratorCap⟩
  constructor <;> norm_num [physicalSourceFace, QRH.Record1252270103Source.globalFace,
    QRH.Record1252270103Return.globalFace, physicalB, physicalLambda, numeratorCap]

private theorem uniform_restrict {strong weak : SourceFace}
    (h : strong.Restricts weak) (hs : UniformUnitFaceSource strong) :
    UniformUnitFaceSource weak := by
  intro ε hε
  obtain ⟨mesh, hm, hnorm⟩ := hs ε hε
  exact ⟨mesh, hm, unit_source_restrict h hnorm⟩

private theorem natural_cap :
    2 * HeckeZeroSupremum.beta - 1 ≤
      finalCountScheme.naturalκ := by
  have hi := Candidate.FourthPower.IncumbentInput.native_kappa_bound
  change 2 * HeckeZeroSupremum.beta - 1 ≤ (9/2 : ℝ) / 6
  linarith

variable (hGC : (51/100:ℝ) ≤ HeckeZeroSupremum.beta → UniformUnitFaceSource countSourceFace)
  (hGP : (51/100:ℝ) ≤ HeckeZeroSupremum.beta → UniformUnitFaceSource physicalSourceFace)
include hGC hGP

/-- The actual initial-source contract at the new endpoint and one common mesh. -/
theorem chosen_initial_source :
    Qrh.JointDetector.FinePhysical.Return.GenericPhysical.PhysicalDirect.ChosenInitialSourceInput := by
  intro hgap
  have hgap' : theta < HeckeZeroSupremum.beta := hgap
  have hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta := by
    have ht : (51/100 : ℝ) < theta := by norm_num [theta]
    linarith
  have hC := uniform_restrict source_restricts_count (hGC hβ)
  have hP := uniform_restrict source_restricts_count_physical (hGP hβ)
  have hcount : ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧
      ∀ w ∈ finalCountScheme.windows,
        UnitFaceSource w.face mesh ε := by
    intro ε hε
    exact final_windows_common_mesh hC hP hε
  have hphysical := uniform_restrict source_restricts_physical (hGP hβ)
  exact (Qrh.JointDetector.FinePhysical.Return.GenericPhysical.PhysicalDirect.chosen_initial_source_of_uniform_faces
    natural_cap hcount hphysical) hgap

/-- Full generic numerator and feedback closure from the explicit selected norm. -/
theorem beta_le_theta : HeckeZeroSupremum.beta ≤ theta :=
  Qrh.JointDetector.FinePhysical.Return.GenericPhysical.PhysicalDirect.beta_le_theta_of_initial_source
    (chosen_initial_source hGC hGP)

theorem hecke_nonvanishing (χ : Character) (s : ℂ)
    (hs : theta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ ((beta_le_theta hGC hGP).trans_lt hs) hpole

/-- Every positive modulus and every Dirichlet character, with the principal pole excluded. -/
theorem dirichlet_nonvanishing {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4369669/5000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Cycle25.dirichlet_of_hecke (θ := theta) (by norm_num [theta])
    (hecke_nonvanishing hGC hGP) χ s (by norm_num [theta]; linarith [hs]) hpole

theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4369669/5000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  dirichlet_nonvanishing hGC hGP χ hs hpole

end

end Qrh.JointDetector.FineReturn

#print axioms Qrh.JointDetector.FineReturn.bound
