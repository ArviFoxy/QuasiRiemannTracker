/- Copyright (c) 2026 Sil (layout and generic theorems, Apache-2.0); step instances for the 46-step density-split chain, 27 Oct 2026.
Exact scalar chain of 30 explicit native cube-free steps (Sil's `NativeGates`, Source/NativeBootstrap.lean)
G(99999/100000, 93/25, 3/50) -> G('99999/100000', '642867/250000', '69859/500000'), then Sil's literal subface step to G('99999/100000', '5143/2000', '1397/10000').
Arithmetic only: the analytic step is a hypothesis of `bootstrapK15`. -/
import Submissions.sil_density_split_20261026.Source.NativeBootstrap

set_option autoImplicit false
namespace QRH.SilDensitySplit.K15
noncomputable section
open QRH.SilDensitySplit

def nface00 : Face := face0
def nface01 : Face := ⟨(99999 / 100000 : ℝ), (169997 / 50000 : ℝ), (64369 / 1000000 : ℝ)⟩
def nface02 : Face := ⟨(99999 / 100000 : ℝ), (1584533 / 500000 : ℝ), (3441 / 50000 : ℝ)⟩
def nface03 : Face := ⟨(99999 / 100000 : ℝ), (1501263 / 500000 : ℝ), (18331 / 250000 : ℝ)⟩
def nface04 : Face := ⟨(99999 / 100000 : ℝ), (2882393 / 1000000 : ℝ), (1557 / 20000 : ℝ)⟩
def nface05 : Face := ⟨(99999 / 100000 : ℝ), (559147 / 200000 : ℝ), (41183 / 500000 : ℝ)⟩
def nface06 : Face := ⟨(99999 / 100000 : ℝ), (109329 / 40000 : ℝ), (2171 / 25000 : ℝ)⟩
def nface07 : Face := ⟨(99999 / 100000 : ℝ), (2688133 / 1000000 : ℝ), (91243 / 1000000 : ℝ)⟩
def nface08 : Face := ⟨(99999 / 100000 : ℝ), (1327803 / 500000 : ℝ), (47773 / 500000 : ℝ)⟩
def nface09 : Face := ⟨(99999 / 100000 : ℝ), (2632143 / 1000000 : ℝ), (99723 / 1000000 : ℝ)⟩
def nface10 : Face := ⟨(99999 / 100000 : ℝ), (1307609 / 500000 : ℝ), (12969 / 125000 : ℝ)⟩
def nface11 : Face := ⟨(99999 / 100000 : ℝ), (2603009 / 1000000 : ℝ), (53807 / 500000 : ℝ)⟩
def nface12 : Face := ⟨(99999 / 100000 : ℝ), (1297101 / 500000 : ℝ), (55647 / 500000 : ℝ)⟩
def nface13 : Face := ⟨(99999 / 100000 : ℝ), (2587849 / 1000000 : ℝ), (114781 / 1000000 : ℝ)⟩
def nface14 : Face := ⟨(99999 / 100000 : ℝ), (2583267 / 1000000 : ℝ), (118067 / 1000000 : ℝ)⟩
def nface15 : Face := ⟨(99999 / 100000 : ℝ), (1289981 / 500000 : ℝ), (121147 / 1000000 : ℝ)⟩
def nface16 : Face := ⟨(99999 / 100000 : ℝ), (2577577 / 1000000 : ℝ), (124021 / 1000000 : ℝ)⟩
def nface17 : Face := ⟨(99999 / 100000 : ℝ), (2575857 / 1000000 : ℝ), (126691 / 1000000 : ℝ)⟩
def nface18 : Face := ⟨(99999 / 100000 : ℝ), (321827 / 125000 : ℝ), (129161 / 1000000 : ℝ)⟩
def nface19 : Face := ⟨(99999 / 100000 : ℝ), (2573721 / 1000000 : ℝ), (131437 / 1000000 : ℝ)⟩
def nface20 : Face := ⟨(99999 / 100000 : ℝ), (643269 / 250000 : ℝ), (133527 / 1000000 : ℝ)⟩
def nface21 : Face := ⟨(99999 / 100000 : ℝ), (257261 / 100000 : ℝ), (1693 / 12500 : ℝ)⟩
def nface22 : Face := ⟨(99999 / 100000 : ℝ), (1286137 / 500000 : ℝ), (68593 / 500000 : ℝ)⟩
def nface23 : Face := ⟨(99999 / 100000 : ℝ), (40188 / 15625 : ℝ), (5551 / 40000 : ℝ)⟩
def nface24 : Face := ⟨(99999 / 100000 : ℝ), (2571857 / 1000000 : ℝ), (69859 / 500000 : ℝ)⟩
def nface25 : Face := ⟨(99999 / 100000 : ℝ), (2571731 / 1000000 : ℝ), (69859 / 500000 : ℝ)⟩
def nface26 : Face := ⟨(99999 / 100000 : ℝ), (64291 / 25000 : ℝ), (69859 / 500000 : ℝ)⟩
def nface27 : Face := ⟨(99999 / 100000 : ℝ), (1285787 / 500000 : ℝ), (69859 / 500000 : ℝ)⟩
def nface28 : Face := ⟨(99999 / 100000 : ℝ), (2571527 / 1000000 : ℝ), (69859 / 500000 : ℝ)⟩
def nface29 : Face := ⟨(99999 / 100000 : ℝ), (2571493 / 1000000 : ℝ), (69859 / 500000 : ℝ)⟩
def nface30 : Face := ⟨(99999 / 100000 : ℝ), (642867 / 250000 : ℝ), (69859 / 500000 : ℝ)⟩
def bootFace : Face := ⟨(99999 / 100000 : ℝ), (5143 / 2000 : ℝ), (1397 / 10000 : ℝ)⟩

theorem ngates00 : NativeGates nface00 nface01 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface00, nface01, face0, nativeK]
theorem ngates01 : NativeGates nface01 nface02 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface01, nface02, face0, nativeK]
theorem ngates02 : NativeGates nface02 nface03 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface02, nface03, face0, nativeK]
theorem ngates03 : NativeGates nface03 nface04 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface03, nface04, face0, nativeK]
theorem ngates04 : NativeGates nface04 nface05 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface04, nface05, face0, nativeK]
theorem ngates05 : NativeGates nface05 nface06 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface05, nface06, face0, nativeK]
theorem ngates06 : NativeGates nface06 nface07 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface06, nface07, face0, nativeK]
theorem ngates07 : NativeGates nface07 nface08 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface07, nface08, face0, nativeK]
theorem ngates08 : NativeGates nface08 nface09 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface08, nface09, face0, nativeK]
theorem ngates09 : NativeGates nface09 nface10 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface09, nface10, face0, nativeK]
theorem ngates10 : NativeGates nface10 nface11 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface10, nface11, face0, nativeK]
theorem ngates11 : NativeGates nface11 nface12 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface11, nface12, face0, nativeK]
theorem ngates12 : NativeGates nface12 nface13 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface12, nface13, face0, nativeK]
theorem ngates13 : NativeGates nface13 nface14 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface13, nface14, face0, nativeK]
theorem ngates14 : NativeGates nface14 nface15 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface14, nface15, face0, nativeK]
theorem ngates15 : NativeGates nface15 nface16 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface15, nface16, face0, nativeK]
theorem ngates16 : NativeGates nface16 nface17 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface16, nface17, face0, nativeK]
theorem ngates17 : NativeGates nface17 nface18 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface17, nface18, face0, nativeK]
theorem ngates18 : NativeGates nface18 nface19 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface18, nface19, face0, nativeK]
theorem ngates19 : NativeGates nface19 nface20 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface19, nface20, face0, nativeK]
theorem ngates20 : NativeGates nface20 nface21 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface20, nface21, face0, nativeK]
theorem ngates21 : NativeGates nface21 nface22 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface21, nface22, face0, nativeK]
theorem ngates22 : NativeGates nface22 nface23 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface22, nface23, face0, nativeK]
theorem ngates23 : NativeGates nface23 nface24 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface23, nface24, face0, nativeK]
theorem ngates24 : NativeGates nface24 nface25 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface24, nface25, face0, nativeK]
theorem ngates25 : NativeGates nface25 nface26 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface25, nface26, face0, nativeK]
theorem ngates26 : NativeGates nface26 nface27 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface26, nface27, face0, nativeK]
theorem ngates27 : NativeGates nface27 nface28 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface27, nface28, face0, nativeK]
theorem ngates28 : NativeGates nface28 nface29 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface28, nface29, face0, nativeK]
theorem ngates29 : NativeGates nface29 nface30 (120629 / 1000000 : ℝ) := by
  constructor <;> norm_num [nface29, nface30, face0, nativeK]

theorem boot_sub : Face.Sub bootFace nface30 := by
  norm_num [Face.Sub, bootFace, nface30]

/-- The finite native bootstrap of the k15 chain, given one generic analytic step and subface monotonicity. -/
theorem bootstrapK15 (P : Face → Prop)
    (step : ∀ p n a, NativeGates p n a → P p → P n)
    (mono : ∀ q p, Face.Sub q p → P p → P q) (h0 : P face0) : P bootFace := by
  have g00 : P nface00 := h0
  have g01 : P nface01 := step _ _ _ ngates00 g00
  have g02 : P nface02 := step _ _ _ ngates01 g01
  have g03 : P nface03 := step _ _ _ ngates02 g02
  have g04 : P nface04 := step _ _ _ ngates03 g03
  have g05 : P nface05 := step _ _ _ ngates04 g04
  have g06 : P nface06 := step _ _ _ ngates05 g05
  have g07 : P nface07 := step _ _ _ ngates06 g06
  have g08 : P nface08 := step _ _ _ ngates07 g07
  have g09 : P nface09 := step _ _ _ ngates08 g08
  have g10 : P nface10 := step _ _ _ ngates09 g09
  have g11 : P nface11 := step _ _ _ ngates10 g10
  have g12 : P nface12 := step _ _ _ ngates11 g11
  have g13 : P nface13 := step _ _ _ ngates12 g12
  have g14 : P nface14 := step _ _ _ ngates13 g13
  have g15 : P nface15 := step _ _ _ ngates14 g14
  have g16 : P nface16 := step _ _ _ ngates15 g15
  have g17 : P nface17 := step _ _ _ ngates16 g16
  have g18 : P nface18 := step _ _ _ ngates17 g17
  have g19 : P nface19 := step _ _ _ ngates18 g18
  have g20 : P nface20 := step _ _ _ ngates19 g19
  have g21 : P nface21 := step _ _ _ ngates20 g20
  have g22 : P nface22 := step _ _ _ ngates21 g21
  have g23 : P nface23 := step _ _ _ ngates22 g22
  have g24 : P nface24 := step _ _ _ ngates23 g23
  have g25 : P nface25 := step _ _ _ ngates24 g24
  have g26 : P nface26 := step _ _ _ ngates25 g25
  have g27 : P nface27 := step _ _ _ ngates26 g26
  have g28 : P nface28 := step _ _ _ ngates27 g27
  have g29 : P nface29 := step _ _ _ ngates28 g28
  have g30 : P nface30 := step _ _ _ ngates29 g29
  exact mono _ _ boot_sub g30

end
end QRH.SilDensitySplit.K15
