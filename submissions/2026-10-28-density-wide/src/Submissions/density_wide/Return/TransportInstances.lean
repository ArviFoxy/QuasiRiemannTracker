/- Repeated marks: fork of Collet's final-stage module TransportInstances (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the widened box `BoundsN` (not PR76 `BoundsR`, which fails here) at the new parameters -/
import Submissions.sil_density_split_20261026.ReturnD.TransportGeometry
import Submissions.density_wide.Return.Geometry
set_option autoImplicit false
namespace QRH.DensityWide.Return.Geometry
open QRH.SilDensitySplit.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalBounds : @BoundsN finalParameters := by
  refine @BoundsN.mk finalParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,QRH.Record1252270103Return.Geometry.dPlus,QRH.Record1252270103Return.Geometry.signal,QRH.Record1252270103Return.Geometry.signalShift,finalParameters,
    QRH.DensityWide.Return.theta,QRH.DensityWide.Return.h,QRH.DensityWide.Return.ell,QRH.DensityWide.Return.x,QRH.DensityWide.Return.y,QRH.DensityWide.Return.c] <;> norm_num
end QRH.DensityWide.Return.Geometry
