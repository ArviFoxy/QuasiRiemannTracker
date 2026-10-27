/- Repeated marks: fork of Collet's generic return module PhysicalDirect.Data (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Submissions.sil_density_split_20261026.ReturnD.Schedule
import Submissions.hailey_collet_1252270103.Record1252270103Return.GenericData
set_option autoImplicit false
open QRH.Record1252270103Return

namespace QRH.SilDensitySplit.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [QRH.SilDensitySplit.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
abbrev BaselineData := QRH.Record1252270103Return.GenericPhysical.BaselineData
abbrev BaselineSourceData (D : BaselineData) := QRH.Record1252270103Return.GenericPhysical.BaselineSourceData D
end QRH.SilDensitySplit.Return.GenericPhysical.PhysicalDirect
