import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.High.GlobalPhysicalRegularSuppliers
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialRegularToTruncatedBalanced
open Lean Meta Elab Command

/-! Fork set of the mixed step's downstream (L4/L5), Phase 0 of `L45_DESIGN.md` §3.

`tainted`: declarations of Collet's tree or of the PR 76 tree whose statement (definitions and
structures: also value) depends on one of the seeds: the first-layer anchor, the phase bound, the
MAIN amplitude, the step's real geometry, or the node price.
`closure`: everything the proofs of `regular_supplier_some_rm` and `balanced_of_regular` use,
not descending through the stop set (the second-layer objects the design reuses verbatim).
The fork restates exactly `tainted ∩ closure`. The stop set must stay untainted.

Run (from `lean-env/qrh`): `lake env lean <this file>`; it writes
`research/mixed-step/fork/{closure_mx.tsv,direct_mx.tsv,tainted_all_mx.txt,stop_mx.txt}`. -/

def seedNames : List Name := [
  `QRH.Record1252270103Source.Admission.SelectedRegularSourceData.Anchor,
  `QRH.Record1252270103Source.Admission.SelectedHighPaid.PhaseBound,
  `QRH.Record1252270103Source.Admission.SelectedHighPaid.mainExtra,
  `QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.amplitude,
  `QRH.Record1252270103StepScalar.RealGeometry,
  `QRH.Record1252270103Source.RegularLowPhysicalPrice.ModifiedNodePrice ]

def roots : List Name := [
  `QRH.Record1252270103Source.High.GlobalPhysical.regular_supplier_some_rm,
  `QRH.Record1252270103Source.InitialRegularToTruncated.balanced_of_regular ]

/-- Reused verbatim at the second-layer parent `s := s.restrict J` (design §0). -/
def stopNames : List Name := [
  `QRH.Record1252270103Source.Admission.SelectedHighCofactorFamily.Selection,
  `QRH.Record1252270103Source.Admission.SelectedSecondPhase.FirstStage,
  `OAI.SevenEighths.CenteredMomentAmplificationChildInput.child,
  `QRH.Record1252270103Source.High.GlobalPhysical.correctedChildGaussEnergy,
  `QRH.Record1252270103Source.InitialRegularToTruncated.eventual_selected_second,
  `QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.CorrectedFamilyData ]

def OUT : String := "/home/user/QuasiRiemannTracker/research/mixed-step/fork/"

def scopePrefixes : List Name :=
  [`Submissions.hailey_collet_1252270103, `Submissions.arvi_repeated_marks_on_sil_face_20261025]

def inScope (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if scopePrefixes.any (·.isPrefixOf m) then some m else none
  | none => none

def modIdx (env : Environment) (n : Name) : Nat :=
  match env.getModuleIdxFor? n with
  | some idx => idx.toNat
  | none => 0

def stmtRefs (ci : ConstantInfo) : NameSet :=
  let tyRefs := ci.type.getUsedConstantsAsSet
  match ci with
  | .defnInfo d => tyRefs.append d.value.getUsedConstantsAsSet
  | .opaqueInfo d => tyRefs.append d.value.getUsedConstantsAsSet
  | _ => tyRefs

def allRefs (ci : ConstantInfo) : NameSet :=
  match ci.value? (allowOpaque := true) with
  | some v => ci.type.getUsedConstantsAsSet.append v.getUsedConstantsAsSet
  | none => ci.type.getUsedConstantsAsSet

/-- Is `n` a stop item or a declaration in a stop item's namespace (projections, `mk`, helpers)? -/
def underStop (n : Name) : Bool := stopNames.any (fun s => s == n || s.isPrefixOf n)

run_cmd do
  let env ← getEnv
  for s in seedNames ++ roots ++ stopNames do
    unless env.contains s do logError m!"missing declaration {s}"
  -- taint (statement level), with a witness parent for every tainted declaration
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if (inScope env n).isSome then
      for r in (stmtRefs ci).toList do
        rev := rev.insert r ((rev.getD r #[]).push n)
      if let .ctorInfo c := ci then
        rev := rev.insert n ((rev.getD n #[]).push c.induct)
      if let .recInfo r := ci then
        for t in r.all do rev := rev.insert t ((rev.getD t #[]).push n)
  let mut tainted : NameSet := {}
  let mut parent : Std.HashMap Name Name := {}
  let mut queue : Array Name := #[]
  for s in seedNames do
    tainted := tainted.insert s
    queue := queue.push s
  let mut i := 0
  while i < queue.size do
    let x := queue[i]!
    i := i + 1
    for y in rev.getD x #[] do
      if !tainted.contains y then
        tainted := tainted.insert y
        parent := parent.insert y x
        queue := queue.push y
  -- the stop set must stay untainted
  let mut stopLines : Array String := #[]
  let mut stopTainted := false
  for (n, _) in env.constants.toList do
    if underStop n && (inScope env n).isSome && tainted.contains n && !n.isInternal then
      stopTainted := true
      let mut path : Array String := #[n.toString]
      let mut cur := n
      let mut k := 0
      while k < 40 do
        k := k + 1
        match parent.get? cur with
        | some p => path := path.push p.toString; cur := p
        | none => break
      stopLines := stopLines.push ("TAINTED\t" ++ String.intercalate " <- " path.toList)
  for s in stopNames do
    stopLines := stopLines.push ((if tainted.contains s then "tainted\t" else "clean\t") ++ s.toString)
  IO.FS.writeFile (OUT ++ "stop_mx.txt") (String.intercalate "\n" stopLines.toList ++ "\n")
  logInfo m!"stop set tainted: {stopTainted}"
  -- proof closure of the roots (in-scope declarations only), not descending through the stop set
  let mut closure : NameSet := {}
  let mut stack : Array Name := roots.toArray
  while h : stack.size > 0 do
    let x := stack.back
    stack := stack.pop
    if closure.contains x || underStop x then continue
    closure := closure.insert x
    if let some ci := env.find? x then
      for r in (allRefs ci).toList do
        if (inScope env r).isSome && !closure.contains r then
          stack := stack.push r
  -- report tainted ∩ closure by module, modules in import (topological) order, declarations in
  -- source order
  let mut byMod : Std.HashMap Name (Array Name) := {}
  let mut cnt : Nat := 0
  for n in closure.toList do
    if tainted.contains n then
      if let some m := inScope env n then
        cnt := cnt + 1
        byMod := byMod.insert m ((byMod.getD m #[]).push n)
  let modsSorted := byMod.toList.toArray.qsort (fun a b =>
    modIdx env (a.2[0]!) < modIdx env (b.2[0]!))
  let mut lines : Array String := #["# order\tmodule\tcount\tdeclarations (source order; tainted ∩ closure)"]
  let mut ord : Nat := 0
  for (m, ns) in modsSorted do
    ord := ord + 1
    let shown := ns.filter (fun n => !n.isInternal)
    let mut keyed : Array (Nat × Name) := #[]
    for n in shown do
      let r ← liftCoreM <| findDeclarationRanges? n
      let line := match r with
        | some rr => rr.range.pos.line
        | none => 0
      keyed := keyed.push (line, n)
    let sorted := keyed.qsort (fun a b => a.1 < b.1)
    lines := lines.push (toString ord ++ "\t" ++ m.toString ++ "\t" ++ toString shown.size ++ "\t" ++
      String.intercalate " " (sorted.toList.map (fun p => p.2.toString)))
  -- all tainted names (any in-scope module), for reference rewriting
  let mut all : Array String := #[]
  for n in tainted.toList do
    if (inScope env n).isSome && !n.isInternal then all := all.push n.toString
  -- declarations of the fork whose type, value or proof mentions a seed directly
  let mut direct : Array String := #[]
  for n in closure.toList do
    if tainted.contains n && !(seedNames.contains n) && !n.isInternal then
      if let some ci := env.find? n then
        let refs := allRefs ci
        let hits := seedNames.filter (fun s => refs.contains s)
        if !hits.isEmpty then
          direct := direct.push (n.toString ++ "\t" ++ String.intercalate " " (hits.map toString))
  -- closure members that are untainted, by module (reused verbatim)
  let mut clean : Nat := 0
  for n in closure.toList do
    if !tainted.contains n then clean := clean + 1
  IO.FS.writeFile (OUT ++ "direct_mx.tsv") (String.intercalate "\n" direct.toList ++ "\n")
  IO.FS.writeFile (OUT ++ "closure_mx.tsv") (String.intercalate "\n" lines.toList ++ "\n")
  IO.FS.writeFile (OUT ++ "tainted_all_mx.txt") (String.intercalate "\n" all.toList ++ "\n")
  logInfo m!"closure: {closure.size} (untainted {clean}), fork modules: {modsSorted.size}, fork declarations: {cnt}, tainted total: {all.size}"
