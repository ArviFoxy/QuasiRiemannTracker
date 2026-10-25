import Candidate.Main
open Lean

/-- Constants reachable from `roots` through types, values, constructors and recursors, without
expanding the constants in `stop`. -/
partial def qrhClosure (env : Environment) (roots : List Name) (stop : NameSet := {}) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      if stop.contains n then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut refs := ci.type.getUsedConstants.toList
        if let some v := ci.value? (allowOpaque := true) then
          refs := refs ++ v.getUsedConstants.toList
        match ci with
        | .inductInfo i => refs := refs ++ i.ctors ++ i.all
        | .ctorInfo c => refs := refs ++ [c.induct]
        | .recInfo r => refs := refs ++ r.all
        | _ => pure ()
        for r in refs do
          if !seen.contains r then stack := r :: stack
  return seen

#eval show CoreM Unit from do
  let env ← getEnv
  let roots : List (String × Name) := [
    ("all", `Candidate.bound_sharp),
    ("seed", `QRH.Record1252270103Source.Endpoint.seed_step),
    ("nf2", `QRH.RepeatedMarks.Source.nf_step2),
    ("incumbent", `QRH.Record1252270103Bootstrap.incumbent_beta),
    ("intermediate", `QRH.Record1252270103Return.Intermediate.beta_of_global_sources),
    ("final", `QRH.RepeatedMarks.Return.Final.beta_of_global_sources),
    ("chain", `QRH.RepeatedMarks.Graph.chain_sources),
    ("seedsup", `QRH.Record1252270103Graph.seed_global_suppliers),
    ("natcap", `QRH.Record1252270103Graph.final_natural_cap)]
  for (_, r) in roots do
    if (env.find? r).isNone then IO.println s!"missing root {r}"
  let full := qrhClosure env [`Candidate.bound_sharp]
  -- closures of each root, and of `all` with that root treated as a leaf
  let mut cols : Array (String × NameSet × NameSet) := #[]
  for (lab, r) in roots.tail do
    let own := qrhClosure env [r]
    let without := qrhClosure env [`Candidate.bound_sharp] (NameSet.empty.insert r)
    cols := cols.push (lab, own, without)
  let h ← IO.FS.Handle.mk "OUT_DIR/closure_split.tsv" .write
  h.putStrLn ("name\t" ++ String.intercalate "\t" (cols.toList.map fun (l, _, _) => l ++ "\t" ++ l ++ "_cut"))
  for n in full.toList do
    let flags := cols.toList.map fun (_, own, without) =>
      (if own.contains n then "1" else "0") ++ "\t" ++ (if without.contains n then "1" else "0")
    h.putStrLn (n.toString ++ "\t" ++ String.intercalate "\t" flags)
  IO.println s!"full {full.size}"
  for (l, own, without) in cols do
    IO.println s!"{l}: own {own.size}, all-with-{l}-as-leaf {without.size}"
