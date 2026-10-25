/-
Declaration graph of compiled modules, read straight from their .olean files.

  lean --run bench/alive/Dump.lean INDEX OUTDIR

INDEX has one line per module of a submission's import closure, in any order:
  MODULE<TAB>OLEAN<TAB>KEY<TAB>1 to write OUTDIR/KEY.json, 0 to only read its names

Nothing is imported or elaborated: the .olean files are read as data. For each
constant of a written module the dump says what kind it is, where it was
declared, and which constants of the closure it needs (named in its type, its
value, or for inductive types its constructors). Constants of libraries outside
the closure are left out: nothing in the closure can be needed by them.
-/
import Lean
open Lean

structure Entry where
  name : Name
  path : System.FilePath
  key : String
  write : Bool

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- A proof that is `rfl`, under any binders: simp uses such a lemma by unfolding,
and leaves no trace of it in the proof term. -/
partial def isRfl : Expr → Bool
  | .lam _ _ b _ => isRfl b
  | .mdata _ b => isRfl b
  | e =>
    let f := e.getAppFn
    f.isConstOf ``Eq.refl || f.isConstOf ``rfl || f.isConstOf ``Iff.refl || f.isConstOf ``Iff.rfl ||
      f.isConstOf ``HEq.refl || f.isConstOf ``HEq.rfl

/-- Every constant the declaration needs to be checked: its type, its value, and
the declarations that are defined together with it. -/
def needs (c : ConstantInfo) : Array Name :=
  let value : Array Name := match c with
    | .defnInfo d => d.value.getUsedConstants
    | .thmInfo d => d.value.getUsedConstants
    | .opaqueInfo d => d.value.getUsedConstants
    | _ => #[]
  let together : Array Name := match c with
    | .inductInfo i => i.ctors.toArray ++ i.all.toArray
    | .ctorInfo k => #[k.induct]
    | .recInfo r => r.all.toArray
    | .defnInfo d => d.all.toArray
    | .thmInfo d => d.all.toArray
    | .opaqueInfo d => d.all.toArray
    | _ => #[]
  c.type.getUsedConstants ++ value ++ together

unsafe def entriesOf {α : Type} (data : ModuleData) (ext : Name) : Array α :=
  match data.entries.find? (·.1 == ext) with
  | some (_, es) => unsafeCast es
  | none => #[]

def esc (s : String) : String := (Json.str s).compress

def parseLine (line : String) : Option Entry :=
  match line.splitOn "\t" with
  | [m, p, k, w] => some { name := m.toName, path := p, key := k, write := w == "1" }
  | _ => none

def intern (table : Array Name) (index : Std.HashMap Name Nat) (n : Name) :
    Nat × Array Name × Std.HashMap Name Nat :=
  match index[n]? with
  | some i => (i, table, index)
  | none => (table.size, table.push n, index.insert n table.size)

unsafe def dump (names : Std.HashSet Name) (data : ModuleData) (module : Name) : String := Id.run do
  let ranges : Std.HashMap Name DeclarationRanges :=
    (entriesOf (α := Name × DeclarationRanges) data `Lean.declRangeExt).foldl (init := {}) fun m (n, r) => m.insert n r
  let aliases := entriesOf (α := Name × Name) data `Lean.aliasExtension
  -- Names of the closure that this module mentions, numbered as first seen.
  let mut table : Array Name := #[]
  let mut index : Std.HashMap Name Nat := {}
  let mut out := ""
  let mut first := true
  for c in data.constants do
    let (here, t, ix) := intern table index c.name
    table := t
    index := ix
    let mut refs : Array Nat := #[]
    let mut seen : Std.HashSet Nat := {}
    let mut usesLean := false
    for n in needs c do
      if n.getRoot == `Lean then usesLean := true
      if n != c.name && names.contains n then
        let (i, t, ix) := intern table index n
        table := t
        index := ix
        if !seen.contains i then
          seen := seen.insert i
          refs := refs.push i
    let range := match ranges[c.name]? with
      | some r => s!",\"r\":[{r.range.pos.line},{r.range.pos.column},{r.range.endPos.line},{r.range.endPos.column}]"
      | none => ""
    let rflThm := match c with
      | .thmInfo d => isRfl d.value
      | _ => false
    let flag := (if usesLean then ",\"m\":1" else "") ++ (if rflThm then ",\"d\":1" else "")
    out := out ++ (if first then "" else ",") ++
      "{\"n\":" ++ toString here ++ ",\"k\":\"" ++ kind c ++ "\"" ++ range ++ flag ++
      ",\"u\":" ++ toString refs.toList ++ "}"
    first := false
  let tableJson := String.intercalate "," (table.toList.map fun n => esc n.toString)
  let aliasJson := String.intercalate "," (aliases.toList.map fun (a, t) => "[" ++ esc a.toString ++ "," ++ esc t.toString ++ "]")
  return "{\"module\":" ++ esc module.toString ++ ",\"names\":[" ++ tableJson ++ "],\"aliases\":[" ++ aliasJson ++ "],\"constants\":[" ++ out ++ "]}"

unsafe def run (args : List String) : IO UInt32 := do
  let [indexFile, outDir] := args | do
    IO.eprintln "usage: Dump INDEX OUTDIR"
    return 2
  let entries := (← IO.FS.lines indexFile).filterMap parseLine
  -- First pass: which constants does the closure define?
  let mut names : Std.HashSet Name := {}
  let mut loaded : Array (Entry × ModuleData) := #[]
  for e in entries do
    let (data, _) ← readModuleData e.path
    for n in data.constNames do names := names.insert n
    for n in data.extraConstNames do names := names.insert n
    if e.write then loaded := loaded.push (e, data)
  IO.FS.createDirAll outDir
  for (e, data) in loaded do
    IO.FS.writeFile (System.FilePath.mk outDir / s!"{e.key}.json") (dump names data e.name)
  return 0

@[implemented_by run] opaque runImpl (args : List String) : IO UInt32

def main (args : List String) : IO UInt32 := runImpl args
