module

public meta import Lean

/-!
# Axiom check

Issue #31, question 3 of « …and the proof is checked in Lean » (Xena, 12 November 2026), its
axiom half. Run after `lake build`:

    lake env lean --run scripts/CheckAxioms.lean <root module> <module prefix>...

The CI runs it on `GrothendieckArchivesProofs` with the prefixes of the libraries of this
repository (`Grothendieck`, `Buffalo`, `OpenProblems`, the copied `MMP`, `LeanPool`, and the dependency
`Mordell`).

Imports the root module and collects every axiom that the constants declared in modules whose
name starts with one of the prefixes depend on, transitively, through Mathlib, Stacks and the
copied files. It fails if any axiom other than `propext`, `Classical.choice` and `Quot.sound` is
reached (`sorryAx`, or an `axiom` declared anywhere in the closure), and then names, for each
offending axiom, the constants of these modules that depend on it.

This does not detect a statement whose meaning is changed by an import; that is the job of a
comparator between a trusted statement file and the proof (issue #31).

One traversal of the whole dependency graph decides pass or fail; the per-constant report,
which is slower, runs only on failure.
-/

public meta section

open Lean

/-- The axioms of mathematics allowed in a proof. -/
def allowedAxioms : NameSet :=
  NameSet.empty |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound

/-- The constants a declaration refers to, as in `Lean.collectAxioms`. -/
def dependencies (info : ConstantInfo) : Array Name :=
  let ofExpr (e : Expr) : Array Name := e.getUsedConstants
  match info with
  | .axiomInfo v => ofExpr v.type
  | .defnInfo v => ofExpr v.type ++ ofExpr v.value
  | .thmInfo v => ofExpr v.type ++ ofExpr v.value
  | .opaqueInfo v => ofExpr v.type ++ ofExpr v.value
  | .quotInfo v => ofExpr v.type
  | .ctorInfo v => ofExpr v.type
  | .recInfo v => ofExpr v.type
  | .inductInfo v => ofExpr v.type ++ v.ctors.toArray

/-- Every axiom reachable from `roots`, by an iterative depth-first search. -/
def reachableAxioms (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut found : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let name := stack.back!
    stack := stack.pop
    if visited.contains name then continue
    visited := visited.insert name
    match env.find? name with
    | none => pure ()
    | some info =>
      if info matches .axiomInfo _ then found := found.insert name
      for dependency in dependencies info do
        unless visited.contains dependency do stack := stack.push dependency
  return found

def main (arguments : List String) : IO UInt32 := do
  let root :: prefixes := arguments
    | throw <| IO.userError "usage: CheckAxioms <root module> <module prefix>..."
  let prefixes := prefixes.map String.toName
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← importModules #[{ module := root.toName }] {} (trustLevel := 1024)
  let owned (module : Name) : Bool := prefixes.any (·.isPrefixOf module)
  let roots := env.constants.map₁.fold (init := #[]) fun roots name _ =>
    match env.getModuleIdxFor? name with
    | some index =>
      if owned env.header.moduleNames[index.toNat]! then roots.push name else roots
    | none => roots
  let found := reachableAxioms env roots
  let bad := found.toList.filter (!allowedAxioms.contains ·)
  IO.println s!"Checked {roots.size} constants from {prefixes}; axioms reached: {found.toList}"
  if bad.isEmpty then
    return 0
  IO.eprintln s!"error: axioms other than propext, Classical.choice and Quot.sound: {bad}"
  let mut shown := 0
  for name in roots do
    let axioms := reachableAxioms env #[name]
    let offending := bad.filter axioms.contains
    unless offending.isEmpty do
      IO.eprintln s!"  {name} depends on {offending}"
      shown := shown + 1
      if shown ≥ 200 then
        IO.eprintln "  (stopping after 200 constants)"
        break
  return 1
