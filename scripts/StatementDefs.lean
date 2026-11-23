module

public meta import Lean

/-!
# The definitions behind the statements

Issue #31, question 1 of « …and the proof is checked in Lean » (Xena, 12 November 2026): a
statement is only as trustworthy as the definitions it is written with, and Mathlib is the only
dependency reviewed by humans to Mathlib's standard. Run after `lake build`:

    lake env lean --run scripts/StatementDefs.lean <root module> <output file>
      [--mathlib-only <second output file>] <module prefix>...

Imports the root module and, for every theorem declared in a module whose name starts with one of
the prefixes, collects the constants in its *statement* (its type, not its proof; for a
`def … : Prop`, as in `OpenProblems/`, its body) that are
defined outside Mathlib and Lean's core libraries: definitions, structures and inductive types of
AxiomMath/Stacks, of AxiomMath/Mordell, of the copied `MMP/` files, and of this repository. It then
follows the definitions those depend on (types and bodies), still outside Mathlib, which is the
whole set a reader has to check to trust the statements.

The report (Markdown) lists, by library and then by defining module, each definition used
directly in a statement, with the number of statements that use it and one of them, and gives
the size of the closure. Instances and structure projections are counted separately: they are
reviewed with the class or structure they belong to.

With `--mathlib-only`, a second report (Markdown) lists the *theorems* whose statement uses no
constant outside Mathlib and Lean's core libraries at all, by module, with their count: these can
be restated in `Challenge.lean` with Mathlib's imports alone and compared by `lake comparator`
(issue #31, question 3).
-/

public meta section

open Lean

/-- Roots of the modules taken as trusted here: Mathlib and the libraries it is built on. -/
def trustedRoots : List Name :=
  [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
    `ImportGraph, `LeanSearchClient]

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

def isTrusted (mod : Name) : Bool := trustedRoots.contains mod.getRoot

def hasPrefix (prefixes : List Name) (mod : Name) : Bool :=
  prefixes.any fun p => p.isPrefixOf mod

/-- Constants worth reviewing: definitions, opaque constants, inductive types. -/
def isDefinitionLike : ConstantInfo → Bool
  | .defnInfo _ | .opaqueInfo _ | .inductInfo _ => true
  | _ => false

/-- The library a module belongs to, for the report's sections. -/
def library (mod : Name) : String :=
  match mod.getRoot with
  | `StacksCore | `StacksFrontier | `Stacks => "AxiomMath/Stacks"
  | `Mordell => "AxiomMath/Mordell"
  | `MMP => "MMP (copied)"
  | r => s!"{r} (this repository)"

/-- Lemmas the compiler generates (equation lemmas, `sizeOf` specs, congruence and injectivity
lemmas): their statements repeat those of the declarations they come from. -/
def isGenerated (n : Name) : Bool :=
  match n with
  | .str _ s =>
    ["sizeOf_spec", "congr_simp", "injEq", "inj", "ext_iff", "eq_def"].contains s ||
      (s.startsWith "eq_" && (s.drop 3).all Char.isDigit) || s.startsWith "match_" ||
      s.startsWith "_"
  | _ => true

structure Use where
  count : Nat := 0
  example? : Option Name := none

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | root :: out :: rest =>
    let (mathlibOnly?, prefixStrs) := match rest with
      | "--mathlib-only" :: f :: ps => (some f, ps)
      | ps => (none, ps)
    let prefixes := prefixStrs.map String.toName
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let env ← importModules #[{ module := root.toName }] {} (loadExts := true)
    -- Direct uses: non-Mathlib definitions in the statements of our theorems.
    let mut uses : Std.HashMap Name Use := {}
    let mut theorems := 0
    -- Theorems whose statement uses Mathlib and core constants only, with their module.
    let mut onlyTrusted : Array (Name × Name) := #[]
    for (n, ci) in env.constants.map₁.toList do
      -- A statement is a theorem's type, or the body of a `def … : Prop` (`OpenProblems/`).
      let statement? : Option Expr := match ci with
        | .thmInfo t => some t.type
        | .defnInfo d => if d.type.isProp then some d.value else none
        | _ => none
      let some statement := statement? | continue
      if n.isInternalDetail || isGenerated n then continue
      let some mod := moduleOf env n | continue
      unless hasPrefix prefixes mod do continue
      theorems := theorems + 1
      if ci matches .thmInfo _ then
        if statement.getUsedConstants.all fun c =>
            ((moduleOf env c).map isTrusted).getD true then
          onlyTrusted := onlyTrusted.push (mod, n)
      for c in statement.getUsedConstants do
        let some m := moduleOf env c | continue
        if isTrusted m then continue
        let some cci := env.find? c | continue
        unless isDefinitionLike cci do continue
        if c.isInternalDetail || isGenerated c then continue
        let u := uses.getD c {}
        uses := uses.insert c { count := u.count + 1, example? := u.example?.getD n }
    -- Closure: the non-Mathlib definitions these depend on, through types and bodies.
    let mut closure : NameSet := {}
    let mut stack : List Name := uses.toList.map (·.1)
    while !stack.isEmpty do
      match stack with
      | [] => pure ()
      | c :: rest =>
        stack := rest
        if closure.contains c then continue
        closure := closure.insert c
        let some cci := env.find? c | continue
        -- A definition's type and body; an inductive type's (or structure's) constructors.
        let deps := cci.type.getUsedConstants ++
          (match cci.value? (allowOpaque := true) with
            | some v => v.getUsedConstants
            | none => #[]) ++
          (match cci with
            | .inductInfo i => i.ctors.toArray.flatMap fun k =>
                ((env.find? k).map (·.type.getUsedConstants)).getD #[]
            | _ => #[])
        for d in deps do
          if closure.contains d then continue
          let some m := moduleOf env d | continue
          if isTrusted m then continue
          let some dci := env.find? d | continue
          if isDefinitionLike dci && !d.isInternalDetail then stack := d :: stack
    -- Report.
    let isInst (c : Name) : Bool := Meta.isInstanceCore env c
    let isProj (c : Name) : Bool := (env.getProjectionFnInfo? c).isSome
    let rows := uses.toList.filterMap fun (c, u) =>
      (moduleOf env c).map fun m => (library m, m, c, u)
    let rows := rows.toArray.qsort fun a b =>
      a.1 < b.1 || (a.1 == b.1 && (a.2.1.toString < b.2.1.toString ||
        (a.2.1 == b.2.1 && a.2.2.1.toString < b.2.2.1.toString)))
    let mut md := "# Definitions behind the statements\n\n"
    md := md ++ s!"Generated by `scripts/StatementDefs.lean` from `{root}`, prefixes " ++
      s!"{", ".intercalate (prefixStrs.map (s!"`{·}`"))}.\n\n"
    md := md ++ s!"- Statements read (theorems, and `def … : Prop`): {theorems}.\n"
    md := md ++ s!"- Non-Mathlib definitions used directly in a statement: {uses.size} " ++
      s!"({(uses.toList.filter (isInst ·.1)).length} instances, " ++
      s!"{(uses.toList.filter (isProj ·.1)).length} structure projections).\n"
    md := md ++ s!"- Non-Mathlib definitions they depend on, these included: {closure.size}"
    let closureLibs := closure.toList.filterMap fun c => (moduleOf env c).map library
    let perLib := closureLibs.eraseDups.map fun l =>
      s!"{l}: {(closureLibs.filter (· == l)).length}"
    md := md ++ s!" ({", ".intercalate perLib}).\n\n"
    let libs := (rows.map (·.1)).toList.eraseDups
    for lib in libs do
      let libRows := rows.filter (·.1 == lib)
      md := md ++ s!"## {lib}\n\n{libRows.size} definitions.\n\n"
      md := md ++ "| Definition | Module | Statements | Kind | Example |\n|---|---|---|---|---|\n"
      for (_, m, c, u) in libRows do
        let kind := if isInst c then "instance" else if isProj c then "projection" else ""
        let ex := (u.example?.map (s!"`{·}`")).getD ""
        md := md ++ s!"| `{c}` | `{m}` | {u.count} | {kind} | {ex} |\n"
      md := md ++ "\n"
    IO.FS.writeFile out md
    if let some out₂ := mathlibOnly? then
      let sorted := onlyTrusted.qsort fun a b =>
        a.1.toString < b.1.toString || (a.1 == b.1 && a.2.toString < b.2.toString)
      let mut md₂ := "# Theorems stated with Mathlib alone\n\n"
      md₂ := md₂ ++ s!"Generated by `scripts/StatementDefs.lean` from `{root}`, prefixes " ++
        s!"{", ".intercalate (prefixStrs.map (s!"`{·}`"))}.\n\n"
      md₂ := md₂ ++ "- Theorems whose statement uses only constants of Mathlib and Lean's " ++
        s!"core libraries: {sorted.size}.\n"
      let mods := (sorted.map (·.1)).toList.eraseDups
      let roots := (sorted.map (·.1.getRoot)).toList.eraseDups
      let perRoot := roots.map fun r => s!"{r}: {(sorted.filter (·.1.getRoot == r)).size}"
      let byLib := ", ".intercalate perRoot
      md₂ := md₂ ++ s!"- By library: {byLib}.\n"
      md₂ := md₂ ++ s!"- Modules: {mods.length}.\n\n"
      for m in mods do
        let ns := sorted.filter (·.1 == m)
        md₂ := md₂ ++ s!"## `{m}` ({ns.size})\n\n"
        for (_, n) in ns do
          md₂ := md₂ ++ s!"- `{n}`\n"
        md₂ := md₂ ++ "\n"
      IO.FS.writeFile out₂ md₂
      IO.println s!"{sorted.size} theorems are stated with Mathlib alone ({byLib}), in \
        {mods.length} modules. Report: {out₂}"
    IO.println s!"Read {theorems} statements; {uses.size} non-Mathlib definitions used directly, \
      {closure.size} in their closure. Report: {out}"
    return 0
  | _ =>
    IO.eprintln "usage: lake env lean --run scripts/StatementDefs.lean <root module> <output> \
      [--mathlib-only <output>] <module prefix>..."
    return 2
