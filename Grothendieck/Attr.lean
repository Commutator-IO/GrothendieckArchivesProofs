/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public meta import Lean

/-!
# Source attributes: where a declaration comes from in Grothendieck's notes

Issue #39, step 3. Two attributes record, on a declaration, the place in the sources that it
formalises, next to Stacks' `@[stacks]`, `@[ega]` and `@[sga]` (`StacksCore.Tactic.StacksAttribute`,
`StacksCore.Tactic.EgaSgaAttribute`), on which they are modelled:

- `@[montpellier "136, 19–31"]`: the Montpellier notes, as `"cote, page"`. The cote is the folder
  number of the archive (`136`, `156-1`, `161-2`); the page, a page or a range of pages
  (`19–31`, `5, 226–232`), or `n.p.` when the folder is not paginated.
- `@[buffalo "Oqhr-Gt66es-22510"]`: an entry of the index of the Buffalo lectures (1973), as it is
  written at the head of the declaration's docstring: the video and the entry number (its time
  in the video, in seconds).

Both are pure annotations: the attribute stores the declaration's name and the string in the
environment extension `sourceExt` and does nothing else. It changes no docstring, adds no
constant and has no effect on elaboration, so neither the axiom check
(`scripts/CheckAxioms.lean`) nor `lake comparator` sees it. `scripts/SourceIndex.lean` reads
the extension and lists the declarations by cote, by Buffalo entry and by EGA/SGA item.

## Main definitions

* `Grothendieck.Source.sourceExt`: the record of which declaration comes from which place;
* `Grothendieck.Source.allEntries`: every entry visible in an environment;
* `#source_tags?`: lists the entries added in the current file.

## Implementation notes

The extension and the attributes copy the shape of `Stacks.EgaSga.refExt` and its attributes
(AxiomMath/Stacks, Apache-2.0), without the docstring line those add.
-/

@[expose] public section

meta section

open Lean Elab Command

namespace Grothendieck.Source

/-- The two sources. -/
inductive Work where
  /-- The working notes kept at the University of Montpellier, by cote and page. -/
  | montpellier
  /-- The Buffalo lectures (1973), by entry of the index. -/
  | buffalo
  deriving BEq, Hashable, Inhabited, Repr

/-- A recorded source: `ref` is the string of the attribute, e.g. `"136, 19–31"`. -/
structure Entry where
  /-- The declaration carrying the attribute. -/
  declName : Name
  /-- Montpellier or Buffalo. -/
  work : Work
  /-- `"cote, page"` for Montpellier, the entry for Buffalo. -/
  ref : String
  deriving BEq, Hashable, Inhabited, Repr

/-- The environment extension recording every source attribute. -/
initialize sourceExt : SimplePersistentEnvExtension Entry (Array (Array Entry)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries
    addEntryFn := fun entries _ => entries
  }

/-- Every entry visible in `env`, imported ones included. -/
def allEntries (env : Environment) : Array Entry :=
  let state := PersistentEnvExtension.getState sourceExt env
  state.2.flatten ++ state.1.toArray.reverse

/-- The cote of a Montpellier reference `"cote, page"`: what comes before the first comma. -/
def cote (ref : String) : String := ((ref.splitOn ",").headD ref).trimAscii.toString

/-- Check a Montpellier reference: a cote (digits, possibly with a `-n` suffix), a comma, a
page. -/
def checkMontpellier (ref : String) : Except String Unit := do
  let parts := ref.splitOn ", "
  unless parts.length ≥ 2 && parts.all (!·.isEmpty) do
    throw s!"expected \"cote, page\", e.g. \"136, 19–31\", got \"{ref}\""
  let c := parts.headD ""
  unless c.front.isDigit && c.all (fun ch => ch.isDigit || ch == '-') do
    throw s!"\"{c}\" is not a cote such as 136 or 156-1"

/-- Check a Buffalo entry: a video identifier, a hyphen, the entry number. -/
def checkBuffalo (ref : String) : Except String Unit := do
  let parts := ref.splitOn "-"
  let num := parts.getLastD ""
  unless parts.length ≥ 2 && !num.isEmpty && num.all Char.isDigit do
    throw s!"expected \"VIDEO-NUMBER\", e.g. \"Oqhr-Gt66es-22510\", got \"{ref}\""

/-- Check and record the entry. -/
def addEntry (decl : Name) (work : Work) (ref : String) : CoreM Unit := do
  match (match work with | .montpellier => checkMontpellier ref | .buffalo => checkBuffalo ref) with
  | .ok () => pure ()
  | .error e => throwError e
  if (allEntries (← getEnv)).any fun e => e.declName == decl && e.work == work && e.ref == ref then
    logWarning m!"'{decl}' already carries this source; skipping duplicate."
  else
    modifyEnv (sourceExt.addEntry · { declName := decl, work, ref })

/-- `@[montpellier "136, 19–31"]`: the declaration comes from folder (cote) 136 of the
Montpellier notes, pages 19–31. -/
syntax (name := montpellierAttr) "montpellier " str : attr
/-- `@[buffalo "Oqhr-Gt66es-22510"]`: the declaration is the entry `Oqhr-Gt66es-22510` of the
index of the Buffalo lectures. -/
syntax (name := buffaloAttr) "buffalo " str : attr

initialize
  for (name, work) in [(`montpellierAttr, Work.montpellier), (`buffaloAttr, Work.buffalo)] do
    registerBuiltinAttribute {
      name
      descr := "Record the place in Grothendieck's notes that this declaration formalises."
      add := fun decl stx _ => do
        let ref ← match stx with
          | `(attr| montpellier $r) | `(attr| buffalo $r) => pure r.getString
          | _ => throwUnsupportedSyntax
        addEntry decl work ref
    }

/-- List the source attributes added in the current file. -/
elab "#source_tags?" : command => do
  let entries := (PersistentEnvExtension.getState sourceExt (← getEnv)).1.reverse
  let lines := entries.map fun e =>
    let w := match e.work with | .montpellier => "Montpellier" | .buffalo => "Buffalo"
    m!"{w} {e.ref}: {e.declName}"
  logInfo (MessageData.joinSep lines "\n")

end Grothendieck.Source
