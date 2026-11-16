import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem

/-!
# Draft: Buffalo 8313: Cohen's structure theorem for complete regular local rings

Issue Commutator-IO/grothendieck-project#162, heavy item. **Draft only**: this file is not imported
from the root, so CI does not compile it or its Stacks imports. To work on it, add
`import Drafts.Buffalo14Cohen` to `GrothendieckArchivesProofs.lean` (or move it under `Grothendieck/` or
`Buffalo/`), expect a long first CI run, and state and prove the result.

## Goal

Index entry 8313: a complete regular local ring is a power series ring over a field or a Cohen ring (Stacks 032D, 032A; closure 99).

## Stacks declarations to start from

* Stacks 032D: `StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem`
* Stacks 032A: `StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem`

Import closure of the modules below: 99 Stacks modules.

## Plan

1. State the result faithfully (source row in `src/content/findings.ts`, or the Buffalo index entry).
2. Prove it from the declarations above.
3. Update the edition (findings `lean` field, Lean article section, reading footnote, counts).
-/
