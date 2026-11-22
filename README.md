# Lean proofs of Grothendieck's archives

Lean 4 proofs of statements from two of Alexandre Grothendieck's archives, built on
[Mathlib](https://github.com/leanprover-community/mathlib4) and on
[the Stacks Project in Lean](https://github.com/AxiomMath/Stacks) (AxiomMath):

- `Grothendieck/`: the working notes kept at the University of Montpellier, one file per folder
  (cote), with the general lemmas they use in `Grothendieck/Upstream/`. The statements are the
  modernised readings of the edition [grothendieck-project](https://github.com/Commutator-IO/grothendieck-project),
  where each file is linked to its folder, its pages and its findings.
- `Buffalo/`: the lectures given at Buffalo in 1973, one file per part of their index.

The Montpellier statements and their proofs, written out in French, are in the preprint
M. Hua, *Grothendieck Montpellier. Énoncés des lectures modernisées démontrés*, Hexagon
[2611.00125v2](https://hexagonmath.org/2611.00125v2).

`import GrothendieckArchivesProofs` brings in both. Lean's kernel checks every proof; the build
treats warnings as errors, so a `sorry` fails it.

## Open problems

`OpenProblems/` states the open questions of the Montpellier notes and of the Buffalo lectures,
one file per section of the edition's two notes on open problems. Each is a `def … : Prop`, not a
theorem: nothing there is proved, and the build would reject a `sorry`. The docstrings give the
question in our words, its source (folder and pages, or video and time), its status (open,
settled, or false with the counterexample) and the choices made in writing it down; questions
that the libraries cannot yet express are listed in each file's header with what is missing.

## Versions

Lean v4.35.0 and Mathlib v4.35.0, the versions of the Stacks project, which is required at a
pinned commit (`lakefile.toml`). The proofs that use Stacks import its modules
(`StacksCore.…`, `StacksFrontier.…`) directly.

## Building

```
lake exe cache get
lake build
```

The continuous-integration workflow (`.github/workflows/build.yml`) does the same on every push.
Mathlib's compiled files come from its cache; the Stacks modules the proofs import have no cache
yet and are compiled by the build.

## Plan

This repository follows the layout of AxiomMath's projects built on Stacks
([Weil](https://github.com/AxiomMath/Weil), [Mordell](https://github.com/AxiomMath/Mordell)).
The next steps, tracked in
[grothendieck-project#160](https://github.com/Commutator-IO/grothendieck-project/issues/160):
a library arranged by mathematical topic instead of by folder, an attribute linking each
declaration to its folder and page or Buffalo entry, Stacks' `@[ega]`/`@[sga]` attributes where a
declaration proves an EGA or SGA item, and Mathlib's style options.

## Licence

[Apache 2.0](LICENSE). The same proofs are under CC0 in grothendieck-project. Short quotations of
the manuscripts in comments, in « », are not covered: the rights in Grothendieck's manuscripts are
held by his heirs.

`Mordell/` holds files copied unchanged from [AxiomMath/Mordell](https://github.com/AxiomMath/Mordell)
(Apache-2.0): abelian varieties (Pic⁰, φ_L, the theorem of the square) and ample sheaves over a
field. `MMP/` holds files copied from [AxiomMath/MMP](https://github.com/AxiomMath/MMP)
(Apache-2.0): nef divisors and numerical equivalence; one of them is ported to the pinned Stacks.
They are listed in [`NOTICE`](NOTICE), with the commit they come from.
