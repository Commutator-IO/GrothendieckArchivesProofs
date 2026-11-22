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
`OpenProblems/TopoiStacksNoncoh.lean` is the exception: it proves, by Łoś's theorem, a
first-order part of problem p:noncoh (the rings with prime nilradical, and the rings of
dimension `≤ 0`, are not the models of a first-order theory).

## Versions

Everything the build depends on is pinned in two files:

- `lean-toolchain`: Lean `v4.35.0` (elan installs it on the first `lake` command);
- `lake-manifest.json`: the exact commits of every dependency — Mathlib `56a0058`, the
  [Stacks project](https://github.com/AxiomMath/Stacks) `f56a316` (the Mathlib and Lean of
  Stacks), and their own dependencies. `lakefile.toml` names the two direct ones.

`Mordell/` and `MMP/` are copied files, not dependencies; their origin commits are in `NOTICE`.

## Building

From a clean clone, with [elan](https://github.com/leanprover/elan) installed:

```
lake exe cache get      # Mathlib's compiled files, from its cache
lake build              # everything else: the Stacks modules imported, and this repository
lake env lean --run scripts/CheckAxioms.lean GrothendieckArchivesProofs \
  GrothendieckArchivesProofs Grothendieck Buffalo OpenProblems Mordell MMP
```

`lake build` fails on any warning (`warningAsError = true`), so on any `sorry`. The last command
walks the dependencies of every constant of this repository, through Mathlib, Stacks and the
copied files, and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`.

**Cost.** The Stacks modules the proofs import have no cache and are compiled by the build:
several thousand modules. A cold build took 3 h 50 on GitHub's hosted runner (4 cores, 16 GB of
RAM plus 12 GB of swap, without which it ran out of memory) and 34 minutes on 32 cores with 128 GB. Count about
15 GB of disk for `.lake`. The axiom check takes about 5 minutes.

**Statements against proofs.** `Challenge/` holds trusted statements, written with Mathlib alone
and left unproved; `Solution/` proves the same statements through the libraries above.
`lake comparator` (configured in `comparator.json`, sandboxed with
[bubblewrap](https://github.com/containers/bubblewrap)) checks that each theorem of `Solution`
has exactly the statement of `Challenge`, is accepted by the kernel and uses only the three
axioms, so that no import of the proof can change what the statement means. One statement is
there so far (folder 19, page 80).

The continuous integration (`.github/workflows/build.yml`) runs these commands on every push
to `main`, on a self-hosted runner that keeps `main`'s `.lake` between runs, and on a pull request
when the label `ci` is added; `build-hosted.yml` is the same build on GitHub's runner, by hand.

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
`LeanPool/` holds files copied from [lean-pool](https://github.com/LeanPool/lean-pool)
(Apache-2.0), from Michel Hua's pull requests there: classifying topoi of geometric theories,
Diaconescu's theorem, theories of presheaf type, Morita equivalence, Boolean and De Morgan
presheaf topoi, subtopoi and essential points; twelve of them are ported from Lean v4.36 to the
pinned Lean and Mathlib. They are listed in [`NOTICE`](NOTICE), with the commit they come from.
