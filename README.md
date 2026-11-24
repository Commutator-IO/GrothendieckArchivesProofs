# Lean proofs of Grothendieck's archives

Lean 4 proofs of statements from two of Alexandre Grothendieck's archives, built on
[Mathlib](https://github.com/leanprover-community/mathlib4) and on
[the Stacks Project in Lean](https://github.com/AxiomMath/Stacks) (AxiomMath):

- `Grothendieck/`: the working notes kept at the University of Montpellier, in topic directories
  as in Mathlib (`AlgebraicGeometry/`, `RingTheory/`, `CategoryTheory/`, …), with the general
  lemmas they use in `LeanPool/` (see [Licence](#licence)). The files keep the name of their folder (cote),
  `Grothendieck/AlgebraicGeometry/Folder126Glue.lean` for instance, and each statement carries its
  source as an attribute (see [Conventions](#conventions)). The statements are the modernised
  readings of the edition [grothendieck-project](https://github.com/Commutator-IO/grothendieck-project),
  where each file is linked to its folder, its pages and its findings.
- `Buffalo/`: the lectures given at Buffalo in 1973, one file per part of their index, in the same
  topic directories (`AlgebraicGeometry/`, `CategoryTheory/`), the lecture series (`AG`, `Groupes`,
  `Topos`) prefixing the file name: `Buffalo/CategoryTheory/ToposPart03a.lean` for instance.

The Montpellier statements and their proofs, written out in French, are in the preprint
M. Hua, *Grothendieck Montpellier. Énoncés des lectures modernisées démontrés*, Hexagon
[2611.00125v3](https://hexagonmath.org/pdf/2611.00125v3).

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
  Stacks), [Mordell](https://github.com/AxiomMath/Mordell) `82a30cb` (built against that Stacks,
  not its own pin `c496df0`), and their own dependencies. `lakefile.toml` names the three direct
  ones.

`MMP/` is copied, not a dependency (one of its files needs a port to the pinned Stacks); its origin
commit is in `NOTICE`.

## Building

From a clean clone, with [elan](https://github.com/leanprover/elan) installed:

```
lake exe cache get      # Mathlib's compiled files, from its cache
lake build              # everything else: the Stacks modules imported, and this repository
lake env lean --run scripts/CheckAxioms.lean GrothendieckArchivesProofs \
  GrothendieckArchivesProofs Grothendieck Buffalo OpenProblems Mordell MMP LeanPool
```

`lake build` fails on any warning (`warningAsError = true`), so on any `sorry`. The last command
walks the dependencies of every constant of this repository, through Mathlib, Stacks and the
copied files, and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`.

**Cost.** The Stacks modules the proofs import have no cache and are compiled by the build:
several thousand modules. A cold build took 3 h 50 on GitHub's hosted runner (4 cores, 16 GB of
RAM plus 12 GB of swap, without which it ran out of memory) and 34 minutes on 32 cores with 128 GB
(expect about four times that, a little over 2 hours, on the 8 cores the runner has since
2026-11-23). The compilation peaks at
26 GB of RAM. Count about 40 GB of disk for `.lake`. The axiom check takes about 6 minutes.

**Statements against proofs.** `Challenge.lean` holds trusted statements, in one file that imports
Mathlib alone, left unproved; `Solution/` proves the same statements through the libraries above.
`lake comparator` (configured in `comparator.json`, sandboxed with
[bubblewrap](https://github.com/containers/bubblewrap)) checks that each theorem of `Solution`
has exactly the statement of `Challenge`, is accepted by the kernel and uses only the three
axioms, so that no import of the proof can change what the statement means. There are 41 such
statements, from 31 folders and from problem 3 of the Buffalo lectures. `comparator.json` and
`formalization.yaml` follow the rules of the [Palomar Registry](https://palomar-registry.org/)
(a Challenge of at most 1,000 lines importing Mathlib alone, a `module` header in every Lean file).

The continuous integration (`.github/workflows/build.yml`) runs these commands on every push
to `main`, on a self-hosted runner that keeps `main`'s `.lake` between runs, and on a pull request
when the label `ci` is added; `build-hosted.yml` is the same build on GitHub's runner, by hand.
The runner is an Azure VM with 8 cores and 32 GB (Commutator-IO/ai-infra, `stacks/lean-ci`),
started by the workflow and deallocated by itself after 10 idle minutes. After the build, the
five checks (axioms, statement definitions, duplicates, source index, comparator) each use one
core, so they run side by side in a single step: about 8 minutes instead of 25. When the build
only replays modules, a run takes 11 to 17 minutes, the longer when the VM has just changed host
and its disk cache is cold.

## Conventions

The repository follows the layout of AxiomMath's projects built on Stacks
([Weil](https://github.com/AxiomMath/Weil), [Mordell](https://github.com/AxiomMath/Mordell)) and of
Mathlib (#39):

- **Style.** The libraries build with Mathlib's options (`autoImplicit = false`,
  `relaxedAutoImplicit = false`, `maxSynthPendingDepth = 3`) and its linter set
  (`weak.linter.mathlibStandardSet`), warnings being errors. Module docstrings have Mathlib's
  shape: a summary, then Main results, Implementation notes and References.
- **Sources.** `@[montpellier "cote, page"]` and `@[buffalo "entry"]` (`Grothendieck/Attr.lean`)
  record the folder and page, or the Buffalo index entry, of a statement; Stacks' `@[ega …]` and
  `@[sga …]` mark a declaration that proves that EGA or SGA item. `scripts/SourceIndex.lean` lists
  the declarations by source, and the CI keeps the list as an artifact.
- **Topic tree.** `scripts/restructure.py` moved the folder files into topic directories;
  `docs/review/restructure-map.md` maps each old path to the new one.
- **What is already in the libraries.** `scripts/FindDuplicates.lean` compares every statement of
  this repository with those of Mathlib and Stacks (same statement, or a library theorem applied
  to some of the hypotheses); the CI keeps its report, `duplicates.md`. A proof that redoes a
  library theorem is replaced by it, and the name stays, since the edition cites it.
- **Kernel replay.** `.github/workflows/kernel-check.yml` replays every constant of the
  repository's own libraries through Lean's kernel, and runs `lake comparator --paranoid` (the
  independent kernels) on the statements of `Challenge.lean`; it runs weekly and by hand.

The proofs were golfed in #69: unneeded `show` and `change` removed, one-call `simp`, `grind` and
`omega` where they do not slow the build, and near-duplicate lemmas merged; open work is tracked in
the issues.

## Licence

[Apache 2.0](LICENSE). The same proofs are under CC0 in grothendieck-project. Short quotations of
the manuscripts in comments, in « », are not covered: the rights in Grothendieck's manuscripts are
held by his heirs.

[AxiomMath/Mordell](https://github.com/AxiomMath/Mordell) (Apache-2.0) is a dependency: its abelian
varieties (Pic⁰, φ_L, the theorem of the square) and ample sheaves over a field serve the Buffalo
lectures. `MMP/` holds files copied from [AxiomMath/MMP](https://github.com/AxiomMath/MMP)
(Apache-2.0): nef divisors and numerical equivalence; one of them is ported to the pinned Stacks.
`LeanPool/` holds files copied from [lean-pool](https://github.com/LeanPool/lean-pool)
(Apache-2.0), from Michel Hua's pull requests there: classifying topoi of geometric theories,
Diaconescu's theorem, theories of presheaf type, Morita equivalence, Boolean and De Morgan
presheaf topoi, subtopoi and essential points; twelve of them are ported from Lean v4.36 to the
pinned Lean and Mathlib. It also holds, at lean-pool's paths, the 25 general lemmas of the
Montpellier proofs that Michel Hua contributed to lean-pool (`CategoryTheoryToolkit/`,
`CommutativeAlgebraToolkit/`, `LinearAlgebraCombinatoricsAndAnalysis/`), in this repository's
version, which differs from lean-pool's in style and in a few declarations. They are listed in
[`NOTICE`](NOTICE), with the commit they come from.
