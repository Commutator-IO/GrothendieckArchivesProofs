/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.RingTheory.FinitePresentation
import Grothendieck.Attr

/-!
# Folder 161-2: pseudo-fields and residue fields; a join of subtopoi, not stated

Two rows of the edition's list of findings (`src/content/findings.ts`) for folder 161-2
(*Algèbre universelle*). The neighbouring problem p:noncoh (same folder) is in
`OpenProblems/TopoiStacks.lean`.

## Main definitions

* `RingHomOfResidueFields` (`161-2-pseudofield-opens-by-residue-fields`, pp. 41–42): for a
  finitely presented ring `A` and a von Neumann regular ring `R`, a ring map `A → R` exists as
  soon as every residue field of `R` receives one. Proved, as
  `Grothendieck.Folder161_2.ringHomOfResidueFields`
  (`Grothendieck/RingTheory/Folder161_2Pseudofield.lean`).

The row `161-2-definite-characteristic-join-of-subtopoi`, pp. 47–49, cannot be stated faithfully
with Mathlib and the Stacks library; what is missing is below.

## Not formalised

* `161-2-definite-characteristic-join-of-subtopoi`: the rings locally of characteristic `p` for
  some prime `p` or of characteristic `0` are classified by a subtopos of the classifying topos of
  rings which is not coherent and not presented by an open condition, but is the join of the open
  subtopos `X_{car > 0} = ⋃_p X_{ℤ/p}` and the non-open subtopos `X_ℚ = ⋂_n X_{ℤ[1/n]}`; and the
  join of two subtopoi `V, W` is obtained by gluing along an open under conditions on opens `Z'`
  of `V` and `Z''` of `W`. Status: candidate. Missing: the classifying topos of a geometric
  theory and the subtopoi classifying its quotient theories, coherent topoi, and the lattice of
  subtopoi with its joins; the Stacks library has subtopoi of a topos of sheaves, open and closed
  ones (`IsSubtopos`, `IsOpenSubtopos`, `IsClosedSubtopos`, Stacks 08LV, 08LX, 08LZ), but not the
  join. The gluing lemma of p. 48 (issue Commutator-IO/grothendieck-project#185) is proved in its
  order-theoretic core, in any distributive lattice, in `Grothendieck/Order/Folder161_2Join.lean`
  (`Grothendieck.Folder161_2.recollement_iff`, `Grothendieck.Folder161_2.recollement`): the two
  forms of the condition on the opens are equivalent, and they give Grothendieck's form
  `V = Z' ⊔ (Z'' ⊓ V)`, `W = Z'' ⊔ (Z' ⊓ W)`. Its instance on subtopoi is not stated: the libraries
  have no distributive lattice of subtopoi (or of Grothendieck topologies), no open subtopos
  `o(U)` as an element of it, and no gluing of subtopoi along an open cover; that file's header
  lists what is missing.

## References

* A. Grothendieck, folder 161-2, pp. 47–49, *Algèbre universelle* (finding
  `161-2-definite-characteristic-join-of-subtopoi`)
* Stacks Project, tags 08LV, 08LX, 08LZ
* A. Grothendieck, folder 161-2, pp. 41–42 (finding `161-2-pseudofield-opens-by-residue-fields`)
* P. T. Johnstone, *Sketches of an Elephant*, §A4.5
-/

@[expose] public section

namespace OpenProblems.Findings.Folder161_2

universe u v

/-- `161-2-pseudofield-opens-by-residue-fields` (folder 161-2, pp. 41–42, the open subtopoi of
the classifying topos of pseudo-fields described by fields). Let `A` be a finitely presented
commutative ring and `R` a commutative von Neumann regular ring (a pseudo-field: every `a` has
some `b` with `a² b = a`). If every residue field `R ⧸ 𝔪`, `𝔪` maximal, receives a ring map from
`A`, then so does `R`. The finite presentation cannot be dropped: the edition's note gives a
counterexample with `A` countably presented.

Status: proved, as `Grothendieck.Folder161_2.ringHomOfResidueFields`
(`Grothendieck/RingTheory/Folder161_2Pseudofield.lean`), as stated (issue
Commutator-IO/grothendieck-project#186).

Choices: « of finite presentation » is `Algebra.FinitePresentation ℤ A`; « von Neumann regular »
is the elementwise condition `∀ a, ∃ b, a * a * b = a`, as in
`Grothendieck/CategoryTheory/Folder161_2Classifying.lean` (Mathlib has no such class; Stacks'
`IsAbsolutelyFlat`, tag 092B, is equivalent); the residue fields are the quotients by maximal
ideals, which in a von Neumann regular ring are also its localisations at primes. The
counterexample is not formalised. -/
@[montpellier "161-2, 41–42"]
def RingHomOfResidueFields : Prop :=
  ∀ (A : Type u) (R : Type v) [CommRing A] [CommRing R] [Algebra.FinitePresentation ℤ A],
    (∀ a : R, ∃ b, a * a * b = a) →
    (∀ m : Ideal R, m.IsMaximal → Nonempty (A →+* R ⧸ m)) → Nonempty (A →+* R)

end OpenProblems.Findings.Folder161_2
