module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Torsor

@[expose] public section

/-!
# Folder 45: surjectivity of `H¹` over a field of dimension `≤ 1`, stated as a proposition

The open row `45-h1-surjectivity-dim-one` of the edition's list of findings
(`src/content/findings.ts`), folder 45, pp. 3–10. Nothing here is proved; a `def … : Prop`
asserts nothing.

The flat cohomology set `H¹(k, G)` of an algebraic group `G` over a field `k` is the set of
isomorphism classes of fppf torsors under `G`; a torsor under a group scheme of finite type over a
field is representable, so these are the `G`-schemes `X` over `k` with
`AlgebraicGeometry.IsFppfTorsor` of the Stacks library (Stacks 0498, 049A: the shear map is an
isomorphism and `X` is trivial after an fppf covering). For a homomorphism `φ : G → G'`, the map
`H¹(k, G) → H¹(k, G')` sends `X` to the contracted product `X ∧^G G'`, and a `G'`-torsor `X'` is
of that form exactly when there is a `G`-torsor `X` with a morphism `X → X'` equivariant along
`φ`. Surjectivity is stated in that form, which needs no contracted product.

## Stated

* `H1Surjective`: the reading's statement of the Théorème of p. 9.

## Not stated, and what is missing

* The lemmas of the reduction (normalisers of maximal tori, Cartan subalgebras of radicial
  kernels, the dévissage of Lemma 5): Mathlib and Stacks have no maximal tori of group schemes or
  Cartan subalgebras of restricted Lie algebras.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe u

namespace OpenProblems.Findings.Folder45

/-- `f : X ⟶ X'` is equivariant along `φ : G ⟶ G'` for actions of `G` on `X` and of `G'` on
`X'`. -/
def IsEquivariantAlong {S : Scheme.{u}} {G G' X X' : Over S} [GrpObj G] [GrpObj G'] [ModObj G X]
    [ModObj G' X'] (φ : G ⟶ G') (f : X ⟶ X') : Prop :=
  ModObj.smul (M := G) (X := X) ≫ f = (φ ⊗ₘ f) ≫ ModObj.smul (M := G') (X := X')

/-- `Br(k') = 0` for every finite separable extension `k'` of `k`, the reading's form of Serre's
« dimension `≤ 1` ». -/
def BrauerTrivialFiniteSeparable (k : Type u) [Field k] : Prop :=
  ∀ (k' : Type u) [Field k'] [Algebra k k'], FiniteDimensional k k' → Algebra.IsSeparable k k' →
    Subsingleton (BrauerGroup.{u, u} k')

/-- `45-h1-surjectivity-dim-one` (folder 45, pp. 3–10; Théorème of p. 9). Over a field `k` with
`Br(k') = 0` for every finite separable extension `k'/k`, the map `H¹(k, G) → H¹(k, G')` of flat
cohomology is surjective for every epimorphism `G → G'` of algebraic group schemes over `k`, not
necessarily smooth, linear or with commutative kernel.

Status: unsearched. For `G` smooth connected linear it is the matched case (Serre's Conjecture I,
Steinberg 1965, Borel–Springer 1968). The folder carries a reduction scheme, not a proof: Lemma 4
invokes a conjugacy theorem for Cartan subalgebras that the page does not establish in the form
needed and that fails in general in characteristic `p`.

Choices: much of the statement is the reading's: « `cd(k) ≤ 1` » on the page is replaced by
Serre's « dimension `≤ 1` », written as the vanishing of the Brauer groups of the finite separable
extensions (Mathlib's `BrauerGroup`, over the universe of `k`). An algebraic group scheme is a
group object of finite type over `Spec k`; an epimorphism is a faithfully flat homomorphism (flat
and surjective). `H¹` surjective is « every `G'`-torsor receives a `G`-torsor equivariantly », as
in the module docstring. -/
def H1Surjective : Prop :=
  ∀ (k : Type u) [Field k], BrauerTrivialFiniteSeparable k →
    ∀ (G G' : Over (Spec (CommRingCat.of k))) [GrpObj G] [GrpObj G']
      [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [LocallyOfFiniteType G'.hom]
      [QuasiCompact G'.hom] (φ : G ⟶ G') [IsMonHom φ] [Flat φ.left] [Surjective φ.left]
      (X' : Over (Spec (CommRingCat.of k))) [ModObj G' X'], IsFppfTorsor _ G' X' →
      ∃ (X : Over (Spec (CommRingCat.of k))) (_ : ModObj G X) (f : X ⟶ X'),
        IsFppfTorsor _ G X ∧ IsEquivariantAlong φ f

end OpenProblems.Findings.Folder45
