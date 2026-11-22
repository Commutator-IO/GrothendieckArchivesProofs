/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Category.Cat.Colimit
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Types
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The questions of the Buffalo lectures (1973), stated as propositions

The source is the note on the open problems of the Buffalo lectures
(`docs/buffalo-open/article.tex` in the edition's repository): thirteen `problem` environments and
its section « Effectivity ». Each question that the libraries can express is a `def … : Prop`;
nothing here is proved, and a `def` asserts nothing. Each docstring gives the question in our
words, its label, its source (YouTube video id and time), its status as the note gives it, and the
choices made in writing it down. Most of these questions are settled, several against the
lecturer's expectation; the `Prop` then states *his* expectation, and the docstring says that it
is false and why. The arguments of the note marked as the edition's own have not been checked by
a specialist.

## Stated

* `PresheafToposConjecture` (p:presheaf): false.
* `PushforwardWithRightAdjointIsEquivalence` (p:fshriek): false.
* `ColimitOfSmallAccessibleIsAccessible` (p:colim): a special case (strict colimits of small
  categories); false.
* `ReflectiveLimitClosedIsAccessible` (p:reflective): open in ZFC as far as the note knows.
* `AccessibleSelfDualIsPoint` (p:dual): false.
* `ImmersionDescendsFpqc` (p:immersion, first question): false.
* `FiniteEquivalenceRelationsEffective` (§ Effectivity): false (Venken 1971).

## Not stated, and what is missing

* p:classifying (classifying topoi of algebraic structures): Mathlib has no geometric theories,
  classifying topoi or homotopy types of topoi. The note records the programme as carried out
  for geometric theories.
* p:exactness (exactness properties as factorisation conditions): « exactness property » is not
  a formal notion; the note points to the exactness sequents of Jacqmin and Janelidze, which are
  not in Mathlib. The side remark that « every semigroup object is a monoid » forces the category
  to be trivial is elementary, but it answers rather than states the question.
* p:representable, p:envelope: the 2-category `Cat_D` of categories with `D`-limits, the notion
  of algebraic theory relative to `D` obtained stepwise, and free `D`-completions and
  localisations in `Cat_D` are not in Mathlib.
* p:three (« problem three »): what remains open is the converse for mixed large classes `D`
  (finite limits together with all colimits, say), which needs the notions « basic » and
  « algebraic » relative to `D`; they are not formalised. `Buffalo/ProblemThree.lean` proves the
  concrete halves of the counterexample `{2} → Set` for all small limits: every set is in
  bijection with an equaliser of maps between powers of `2` (`equivEqualizer`), the saturation of
  `{2}` under limits is everything at its second stage and misses `Fin 3` at its first
  (`saturation_two`, `not_saturation_one`), condition (G) holds (`conditionG`), and `2` is not
  presentable in `Setᵒᵖ` (`not_isCardinalPresentable`, `not_isPresentable`). That `Set` is not
  algebraic, which uses Kelly's sketches, is not formalised there.
* p:perrin (« the main conjecture » on group schemes over a field, proved by Perrin 1976):
  stating it needs fppf quotients of group schemes, or filtered limits in the category of group
  schemes over a field with affine transition maps; Mathlib has group objects in `Over (Spec k)`
  but neither quotients nor that limit theory.
* p:qcoh (descent of quasi-coherent sheaves along universal effective epimorphisms of schemes):
  Mathlib has no category of descent data for quasi-coherent sheaves along a morphism of schemes.
  The open part is effectivity along a universal effective epimorphism that is not
  quasi-compact, in ZFC alone. `Buffalo/QcohDescent.lean` proves the affine core of full
  faithfulness: if `N → B ⊗_A N ⇉ B ⊗_A B ⊗_A N` is an equaliser, base change on homomorphisms
  into `N` is bijective (`descend_bijective`), with the converse for `M = A`
  (`isEqualizer_iff_bijective`) and the equivalence of the condition for all modules with
  purity (`equalizerCondition_iff_isPure`).
* The second question of p:immersion (exactness of descent of subschemes without
  retrocompactness) is stated loosely in the lecture; the same counterexample answers it, and
  it is not written separately.
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe v u

namespace OpenProblems.Buffalo

/-! ## Topoi -/

section Topoi

variable (E : Type u) [Category.{v} E]

/-- Condition (A) of the note on p:presheaf: an arbitrary (small) product of epimorphisms is an
epimorphism. -/
def ProductsOfEpisAreEpi [HasLimitsOfSize.{v, v} E] : Prop :=
  ∀ (ι : Type v) (X Y : ι → E) (f : ∀ i, X i ⟶ Y i), (∀ i, Epi (f i)) → Epi (Limits.Pi.map f)

/-- Condition (B) of the note on p:presheaf: arbitrary (small) products distribute over arbitrary
sums, that is, the canonical map `∐_{s ∈ ∏ᵢ Iᵢ} ∏ᵢ X i (s i) ⟶ ∏ᵢ ∐_{j ∈ Iᵢ} X i j` is an
isomorphism. -/
def ProductsDistributeOverCoproducts [HasLimitsOfSize.{v, v} E] [HasColimitsOfSize.{v, v} E] :
    Prop :=
  ∀ (ι : Type v) (I : ι → Type v) (X : ∀ i, I i → E),
    IsIso (Sigma.desc fun s : (∀ i, I i) =>
      (Limits.Pi.map fun i => Sigma.ι (X i) (s i) : ∏ᶜ (fun i => X i (s i)) ⟶ ∏ᶜ fun i => ∐ X i))

end Topoi

/-- **p:presheaf** (topos course, video `PqCQM3Pcl6Q`, 1:26:22 and 7:31:23). Grothendieck
suspected that the presheaf topoi are exactly the topoi sharing all the exactness properties of
`Set`, including the infinitary ones: products of epimorphisms epimorphic, products distributive
over sums. Stated here for the Grothendieck topoi `Sheaf J (Type u)` on a small site: if they
satisfy (A) `ProductsOfEpisAreEpi` and (B) `ProductsDistributeOverCoproducts`, they are
equivalent to presheaves on a small category.

Status: false, by the note's own argument (not checked by a specialist). The sheaves on `[0,1)`
for the topology of the intervals `[0,a)` satisfy (A) and (B), since that frame is a complete
chain, but have no nonzero projective object. The note identifies the topoi with (A) and (B) as
the essential subtopoi of presheaf topoi, and the totally distributive topoi of Rosebrugh and
Wood (Lucyshyn-Wright, 1.5.5).

Choice: the exactness properties « of `Set` » are read as exactly (A) and (B), the two the
lecture names; universes are those of the site (`C : Type u`, sheaves of `Type u`). -/
def PresheafToposConjecture : Prop :=
  ∀ (C : Type u) [SmallCategory C] (J : GrothendieckTopology C),
    ProductsOfEpisAreEpi (Sheaf J (Type u)) →
    ProductsDistributeOverCoproducts (Sheaf J (Type u)) →
    ∃ (D : Type u) (_ : SmallCategory D), Nonempty (Sheaf J (Type u) ≌ (Dᵒᵖ ⥤ Type u))

/-- **p:fshriek** (topos course, video `PqCQM3Pcl6Q`, 4:05:50). Grothendieck had « a feeling » that
the direct image `f_*` of a morphism of topoi cannot have a right adjoint `f^!` on sheaves of sets
unless `f` is an equivalence. Stated for morphisms of topoi (`MorphismOfTopoi` of the Stacks
library: an adjunction `f⁻¹ ⊣ f_*` with `f⁻¹` left exact) between sheaf topoi on small sites.

Status: false. For the open point of the Sierpiński space, `j_*` is the diagonal `A ↦ (A → A)`
and has the global-sections functor as right adjoint; more generally the global-sections functor
of presheaves on a category with a terminal object has a right adjoint (local topoi, Johnstone and
Moerdijk 1989). -/
def PushforwardWithRightAdjointIsEquivalence : Prop :=
  ∀ (C D : Type u) [SmallCategory C] [SmallCategory D] (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u))),
    f.pushforward.IsLeftAdjoint → f.pushforward.IsEquivalence

/-! ## Accessible categories -/

/-- **p:colim**, special case (video `4gynb9uTEE4`, 1:31:03). The question: is a small 2-colimit
in `Cat` of accessible categories accessible? Stated here only for *strict* colimits of *small*
categories, in Mathlib's `Cat.{v, v}`, with no condition on the functors of the diagram: a special
case, chosen because Mathlib has strict colimits of small categories and no 2-colimits.

Status: false, by the note's own example, which is a strict pushout of small categories along
accessible functors and so refutes this special case too: the free category on `a : u → v`,
`b : v → w`, `h : u → w`, mapped to the chain `0 < 1 < 2` and to the free monoid on `t` (`a, b, h ↦ t`),
has as pushout the one-object category with endomorphisms `{1, t}`, `t = t²`, in which the
idempotent `t` does not split. Directed colimits along accessible full embeddings are accessible
(Paré and Rosický 2013). -/
def ColimitOfSmallAccessibleIsAccessible : Prop :=
  ∀ (I : Type v) [SmallCategory I] (F : I ⥤ Cat.{v, v}),
    (∀ i, IsAccessibleCategory.{v} (F.obj i)) → IsAccessibleCategory.{v} (colimit F : Cat.{v, v})

/-- **p:reflective** (video `4gynb9uTEE4`, 1:51:31). Is a full subcategory of an accessible
category, closed under (small) limits and whose inclusion has a left adjoint, itself accessible?

Status: open in ZFC alone, as far as the note found. Yes when the inclusion is moreover accessible
(for a locally presentable ambient category, Adámek and Rosický 2.78), and yes under Vopěnka's
principle for a locally presentable ambient category (Adámek and Rosický, ch. 6).

Choices: « accessible » is Mathlib's `IsAccessibleCategory.{v}` (κ-accessible for some regular
`κ`, cardinals in the universe of the morphisms); « stable under limits » is closure under limits
of every small shape, which also makes the subcategory replete. -/
def ReflectiveLimitClosedIsAccessible : Prop :=
  ∀ (C : Type u) [Category.{v} C] [IsAccessibleCategory.{v} C] (P : ObjectProperty C),
    (∀ (J : Type v) [SmallCategory J], P.IsClosedUnderLimitsOfShape J) →
    P.ι.IsRightAdjoint → IsAccessibleCategory.{v} P.FullSubcategory

/-- **p:dual** (video `4gynb9uTEE4`, 4:48:17). Grothendieck guessed that a category `E` such that
`E` and `Eᵒᵖ` are both accessible is equivalent to the point.

Status: false: the two-element chain is small and idempotent complete, as is its opposite, so
both are accessible. With small colimits in `E` (his setting) `E` is a complete lattice
(Gabriel and Ulmer, Satz 7.13). -/
def AccessibleSelfDualIsPoint : Prop :=
  ∀ (E : Type u) [Category.{v} E], IsAccessibleCategory.{v} E → IsAccessibleCategory.{v} Eᵒᵖ →
    Nonempty (E ≌ Discrete PUnit.{u + 1})

/-! ## Algebraic geometry -/

/-- **p:immersion**, first question (algebraic geometry course, video `vuys5SNs2eQ`, 3:31:11; see
also 2:59:31). Grothendieck believed that immersions which are not quasi-compact still descend
along a faithfully flat quasi-compact morphism: if `X' → X` is flat, surjective and quasi-compact
and the base change `Z ×_X X' → X'` of `i : Z → X` is an immersion, `i` is an immersion.

Status: false. Open, closed and quasi-compact immersions descend along fpqc coverings and all
immersions along fppf ones (Stacks 02L3, 02L6, 02L8, 02YM), but the disjoint union of the
`Spec 𝔽_p` over `Spec ℤ` is not an immersion and becomes one after the faithfully flat base change
`Spec ∏_p ℤ_(p) → Spec ℤ` (a comment of August 2026 on Stacks tag 02YL, not refereed; the note
found no earlier published counterexample).

Choice: the base change is `pullback.snd i p`, and the hypothesis on `p` is Mathlib's `Flat`,
`Surjective` and `QuasiCompact`. -/
def ImmersionDescendsFpqc : Prop :=
  ∀ {X X' Z : Scheme.{u}} (p : X' ⟶ X) (i : Z ⟶ X), Flat p → Surjective p → QuasiCompact p →
    IsImmersion (pullback.snd i p) → IsImmersion i

/-! ## Effectivity -/

section Effectivity

variable (k : Type u) [Field k] (B : Type u) [CommRing B] [Algebra k B]

/-- `b ↦ b ⊗ 1 - 1 ⊗ b`. -/
noncomputable def diag : B →ₗ[k] B ⊗[k] B :=
  (TensorProduct.mk k B B).flip 1 - TensorProduct.mk k B B 1

/-- The projections `pr₁₂, pr₁₃, pr₂₃ : X × X × X → X × X` for `X = Spec B`, on rings, with
`B ⊗ B ⊗ B` bracketed as `B ⊗ (B ⊗ B)`. -/
noncomputable def pr₁₂ : B ⊗[k] B →ₐ[k] B ⊗[k] (B ⊗[k] B) :=
  Algebra.TensorProduct.productMap Algebra.TensorProduct.includeLeft
    (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft)

@[inherit_doc pr₁₂]
noncomputable def pr₁₃ : B ⊗[k] B →ₐ[k] B ⊗[k] (B ⊗[k] B) :=
  Algebra.TensorProduct.productMap Algebra.TensorProduct.includeLeft
    (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight)

@[inherit_doc pr₁₂]
noncomputable def pr₂₃ : B ⊗[k] B →ₐ[k] B ⊗[k] (B ⊗[k] B) :=
  Algebra.TensorProduct.productMap
    (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft)
    (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight)

/-- The closed subscheme `R = V(I)` of `X × X`, `X = Spec B`, is an equivalence relation: it
contains the diagonal, is symmetric, and `pr₁₃(R ×_X R) ⊆ R`, written on ideals. -/
def IsEquivalenceRelationIdeal (I : Ideal (B ⊗[k] B)) : Prop :=
  I ≤ RingHom.ker (Algebra.TensorProduct.lmul' k (S := B)) ∧
    I.map (Algebra.TensorProduct.comm k B B) ≤ I ∧
    I.map (pr₁₃ k B) ≤ I.map (pr₁₂ k B) ⊔ I.map (pr₂₃ k B)

/-- The relation `V(I)` is effective: `I` is the ideal of `X ×_{X/R} X`, generated by the
`b ⊗ 1 - 1 ⊗ b` with `b` in the ring of invariants `B^R = {b | b ⊗ 1 - 1 ⊗ b ∈ I}`. -/
def IsEffectiveIdeal (I : Ideal (B ⊗[k] B)) : Prop :=
  I = Ideal.span (diag k B '' {b | diag k B b ∈ I})

end Effectivity

/-- **§ Effectivity** (group-schemes video `3ULFIl_2Wis`, 6:59:50). Asked for open problems,
Grothendieck gave the question of FGA (1961): is every finite equivalence relation on a finite
scheme over a field effective? He suspected not. Stated for `X = Spec B`, `B` a finite
`k`-algebra, and a closed equivalence relation `R = V(I) ⊆ X × X`; `R` is then finite over `X`,
and the quotient `X/R = Spec B^R` exists, so effectivity is `I = J_{B^R}`.

Status: false over every field, by Venken (C. R. Acad. Sci. Paris 272 (1971), Corollary 3.1), on
a local Artin algebra of dimension 33. The repository checks Venken's example in
`Grothendieck/EffectiveVenken.lean` (`venken_not_effective`, there for the specific algebra
`B K` and its ideal `venkenRel K`, with the same projections and invariants as here); the
deduction of `¬ FiniteEquivalenceRelationsEffective` from it, which needs `B K` finite over `K`,
is not written. A second example, of length 15, is in the edition's note on effectivity. -/
def FiniteEquivalenceRelationsEffective : Prop :=
  ∀ (k : Type u) [Field k] (B : Type u) [CommRing B] [Algebra k B], Module.Finite k B →
    ∀ I : Ideal (B ⊗[k] B), IsEquivalenceRelationIdeal k B I → IsEffectiveIdeal k B I

end OpenProblems.Buffalo
