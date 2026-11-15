import Mathlib
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationStalkSets

/-!
# Does the étale topos remember the scheme? (p:etrec), stated as a proposition

Section « A statement the literature has largely settled » of the note on the open problems of
the Montpellier notes (`docs/problems/article.tex`): problem p:etrec. Nothing here is proved; a
`def … : Prop` asserts nothing.

The étale topos of `X` is `Sheaf X.smallEtaleTopology (Type (u + 1))`; a morphism `f : X ⟶ Y`
induces the inverse image `f⁻¹ = Stacks.EtaleCohomology.smallEtalePullbackSet f` of the Stacks
library, left adjoint to the direct image, and `Stacks.EtaleCohomology.smallEtalePullbackSetCompIso`
compares `f⁻¹ ∘ g⁻¹` with `(f ≫ g)⁻¹`. A 2-isomorphism between the morphisms of topoi `f_et` and
`g_et` is a natural isomorphism of their inverse images; it lies *over* `S_et` when its whiskering
by the inverse image along `Y → S` agrees, through these comparisons, with the identity of the
inverse image along `X → S`.

## Stated

* `EtaleToposFaithful`: the page's « 1-faithful », over a locally noetherian base. Faithful to
  the page; probably false as it stands (see its docstring).
* `EtaleToposFaithfulCharZero`: the same over a base of characteristic `0`, as the margin asks.

## Not stated, and what is missing

* The full faithfulness, « peut-être », in the category of fractions inverting the universal
  homeomorphisms, on morphisms of topoi sending closed points to closed points: Mathlib and Stacks
  have no category of fractions of schemes at the universal homeomorphisms with its functor to
  topoi, and no notion of the points of a topos being closed; the pinned morphisms of Carlson,
  Haine and Wolf are not in either library.
-/

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace OpenProblems.EtaleTopos

/-- The natural isomorphism `α : f⁻¹ ≅ g⁻¹` of inverse images on étale sheaves of sets is a
2-isomorphism over `S_et`, for `S`-morphisms `f, g : X ⟶ Y` (`f ≫ q = p`, `g ≫ q = p`): its
whiskering by `q⁻¹`, composed with `(g ≫ q)⁻¹ = p⁻¹`, is the comparison `q⁻¹ ⋙ f⁻¹ ≅ (f ≫ q)⁻¹ = p⁻¹`. -/
def IsOverBase {S X Y : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S} {f g : X ⟶ Y} (hf : f ≫ q = p)
    (hg : g ≫ q = p) (α : smallEtalePullbackSet f ≅ smallEtalePullbackSet g) : Prop :=
  isoWhiskerLeft (smallEtalePullbackSet q) α ≪≫ smallEtalePullbackSetCompIso g q ≪≫
      eqToIso (congrArg smallEtalePullbackSet hg) =
    smallEtalePullbackSetCompIso f q ≪≫ eqToIso (congrArg smallEtalePullbackSet hf)

/-- **p:etrec, faithfulness** (folder 149, pp. 50–51; undated, group dated [from 1978]–1983).
Over a locally noetherian scheme `S`, the functor `X ↦ X_et` from reduced `S`-schemes locally of
finite presentation to topoi over `S_et` is « 1-faithful »: two `S`-morphisms `f, g : X ⟶ Y`
whose morphisms of étale topoi are 2-isomorphic over `S_et` are equal.

Status: largely settled in the literature, by Voevodsky (1990) for `X` normal of finite type over
a field finitely generated of characteristic `0`, and by Carlson, Haine and Wolf (2024 preprint)
for finite-type schemes over a finitely generated infinite field, with pinned morphisms and the
universal homeomorphisms inverted (their Theorem 0.1; faithfulness for `S` qcqs, Jacobson, `X`
reduced with reduced fibres, Theorem 3.9 and Corollary 3.10). The general base is open.

Our remark, unchecked by a specialist: as stated, without a condition on the characteristic, it
looks false over `S = Spec 𝔽_p`, since the absolute Frobenius of a reduced `𝔽_p`-scheme of finite
type is an `𝔽_p`-morphism acting on the small étale topos as the identity (compatibly with the
base, whose Frobenius is the identity); this may be why the margin asks « `S` de car. 0 ? ». See
`EtaleToposFaithfulCharZero`. -/
def EtaleToposFaithful : Prop :=
  ∀ (S X Y : Scheme.{u}) [IsLocallyNoetherian S] (p : X ⟶ S) (q : Y ⟶ S) [IsReduced X]
    [IsReduced Y] [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q] (f g : X ⟶ Y)
    (hf : f ≫ q = p) (hg : g ≫ q = p) (α : smallEtalePullbackSet f ≅ smallEtalePullbackSet g),
    IsOverBase hf hg α → f = g

/-- **p:etrec, faithfulness in characteristic `0`** (folder 149, p. 51, margin « `S` de car.
0 ? »): `EtaleToposFaithful` for a locally noetherian base `S` over `Spec ℚ`.

Status: as for `EtaleToposFaithful`; open for a general locally noetherian base of characteristic
`0` (for instance a scheme of finite type over `ℚ` that is not a field), as far as the note
found. -/
def EtaleToposFaithfulCharZero : Prop :=
  ∀ (S X Y : Scheme.{u}) [IsLocallyNoetherian S], Nonempty (S ⟶ Spec (CommRingCat.of (ULift ℚ))) →
    ∀ (p : X ⟶ S) (q : Y ⟶ S) [IsReduced X] [IsReduced Y] [LocallyOfFinitePresentation p]
    [LocallyOfFinitePresentation q] (f g : X ⟶ Y) (hf : f ≫ q = p) (hg : g ≫ q = p)
    (α : smallEtalePullbackSet f ≅ smallEtalePullbackSet g), IsOverBase hf hg α → f = g

end OpenProblems.EtaleTopos
