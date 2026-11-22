/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Buffalo.AG.Part05b
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
import Grothendieck.Attr

/-!
# Buffalo, algebraic geometry, part 05: the relative spectrum of a quasi-coherent algebra

Entries `thSz9ZHDK9o-33684` and `thSz9ZHDK9o-33941` of `docs/buffalo-ag/index.tex`, which
`Part05b.lean` treats over an affine base only, Mathlib (at `715a03a`) having no quasi-coherent
algebras and no relative spectrum. They are completed here with the vendored AxiomMath/Stacks
files of `StacksFrontier/AlgebraicGeometry/RelativeSpec/` and their imports (Apache-2.0, see
`lean/Stacks/NOTICE.md`).

## Main definitions

* a *relative spectrum situation* `s` (`Stacks.RelativeSpec.RelativeSpecSituation`, tag 01LM) is
  a scheme `S = s.base` with a quasi-coherent sheaf `𝒜 = s.algebra` of commutative
  `𝒪_S`-algebras;
* `Stacks.RelativeSpec.relativeSpecFunctor s` sends `T` to the pairs `(f : T ⟶ S, 𝒜 ⟶ f_*𝒪_T)`
  of a morphism and a map of `𝒪_S`-algebras, which by adjunction are the `𝒪_T`-algebra maps
  `f^*𝒜 ⟶ 𝒪_T` of the lecture.

## Main results

* the scheme `(gluedSpectrum s).scheme`, glued from the `Spec Γ(U, 𝒜)` over the affine opens
  `U ⊆ S`, represents it (tags 01LU, 01LV), and its restriction over every affine open `U` is
  `Spec Γ(U, 𝒜)` (the cartesian squares of the gluing, tag 01LP).
* Entries `34263` and `34520` (schemes affine over `S` and the anti-equivalence with
  quasi-coherent algebras, which `Part05b.lean` proves over an affine base) follow from the same
  files: `isQuasicoherent_pushforwardAlgebra` (`f_*𝒪_X` is quasi-coherent for `f` affine, half of
  tag 02KG) and `affineQuasicoherentEquivalence` (tag 01SA), whose essential surjectivity sends
  `𝒜` to its relative spectrum, affine over `S`.

## References

* the Buffalo lectures on algebraic geometry (1973), entries `thSz9ZHDK9o-33684`,
  `thSz9ZHDK9o-33941`, `34263`, `34520` (`docs/buffalo-ag/index.tex`)
* Stacks Project, tags 01LM, 01LU, 01LV, 01LP, 02KG, 01SA
-/

@[expose] public section


open AlgebraicGeometry CategoryTheory Limits Stacks.RelativeSpec

universe u

namespace Buffalo.AG.Part05

/-- thSz9ZHDK9o-33684 (9:21:24) [def] For a quasi-coherent `𝒪_S`-algebra `𝒜`, the functor
`Spec(𝒜) : S' ↦ {(f : S' ⟶ S, 𝒜 ⟶ f_*𝒪_{S'})}` (Stacks' `relativeSpecFunctor`); over an affine
base it is the functor of points of `Spec A` (`def_33684`). -/
@[buffalo "thSz9ZHDK9o-33684"]
noncomputable abbrev def_33684_relative (s : RelativeSpecSituation.{u}) :
    Scheme.{u}ᵒᵖ ⥤ Type u :=
  relativeSpecFunctor s

/-- thSz9ZHDK9o-33941 (9:25:41) [prop] The functor `Spec(𝒜)` of a quasi-coherent
`𝒪_S`-algebra is representable by an `S`-scheme `π : X ⟶ S`, and over every affine open
`U ⊆ S` the inverse image `π⁻¹(U)` is `Spec Γ(U, 𝒜)`: the chart `Spec Γ(U, 𝒜) ⟶ X` and the
inclusion `U ⟶ S` form a cartesian square over `π`. Stacks tags 01LP, 01LU. (That the functor
is a Zariski sheaf, which follows from representability, is not restated.) -/
@[buffalo "thSz9ZHDK9o-33941"]
theorem prop_33941_relative (s : RelativeSpecSituation.{u}) :
    (def_33684_relative s).IsRepresentable ∧
      Nonempty ((def_33684_relative s).RepresentableBy (gluedSpectrum s).scheme) ∧
      ∀ U : s.base.affineOpens,
        IsPullback ((gluedSpectrum s).chart U) (specSectionsToOpen s U) (gluedSpectrum s).toBase
          U.1.ι :=
  ⟨relativeSpecFunctor_isRepresentable s, ⟨relativeSpecRepresentableBy s⟩,
    (gluedSpectrum s).chart_isPullback⟩

open Stacks.AffineAlgebraEquivalence in
/-- thSz9ZHDK9o-34520 (9:35:20) [prop] If `f : X ⟶ S` is affine, `f_*𝒪_X` is a quasi-coherent
`𝒪_S`-algebra, and `X ↦ f_*𝒪_X` is an anti-equivalence from the schemes affine over `S` to the
quasi-coherent `𝒪_S`-algebras (Stacks tag 01SA). -/
@[buffalo "thSz9ZHDK9o-34520"]
theorem prop_34520_relative (S : Scheme.{u}) :
    (∀ {X : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f],
      AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f)) ∧
    Nonempty ((AffineOver S)ᵒᵖ ≌ QuasicoherentAlgebra S) ∧
    (affineQuasicoherentPushforwardFunctor S).IsEquivalence :=
  ⟨fun f _ => isQuasicoherent_pushforwardAlgebra f, ⟨affineQuasicoherentEquivalence S⟩,
    { }⟩

open Stacks.AffineAlgebraEquivalence in
/-- thSz9ZHDK9o-34263 (9:31:03) [prop] (essential image) Every quasi-coherent `𝒪_S`-algebra is,
up to isomorphism, `f_*𝒪_X` for a scheme `f : X ⟶ S` affine over `S` (its relative spectrum):
the functor `X ↦ f_*𝒪_X` on schemes affine over `S` is essentially surjective, so the essential
image of `Spec` consists of the schemes affine over `S`. -/
@[buffalo "thSz9ZHDK9o-34263"]
theorem prop_34263_relative (S : Scheme.{u}) :
    (affineQuasicoherentPushforwardFunctor S).EssSurj :=
  inferInstance

end Buffalo.AG.Part05
