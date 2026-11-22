module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
import Grothendieck.Attr

@[expose] public section

/-!
# Buffalo, algebraic geometry, part 08: fpqc descent of finite type and finite presentation

`Part08b.lean` proved the entry `vuys5SNs2eQ-3491` (0:58:11: for `g : X' ⟶ X` faithfully flat
quasi-compact, a quasi-coherent `𝒪_X`-module `F` is of finite type, resp. of finite
presentation, if and only if `F' = g^* F` is) only in the affine case and for finite type
(`prop_3491`). Both halves are proved here, for modules and for quasi-coherent sheaves, from
AxiomMath/Stacks (Apache-2.0).

**What is proved.**
* `prop_3491_module`: for a faithfully flat ring map `A → A'` and an `A`-module `M`, `M` is finite
  (resp. finitely presented) over `A` if and only if `A' ⊗_A M` is so over `A'`.
* `prop_3491_fpqc`: for a flat, surjective, quasi-compact morphism of schemes `g : X' ⟶ X` and a
  quasi-coherent `𝒪_X`-module `F`, `F` is of finite type (resp. of finite presentation) if and
  only if `g^* F` is.

**How.** For modules, descent of finite generation is Mathlib's
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` and descent of finite presentation is
Stacks 03C4 (2), `Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat`
(`StacksFrontier/RingTheory/Flat/FaithfullyFlat/Descent.lean`): `M` is finite, so a quotient
`A^n → M`, whose kernel becomes finitely generated after the faithfully flat base change, hence
is finitely generated. For sheaves, `g` alone is an fpqc covering of `X`
(`Scheme.Hom.singleton_mem_fpqcPrecoverage`), and descent along an fpqc covering is Stacks 05AZ
(`Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_pullback_fpqcCover`) and Stacks 05B0
(`AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover`): the question is local on `X`,
over an affine `X` the covering is refined by a single affine faithfully flat scheme, and there
the module statement above applies. The converse directions are the stability of finite type
and finite presentation under pullback (Stacks 01B6, 01BQ).

**Not formalised.** Nothing of the entry is left out. The modules are those of the universe of
the rings, and the sheaf statement is for the pullback functor `Scheme.Modules.pullback` of
Mathlib; the hypothesis "faithfully flat quasi-compact" is read as flat, surjective and
quasi-compact, as in `Part08b`.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Buffalo.AG.Part08

/-- vuys5SNs2eQ-3491 (0:58:11) [prop], affine form. If `A → A'` is faithfully flat, an `A`-module
`M` is finite (resp. finitely presented) if and only if `A' ⊗_A M` is so over `A'`. Mathlib's
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` and Stacks 03C4. -/
@[buffalo "vuys5SNs2eQ-3491"]
theorem prop_3491_module {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
    [Module.FaithfullyFlat A A'] (M : Type u) [AddCommGroup M] [Module A M] :
    (Module.Finite A' (A' ⊗[A] M) ↔ Module.Finite A M) ∧
      (Module.FinitePresentation A' (A' ⊗[A] M) ↔ Module.FinitePresentation A M) :=
  ⟨⟨fun _ => .of_finite_tensorProduct_of_faithfullyFlat A', fun _ => inferInstance⟩,
    ⟨fun _ => Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat
        (TensorProduct.mk A A' M 1) (TensorProduct.isBaseChange (R := A) (M := M) (S := A')),
      fun _ => inferInstance⟩⟩

/-- vuys5SNs2eQ-3491 (0:58:11) [prop] Let `g : X' ⟶ X` be faithfully flat (flat and surjective)
and quasi-compact. A quasi-coherent `𝒪_X`-module `F` is of finite type (resp. of finite
presentation) if and only if `g^* F` is. Stacks 05AZ and 05B0, for the fpqc covering `{g}`. -/
@[buffalo "vuys5SNs2eQ-3491"]
theorem prop_3491_fpqc {X X' : Scheme.{u}} (g : X' ⟶ X) [Flat g] [Surjective g] [QuasiCompact g]
    (F : X.Modules) [F.IsQuasicoherent] :
    (((Scheme.Modules.pullback g).obj F).IsFiniteType ↔ F.IsFiniteType) ∧
      (((Scheme.Modules.pullback g).obj F).IsFinitePresentation ↔ F.IsFinitePresentation) := by
  let 𝒰 : X.Cover.{u} Scheme.fpqcPrecoverage :=
    Precoverage.ZeroHypercover.singleton g g.singleton_mem_fpqcPrecoverage
  refine ⟨⟨fun h => ?_, fun _ => ?_⟩, ⟨fun h => ?_, fun _ => ?_⟩⟩
  · exact Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_pullback_fpqcCover F 𝒰
      fun _ => h
  · exact Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_pullback g F
  · exact isFinitePresentation_of_pullback_fpqcCover F 𝒰 fun _ => h
  · exact Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback g F

end Buffalo.AG.Part08
