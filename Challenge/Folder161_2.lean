module

public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable

@[expose] public section

/-!
# Folder 161-2: monadicity and the Gabriel–Ulmer characterisation

The trusted statements of `Grothendieck.Folder161_2.monadicite` and
`Grothendieck.Folder161_2.caracterisation_gabriel_ulmer`, written with Mathlib alone and left
unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder161_2` proves exactly
these statements, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

open CategoryTheory Limits

universe w v u u₁ u₂

namespace Challenge.Folder161_2

/-- *Page 33. « Un foncteur `U : A → B` admettant un adjoint à gauche `F` est monadique si `U`
est conservatif et si `A` a et `U` préserve les coégalisateurs des paires réflexives. »* -/
theorem monadicite {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
    {F : B ⥤ A} {U : A ⥤ B} (adj : F ⊣ U) [HasReflexiveCoequalizers A]
    [U.ReflectsIsomorphisms]
    (hU : ∀ ⦃X Y : A⦄ (f g : X ⟶ Y), IsReflexivePair f g → PreservesColimit (parallelPair f g) U) :
    (Monad.comparison adj).IsEquivalence := by
  sorry

/-- *Page 61, Corollaire. A cocomplete, locally small category is locally presentable if and
only if it has a small dense full subcategory made of presentable objects.* -/
theorem caracterisation_gabriel_ulmer
    (C : Type u) [Category.{v} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C] :
    IsLocallyPresentable.{w} C ↔
      ∃ P : ObjectProperty C, ObjectProperty.Small.{w} P ∧ P.ι.IsDense ∧
        ∀ X, P X → IsPresentable.{w} X := by
  sorry

end Challenge.Folder161_2
