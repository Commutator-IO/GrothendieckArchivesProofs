module

public import Grothendieck.CategoryTheory.Folder161_2

@[expose] public section

/-!
# Folder 161-2: monadicity and the Gabriel–Ulmer characterisation

The proof of the trusted statements of `Challenge.Folder161_2`, by
`Grothendieck.Folder161_2.monadicite` and `Grothendieck.Folder161_2.caracterisation_gabriel_ulmer`.
-/

open CategoryTheory Limits

universe w v u u₁ u₂

namespace Challenge.Folder161_2

theorem monadicite {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
    {F : B ⥤ A} {U : A ⥤ B} (adj : F ⊣ U) [HasReflexiveCoequalizers A]
    [U.ReflectsIsomorphisms]
    (hU : ∀ ⦃X Y : A⦄ (f g : X ⟶ Y), IsReflexivePair f g → PreservesColimit (parallelPair f g) U) :
    (Monad.comparison adj).IsEquivalence :=
  @Grothendieck.Folder161_2.monadicite _ _ _ _ _ _ adj _ _ hU

theorem caracterisation_gabriel_ulmer
    (C : Type u) [Category.{v} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C] :
    IsLocallyPresentable.{w} C ↔
      ∃ P : ObjectProperty C, ObjectProperty.Small.{w} P ∧ P.ι.IsDense ∧
        ∀ X, P X → IsPresentable.{w} X :=
  @Grothendieck.Folder161_2.caracterisation_gabriel_ulmer C _ _ _

end Challenge.Folder161_2
