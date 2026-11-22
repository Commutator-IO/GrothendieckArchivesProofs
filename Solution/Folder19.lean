module

public import Grothendieck.CategoryTheory.Folder19

@[expose] public section

/-!
# Folder 19, page 80: the proof of the trusted statement

`Challenge.Folder19.proposition_page80`, `beck_iff` and `gabriel_popescu`, proved by the untrusted
`Grothendieck/CategoryTheory/Folder19.lean`.
-/

open CategoryTheory Limits

universe v u₁ u₂

namespace Challenge.Folder19

theorem proposition_page80 (n : ℕ) :
    ∃ G : Fin n → (((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type) ⥤ ((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type)),
      (∀ (i : Fin n) (h : i.1 + 1 < n), Nonempty (G i ⊣ G ⟨i.1 + 1, h⟩)) ∧
      ∀ i, ¬ ((G i).Full ∧ (G i).Faithful) :=
  Grothendieck.Folder19.proposition_page80 n

theorem beck_iff {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
    {f : A ⥤ B} {g : B ⥤ A} (adj : f ⊣ g) : (Comonad.comparison adj).IsEquivalence ↔
    f.ReflectsIsomorphisms ∧ ∀ ⦃X Y : A⦄ (u v : X ⟶ Y), f.IsCosplitPair u v →
      HasEqualizer u v ∧ PreservesLimit (parallelPair u v) f :=
  Grothendieck.Folder19.beck_iff adj

theorem gabriel_popescu {C : Type u₁} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] (U : C) (hU : IsSeparator U) :
    (preadditiveCoyonedaObj U).Full ∧ (preadditiveCoyonedaObj U).Faithful ∧
      PreservesFiniteLimits (IsGrothendieckAbelian.tensorObj U) ∧
      PreservesFiniteColimits (IsGrothendieckAbelian.tensorObj U) :=
  Grothendieck.Folder19.gabriel_popescu U hU

end Challenge.Folder19
