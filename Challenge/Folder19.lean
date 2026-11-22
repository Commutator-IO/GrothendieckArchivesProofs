module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import Mathlib.CategoryTheory.Abelian.Monomorphisms

@[expose] public section

/-!
# Folder 19, pages 4, 14–15 and 80: the trusted statements

The statements of `Grothendieck.Folder19.proposition_page80`, `Grothendieck.Folder19.beck_iff`
and `Grothendieck.Folder19.gabriel_popescu`, written with Mathlib alone and left unproved.
`lake comparator` (`comparator.json`) checks that `Solution.Folder19` proves exactly these
statements, through the untrusted imports of `Grothendieck/`, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.

`Mathlib.CategoryTheory.Abelian.Monomorphisms` is imported although no statement needs it: it and
`Mathlib.CategoryTheory.Abelian.CommSq` (imported through Gabriel–Popescu) both declare
`CategoryTheory.Abelian.instIsStableUnderCobaseChangeMonomorphisms`, the Solution's environment
has both, and `lake comparator` rejects the constant unless the Challenge's has both too.

*Page 80. For every `n`, there are `n` functors between presheaf topoi on a small category — here
the poset `ℤ ⊕ ℤ` — each right adjoint to the previous one, none of them fully faithful.*
-/

open CategoryTheory Limits

universe v u₁ u₂

namespace Challenge.Folder19

theorem proposition_page80 (n : ℕ) :
    ∃ G : Fin n → (((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type) ⥤ ((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type)),
      (∀ (i : Fin n) (h : i.1 + 1 < n), Nonempty (G i ⊣ G ⟨i.1 + 1, h⟩)) ∧
      ∀ i, ¬ ((G i).Full ∧ (G i).Faithful) := by
  sorry

/-- *Page 4, Théorème 1.12 b), in the form the reading corrects it to (Beck's theorem): the
comparison functor of `f ⊣ g` is an equivalence if and only if `f` is conservative and, for
every `f`-split pair `(u, v)`, `Ker(u, v)` exists and `f` commutes with it.* The « il faut »
of the manuscript, with condition C in place of `f`-split pairs, is false. -/
theorem beck_iff {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
    {f : A ⥤ B} {g : B ⥤ A} (adj : f ⊣ g) : (Comonad.comparison adj).IsEquivalence ↔
    f.ReflectsIsomorphisms ∧ ∀ ⦃X Y : A⦄ (u v : X ⟶ Y), f.IsCosplitPair u v →
      HasEqualizer u v ∧ PreservesLimit (parallelPair u v) f := by
  sorry

/-- *Pages 14–15, Gabriel–Popescu, as corrected by the reading. Let `C` be a Grothendieck
category with a generator `U`. Then `Hom_C(U, -)` is fully faithful and its left adjoint
`- ⊗_R U` is exact.* -/
theorem gabriel_popescu {C : Type u₁} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] (U : C) (hU : IsSeparator U) :
    (preadditiveCoyonedaObj U).Full ∧ (preadditiveCoyonedaObj U).Faithful ∧
      PreservesFiniteLimits (IsGrothendieckAbelian.tensorObj U) ∧
      PreservesFiniteColimits (IsGrothendieckAbelian.tensorObj U) := by
  sorry

end Challenge.Folder19
