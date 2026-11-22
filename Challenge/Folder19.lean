module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Opposites

@[expose] public section

/-!
# Folder 19, page 80: the trusted statement

The statement of `Grothendieck.Folder19.proposition_page80`, written with Mathlib alone and left
unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder19` proves exactly
this statement, through the untrusted imports of `Grothendieck/`, with no axiom beyond
`propext`, `Classical.choice` and `Quot.sound`.

*For every `n`, there are `n` functors between presheaf topoi on a small category — here the
poset `ℤ ⊕ ℤ` — each right adjoint to the previous one, none of them fully faithful.*
-/

open CategoryTheory

namespace Challenge.Folder19

theorem proposition_page80 (n : ℕ) :
    ∃ G : Fin n → (((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type) ⥤ ((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type)),
      (∀ (i : Fin n) (h : i.1 + 1 < n), Nonempty (G i ⊣ G ⟨i.1 + 1, h⟩)) ∧
      ∀ i, ¬ ((G i).Full ∧ (G i).Faithful) := by
  sorry

end Challenge.Folder19
