module

public import Grothendieck.CategoryTheory.Folder19

@[expose] public section

/-!
# Folder 19, page 80: the proof of the trusted statement

`Challenge.Folder19.proposition_page80`, proved by the untrusted `Grothendieck/CategoryTheory/Folder19.lean`.
-/

open CategoryTheory

namespace Challenge.Folder19

theorem proposition_page80 (n : ℕ) :
    ∃ G : Fin n → (((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type) ⥤ ((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type)),
      (∀ (i : Fin n) (h : i.1 + 1 < n), Nonempty (G i ⊣ G ⟨i.1 + 1, h⟩)) ∧
      ∀ i, ¬ ((G i).Full ∧ (G i).Faithful) :=
  Grothendieck.Folder19.proposition_page80 n

end Challenge.Folder19
