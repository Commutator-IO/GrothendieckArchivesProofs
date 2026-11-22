module

public import Grothendieck.Folder13

@[expose] public section

/-!
# Folder 13, page 47: the Tate case of the « double niveau » question

The proof of the trusted statement of `Challenge.Folder13`, by `Grothendieck.Folder13.tate`.
-/

open Complex

namespace Challenge.Folder13

theorem tate (hπ : Transcendental ℚ (Real.pi : ℂ)) (n : ℤ) :
    {q : ℚ | ∃ α : ℂ, IsAlgebraic ℚ α ∧ (q : ℂ) = (2 * Real.pi * I) ^ n * α} =
      if n = 0 then Set.univ else {0} :=
  @Grothendieck.Folder13.tate hπ n

end Challenge.Folder13
