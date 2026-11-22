module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.Algebraic.Defs

@[expose] public section

/-!
# Folder 13, page 47: the Tate case of the « double niveau » question

The trusted statement of `Grothendieck.Folder13.tate`, written with Mathlib alone and left unproved.
`lake comparator` (`comparator.json`) checks that `Solution.Folder13` proves exactly this statement,
through the untrusted imports of this repository, with no axiom beyond `propext`, `Classical.choice`
and `Quot.sound`.
-/

open Complex

namespace Challenge.Folder13

/-- *« c'est une puissance de Tate, et ça marche ». For the Tate motive `ℚ(n)`, the rationals
lying in the de Rham line `(2πi)ⁿ ℚ̄` are all of `ℚ` when `n = 0` and only `0` otherwise.*
The transcendence of `π` (Lindemann, not in Mathlib) is a hypothesis. -/
theorem tate (hπ : Transcendental ℚ (Real.pi : ℂ)) (n : ℤ) :
    {q : ℚ | ∃ α : ℂ, IsAlgebraic ℚ α ∧ (q : ℂ) = (2 * Real.pi * I) ^ n * α} =
      if n = 0 then Set.univ else {0} := by
  sorry

end Challenge.Folder13
