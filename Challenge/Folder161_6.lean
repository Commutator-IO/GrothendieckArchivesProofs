module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# Folder 161-6, pages 4–14: the golden number

The trusted statement of `Grothendieck.Folder161_6.cos_two_pi_div_five`, written with Mathlib alone
and left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder161_6` proves
exactly this statement, through the untrusted imports of this repository, with no axiom beyond
`propext`, `Classical.choice` and `Quot.sound`.
-/

open Real

namespace Challenge.Folder161_6

/-- *`cos(2π/5) = (√5 − 1)/4`, so that `η = 2 cos(2π/5)` satisfies `η² + η − 1 = 0`.* -/
theorem cos_two_pi_div_five : cos (2 * π / 5) = (√5 - 1) / 4 := by
  sorry

end Challenge.Folder161_6
