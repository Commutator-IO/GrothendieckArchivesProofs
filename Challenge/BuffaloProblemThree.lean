module

public import Mathlib.CategoryTheory.Presentable.Basic

@[expose] public section

/-!
# Buffalo, problem 3: `2` is not presentable in `Setᵒᵖ`

The trusted statement of `Buffalo.ProblemThree.not_isPresentable`, written with Mathlib alone and
left unproved. `lake comparator` (`comparator.json`) checks that `Solution.BuffaloProblemThree`
proves exactly this statement, through the untrusted imports of this repository, with no axiom
beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

open CategoryTheory Opposite

namespace Challenge.BuffaloProblemThree

/-- *In `Setᵒᵖ` the object `2` is not presentable.* -/
theorem not_isPresentable : ¬ IsPresentable.{0} (op Bool : Typeᵒᵖ) := by
  sorry

end Challenge.BuffaloProblemThree
