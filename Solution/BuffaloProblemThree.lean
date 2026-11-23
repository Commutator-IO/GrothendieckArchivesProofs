module

public import Buffalo.CategoryTheory.ProblemThree

@[expose] public section

/-!
# Buffalo, problem 3: `2` is not presentable in `Setᵒᵖ`

The proof of the trusted statement of `Challenge.BuffaloProblemThree`, by
`Buffalo.ProblemThree.not_isPresentable`.
-/

open CategoryTheory Opposite

namespace Challenge.BuffaloProblemThree

theorem not_isPresentable : ¬ IsPresentable.{0} (op Bool : Typeᵒᵖ) :=
  @Buffalo.ProblemThree.not_isPresentable

end Challenge.BuffaloProblemThree
