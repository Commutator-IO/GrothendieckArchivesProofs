module

public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# Folder 1, page 124: Corollaire 3 in finite dimension

Finding `1-mixed-schwarz-fredholm-coefficients`.

The trusted statement of `Grothendieck.Folder1.corollaire3`, written with Mathlib alone and left
unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder1` proves exactly this
statement, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Challenge.Folder1

/-- *For complex square matrices `A`, `B`: `|det(1 + A + B)|` is at most the half-sum, and its
square at most the product, of `det(1 + |A| + |B|)` and `det(1 + |A*| + |B*|)`.* -/
theorem corollaire3 {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    ‖det (1 + (A + B))‖ ≤
        ((det (1 + (CFC.abs A + CFC.abs B))).re + (det (1 + (CFC.abs Aᴴ + CFC.abs Bᴴ))).re) / 2 ∧
      ‖det (1 + (A + B))‖ ^ 2 ≤
        (det (1 + (CFC.abs A + CFC.abs B))).re * (det (1 + (CFC.abs Aᴴ + CFC.abs Bᴴ))).re := by
  sorry

end Challenge.Folder1
