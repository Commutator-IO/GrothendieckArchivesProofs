module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-!
# Folder 85: the fifth power of a `2 × 2` matrix

The trusted statement of `Grothendieck.Folder85.pow_five_eq`, written with Mathlib alone and left
unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder85` proves exactly this
statement, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder85

/-- *Cayley–Hamilton iterated: `g⁵ = x₅ g + y₅` with `x₅ = t⁴ − 3dt² + d²`.* -/
theorem pow_five_eq {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) :
    g ^ 5 = (g.trace ^ 4 - 3 * g.det * g.trace ^ 2 + g.det ^ 2) • g
      + (-(g.det) * (g.trace ^ 3 - 2 * g.det * g.trace)) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  sorry

end Challenge.Folder85
