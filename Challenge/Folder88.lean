module

public import Mathlib.Data.Nat.Init

@[expose] public section

/-!
# Folder 88, page 14: the hyperbolic case of the trichotomy

The trusted statement of `Grothendieck.Folder88.hyperbolique_iff`, written with Mathlib alone and
left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder88` proves exactly
this statement, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder88

/-- *`1/p + 1/q < 1/2` for `p, q ≥ 3` exactly when `p + q ≥ 9` and `(p, q) ≠ (3,6), (6,3)`.* -/
theorem hyperbolique_iff (p q : ℕ) (hp : 3 ≤ p) (hq : 3 ≤ q) :
    2 * (p + q) < p * q ↔ 9 ≤ p + q ∧ (p, q) ≠ (3, 6) ∧ (p, q) ≠ (6, 3) := by
  sorry

end Challenge.Folder88
