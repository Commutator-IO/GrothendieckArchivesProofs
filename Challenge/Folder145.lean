module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

@[expose] public section

/-!
# Folder 145, pages 34–35: the unit-exponent exercise

Finding `145-unit-exponent-exercise`.

The trusted statement of `Grothendieck.Folder145.dihedral_witness`, written with Mathlib alone and
left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder145` proves exactly
this statement, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

open DihedralGroup

namespace Challenge.Folder145

/-- *The dihedral witness: for `m` odd, `(sr 0 · sr 1)⁻¹ ^ m · sr 0 ^ m · sr 1 ^ m = 1` in
`DihedralGroup N` if and only if `m ≡ 1 (mod N)`.* -/
theorem dihedral_witness (N : ℕ) {m : ℕ} (hm : Odd m) :
    ((sr 0 * sr 1 : DihedralGroup N)⁻¹) ^ m * (sr 0) ^ m * (sr 1) ^ m = 1 ↔
      (m : ZMod N) = 1 := by
  sorry

end Challenge.Folder145
