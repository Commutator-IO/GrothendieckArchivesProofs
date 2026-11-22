module

public import Mathlib.Algebra.Group.Basic

@[expose] public section

/-!
# Folder 74, page 116: the maps `φ_a` on the relation `xyz = 1`

The trusted statement of `Grothendieck.Folder74.p116`, written with Mathlib alone and left unproved.
`lake comparator` (`comparator.json`) checks that `Solution.Folder74` proves exactly this statement,
through the untrusted imports of this repository, with no axiom beyond `propext`, `Classical.choice`
and `Quot.sound`.
-/

namespace Challenge.Folder74

/-- *On the relation `xyz = 1` of a group `G`, the maps `(x, y, z) ↦ (x, a⁻¹z⁻¹, a⁻¹y⁻¹)` all
preserve the relation if and only if every element of `G` has order dividing 2.* -/
theorem p116 {G : Type*} [Group G] :
    (∀ a x y z : G, x * y * z = 1 → x * (a⁻¹ * z⁻¹) * (a⁻¹ * y⁻¹) = 1) ↔
      ∀ g : G, g * g = 1 := by
  sorry

end Challenge.Folder74
