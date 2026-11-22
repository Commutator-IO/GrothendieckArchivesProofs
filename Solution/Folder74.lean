module

public import Grothendieck.Combinatorics.Folder74

@[expose] public section

/-!
# Folder 74, page 116: the maps `φ_a` on the relation `xyz = 1`

The proof of the trusted statement of `Challenge.Folder74`, by `Grothendieck.Folder74.p116`.
-/

namespace Challenge.Folder74

theorem p116 {G : Type*} [Group G] :
    (∀ a x y z : G, x * y * z = 1 → x * (a⁻¹ * z⁻¹) * (a⁻¹ * y⁻¹) = 1) ↔
      ∀ g : G, g * g = 1 :=
  @Grothendieck.Folder74.p116 _ _

end Challenge.Folder74
