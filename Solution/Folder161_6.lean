module

public import Grothendieck.Geometry.Folder161_6

@[expose] public section

/-!
# Folder 161-6, pages 4–14: the golden number

The proof of the trusted statement of `Challenge.Folder161_6`, by
`Grothendieck.Folder161_6.cos_two_pi_div_five`.
-/

open Real

namespace Challenge.Folder161_6

theorem cos_two_pi_div_five : cos (2 * π / 5) = (√5 - 1) / 4 :=
  @Grothendieck.Folder161_6.cos_two_pi_div_five

end Challenge.Folder161_6
