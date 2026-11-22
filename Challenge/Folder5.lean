module

public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

/-!
# Folder 5, page 4: Legendre's formula for `p^i`

Finding `5-universal-artinian-pd-normal-form`: the integrality of the coefficients `qᵢ`.

The trusted statement of `Grothendieck.Folder5.sub_one_mul_padicValNat_factorial_pow`, written with
Mathlib alone and left unproved. `lake comparator` (`comparator.json`) checks that
`Solution.Folder5` proves exactly this statement, through the untrusted imports of this repository,
with no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

open Nat

namespace Challenge.Folder5

/-- *`(p − 1) v_p((p^i)!) = p^i − 1`.* -/
theorem sub_one_mul_padicValNat_factorial_pow (p : ℕ) [hp : Fact p.Prime] (i : ℕ) :
    (p - 1) * padicValNat p (p ^ i)! = p ^ i - 1 := by
  sorry

end Challenge.Folder5
