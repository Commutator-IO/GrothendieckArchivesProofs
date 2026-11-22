module

public import Grothendieck.RingTheory.Folder5

@[expose] public section

/-!
# Folder 5, page 4: Legendre's formula for `p^i`

The proof of the trusted statement of `Challenge.Folder5`, by
`Grothendieck.Folder5.sub_one_mul_padicValNat_factorial_pow`.
-/

open Nat

namespace Challenge.Folder5

theorem sub_one_mul_padicValNat_factorial_pow (p : ℕ) [hp : Fact p.Prime] (i : ℕ) :
    (p - 1) * padicValNat p (p ^ i)! = p ^ i - 1 :=
  @Grothendieck.Folder5.sub_one_mul_padicValNat_factorial_pow p _ i

end Challenge.Folder5
