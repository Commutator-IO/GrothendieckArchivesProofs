module

public import Grothendieck.RingTheory.Folder77

@[expose] public section

/-!
# Folder 77: the local step of Proposition 8.5

The proof of the trusted statement of `Challenge.Folder77`, by `Grothendieck.Folder77.prop85_local`.
-/

open IsLocalRing

namespace Challenge.Folder77

theorem prop85_local {R : Type*} {C : Type*} [CommRing R] [IsLocalRing R] [CommRing C] [Algebra R C]
    [Algebra.FormallyUnramified R C] [Module.Finite R C] [Nontrivial C]
    (hm : maximalIdeal R = Ideal.span {2}) (h2C : ∀ x : C, 2 * x = 0 → x = 0)
    {Δ : R} {v : C} {n : ℕ} (hv : v ^ 2 = 4 ^ n * algebraMap R C Δ) :
    ∃ b c : R, b ^ 2 - 4 * c = Δ :=
  @Grothendieck.Folder77.prop85_local _ _ _ _ _ _ _ _ _ hm h2C _ _ _ hv

end Challenge.Folder77
