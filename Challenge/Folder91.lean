module

public import Mathlib.Algebra.Module.LinearMap.Defs

@[expose] public section

/-!
# Folder 91, page 19: the cartesian square of `Hom`

Finding `91-hom-unramified-rigidification`.

The trusted statement of `Grothendieck.Folder91HomUnramified.exists_unique_lift_of_surjective`,
written with Mathlib alone and left unproved. `lake comparator` (`comparator.json`) checks that
`Solution.Folder91` proves exactly this statement, through the untrusted imports of this repository,
with no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder91

/-- *`Hom(M_u, J)` is the fibre product of `Hom(M_v, J)` and `Hom(M_u, J_η)` over
`Hom(M_v, J_η)` when `M_v → M_u` is onto and `J → J_η` is injective.* -/
theorem exists_unique_lift_of_surjective {A Mu Mv J Jη : Type*} [CommRing A]
    [AddCommGroup Mu] [AddCommGroup Mv] [AddCommGroup J] [AddCommGroup Jη] [Module A Mu]
    [Module A Mv] [Module A J] [Module A Jη] (f : Mv →ₗ[A] Mu) (hf : Function.Surjective f)
    (ι : J →ₗ[A] Jη) (hι : Function.Injective ι) (a : Mv →ₗ[A] J) (b : Mu →ₗ[A] Jη)
    (hab : ι.comp a = b.comp f) :
    ∃! c : Mu →ₗ[A] J, c.comp f = a ∧ ι.comp c = b := by
  sorry

end Challenge.Folder91
