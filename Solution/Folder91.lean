module

public import Grothendieck.AlgebraicGeometry.Folder91HomUnramified

@[expose] public section

/-!
# Folder 91, page 19: the cartesian square of `Hom`

The proof of the trusted statement of `Challenge.Folder91`, by
`Grothendieck.Folder91HomUnramified.exists_unique_lift_of_surjective`.
-/

namespace Challenge.Folder91

theorem exists_unique_lift_of_surjective {A Mu Mv J Jη : Type*} [CommRing A]
    [AddCommGroup Mu] [AddCommGroup Mv] [AddCommGroup J] [AddCommGroup Jη] [Module A Mu]
    [Module A Mv] [Module A J] [Module A Jη] (f : Mv →ₗ[A] Mu) (hf : Function.Surjective f)
    (ι : J →ₗ[A] Jη) (hι : Function.Injective ι) (a : Mv →ₗ[A] J) (b : Mu →ₗ[A] Jη)
    (hab : ι.comp a = b.comp f) :
    ∃! c : Mu →ₗ[A] J, c.comp f = a ∧ ι.comp c = b :=
  @Grothendieck.Folder91HomUnramified.exists_unique_lift_of_surjective _ _ _ _ _ _ _ _ _ _ _ _ _ _ f
    hf ι hι a b hab

end Challenge.Folder91
