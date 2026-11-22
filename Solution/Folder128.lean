module

public import Grothendieck.Folder128

@[expose] public section

/-!
# Folder 128, page 23: Lemme 2

The proof of the trusted statement of `Challenge.Folder128`, by
`Grothendieck.Folder128.Infinitesimal.lemme2`.
-/

namespace Challenge.Folder128

theorem lemme2 {B : Type*} {C : Type*} [CommRing B] [CommRing C] [Algebra B C]
    [Algebra.IsIntegral B C] [Finite (MaximalSpectrum C)]
    (hinj : ∀ 𝔫 𝔫' : MaximalSpectrum C,
      𝔫.asIdeal.comap (algebraMap B C) = 𝔫'.asIdeal.comap (algebraMap B C) → 𝔫 = 𝔫')
    (hrad : ∀ 𝔫 : MaximalSpectrum C,
      IsPurelyInseparable (B ⧸ 𝔫.asIdeal.comap (algebraMap B C)) (C ⧸ 𝔫.asIdeal))
    {n : Type*} [Fintype n] [DecidableEq n] (u : Matrix n n C) :
    ∃ v : Matrix n n B, IsUnit (u + v.map (algebraMap B C)) :=
  @Grothendieck.Folder128.Infinitesimal.lemme2 _ _ _ _ _ _ _ hinj hrad _ _ _ u

end Challenge.Folder128
