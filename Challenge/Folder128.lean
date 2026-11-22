module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

@[expose] public section

/-!
# Folder 128, page 23: Lemme 2

The trusted statement of `Grothendieck.Folder128.Infinitesimal.lemme2`, written with Mathlib alone
and left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder128` proves
exactly this statement, through the untrusted imports of this repository, with no axiom beyond
`propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Challenge.Folder128

/-- *Let `C` be integral over `B` with finitely many maximal ideals, distinct maximal ideals of
`C` lying over distinct ideals of `B`, and every residue extension purely inseparable. Then
for every `u ∈ M_n(C)` there is `v ∈ M_n(B)` with `u + φ(v)` invertible.* (Without the
page's hypothesis (i).) -/
theorem lemme2 {B : Type*} {C : Type*} [CommRing B] [CommRing C] [Algebra B C]
    [Algebra.IsIntegral B C] [Finite (MaximalSpectrum C)]
    (hinj : ∀ 𝔫 𝔫' : MaximalSpectrum C,
      𝔫.asIdeal.comap (algebraMap B C) = 𝔫'.asIdeal.comap (algebraMap B C) → 𝔫 = 𝔫')
    (hrad : ∀ 𝔫 : MaximalSpectrum C,
      IsPurelyInseparable (B ⧸ 𝔫.asIdeal.comap (algebraMap B C)) (C ⧸ 𝔫.asIdeal))
    {n : Type*} [Fintype n] [DecidableEq n] (u : Matrix n n C) :
    ∃ v : Matrix n n B, IsUnit (u + v.map (algebraMap B C)) := by
  sorry

end Challenge.Folder128
