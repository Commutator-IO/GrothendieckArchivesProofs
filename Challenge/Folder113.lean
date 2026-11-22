module

public import Mathlib.CategoryTheory.Idempotents.Karoubi

@[expose] public section

/-!
# Folder 113, page 3: the Karoubi envelope as free completion under retracts

The trusted statement of `Grothendieck.Folder113.enveloppe_libre`, written with Mathlib alone and
left unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder113` proves exactly
this statement, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

open CategoryTheory CategoryTheory.Idempotents

universe v u v' u'

namespace Challenge.Folder113

/-- *Restriction along `P → Kar P` is an equivalence `Fun(Kar P, D) ≌ Fun(P, D)` for every
idempotent complete category `D`.* -/
theorem enveloppe_libre (P : Type u) [Category.{v} P] (D : Type u') [Category.{v'} D]
    [IsIdempotentComplete D] :
    ((Functor.whiskeringLeft P (Karoubi P) D).obj (toKaroubi P)).IsEquivalence := by
  sorry

end Challenge.Folder113
