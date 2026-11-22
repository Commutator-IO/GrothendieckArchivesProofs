module

public import Grothendieck.CategoryTheory.Folder113

@[expose] public section

/-!
# Folder 113, page 3: the Karoubi envelope as free completion under retracts

The proof of the trusted statement of `Challenge.Folder113`, by
`Grothendieck.Folder113.enveloppe_libre`.
-/

open CategoryTheory CategoryTheory.Idempotents

universe v u v' u'

namespace Challenge.Folder113

theorem enveloppe_libre (P : Type u) [Category.{v} P] (D : Type u') [Category.{v'} D]
    [IsIdempotentComplete D] :
    ((Functor.whiskeringLeft P (Karoubi P) D).obj (toKaroubi P)).IsEquivalence :=
  @Grothendieck.Folder113.enveloppe_libre P _ D _ _

end Challenge.Folder113
