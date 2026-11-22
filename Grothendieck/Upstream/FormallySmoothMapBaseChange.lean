/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib
public import StacksFrontier.RingTheory.Kaehler.JacobiZariski

/-!
# Backport of the mathlib4 branch `mycaule/formallySmooth-mapBaseChange`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `mycaule/formallySmooth-mapBaseChange`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/

@[expose] public section



/-! ## From `Mathlib/RingTheory/Etale/Kaehler.lean` -/

universe u
variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
open TensorProduct
-- `KaehlerDifferential.mapBaseChange_injective` is AxiomMath Stacks' (tag 04B2,
-- `StacksFrontier/RingTheory/Kaehler/JacobiZariski.lean`), with the same statement; the copy
-- this file carried is dropped.

/-- (Named `…_of_projective` here: Stacks' `KaehlerDifferential.exists_retraction_mapBaseChange`,
tag 04B2's companion, assumes `A → B` formally smooth instead.)
The first fundamental sequence `0 → T ⊗[S] Ω[S⁄R] → Ω[T⁄R] → Ω[T⁄S] → 0` is split exact
when `H¹(L_{T⁄S}) = 0` and `Ω[T⁄S]` is projective, e.g. when `T` is a formally smooth `S`-algebra
([Matsumura, Theorem 25.1][matsumura1987]). -/
lemma KaehlerDifferential.exists_retraction_mapBaseChange_of_projective
    [Subsingleton (Algebra.H1Cotangent S T)]
    [Module.Projective T Ω[T⁄S]] :
    ∃ l : Ω[T⁄R] →ₗ[T] T ⊗[S] Ω[S⁄R], l ∘ₗ mapBaseChange R S T = LinearMap.id :=
  ((exact_mapBaseChange_map R S T).split_tfae (mapBaseChange_injective R S T)
    (map_surjective R S T)).out 1 2 |>.mp <|
    Module.projective_lifting_property _ _ (map_surjective R S T)

namespace Algebra.Extension
open KaehlerDifferential
attribute [local instance] SMulCommClass.of_commMonoid
variable {R S T}
variable {P : Extension.{u} R S} {Q : Extension.{u} R T} (f : P.Hom Q)
end Extension
variable {S}
end Algebra
