/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import StacksFrontier.AlgebraicGeometry.Algebraization.StrictDepthFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusDimensionCriterion

/-!
# Folder 58, pages 45 to 51: comparison of Hom along `Y′ = V(t)`, depth asked only off `Y′`

Finding `58-local-hom-comparison-depth-off-y`. Let `A` be a local Noetherian ring, `t` in its
maximal ideal, `A` complete for the `t`-adic topology, `X′ = Spec A ∖ {𝔪}` and
`Y′ = V(t) ∩ X′`. Page 45 asserts that `Hom(F, G) → Hom(F̂, Ĝ)` (completion along `Y′`) is
bijective for coherent `F`, `G` on `X′` as soon as `G` has depth `≥ 2` at the closed points of
`X′ ∖ Y′`, with no depth condition at the points of `Y′`.

This is the case `I = (t)`, `𝔞 = 𝔪`, `d = 1` of Stacks Tag 0EJ7
(`Stacks.Algebraization.completionFunctor_map_bijective_of_satisfiesStrictDepthInequalities`);
`cd(A, (t)) ≤ 1` is Stacks Tag 0DX9.

**What is proved.** `hom_bijective_of_depth_two_off_V_t`: the bijection, under

* `hdepth`, Stacks' condition `DepthTwoOffFormalLocus`: depth `≥ 2` at every `x ∈ X′` whose
  closure meets `V(t)` only at `𝔪`. For `A` local this is the folder's condition: such an `x`
  does not lie on `V(t)`, and a prime `𝔭 ∌ t` has `V(𝔭, t) = {𝔪}` iff `dim A/𝔭 = 1`, iff `𝔭`
  is a closed point of `X′ ∖ Y′ = Spec A_t` (Krull's principal ideal theorem; not formalised);
* `hK`: a dualizing complex on `A` (the folder's « quotient of a regular ring » gives one);
* `hstrict`: the strict `(1, 2)`-inequalities of Stacks Tag 0EJ3 for `Ĝ` along `Y′`.

**Not formalised.** The derivation of `hstrict` from the folder's hypotheses (the sweep's sketch
through Tags 0AWY, 0AW6 and 0DX9). Without it the folder's statement is reduced to 0EJ7 but not
proved: `hstrict` is a condition at the points of `Y′`, the very points where the folder asks
nothing, and page 47 leaves the corresponding `t`-regular step at « ? ».
-/

@[expose] public section


namespace Grothendieck.Folder58DepthComparison

open AlgebraicGeometry CategoryTheory Stacks.Algebraization Stacks.LocalCohomology

universe u

/-- The algebraization situation of the folder: `I = (t)` and `𝔞 = 𝔪`, so `Y = V(t)`, `Z` is
the closed point and `U = X′` is the punctured spectrum. -/
noncomputable abbrev situation (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A) : AlgebraizationSituation.{u} where
  A := A
  I := Ideal.span {t}
  a := IsLocalRing.maximalIdeal A
  I_le_a := (Ideal.span_singleton_le_iff_mem _).mpr ht

/-- **Folder 58, page 45, under the strict `(1, 2)`-inequalities.** For `A` local Noetherian,
`t`-adically complete, with a dualizing complex, and coherent `F`, `G` on the punctured spectrum
`X′`, completion along `Y′ = V(t) ∩ X′` is bijective on `Hom(F, G)` when `G` has depth `≥ 2`
at the closed points of `X′ ∖ Y′` and `Ĝ` satisfies the strict `(1, 2)`-inequalities. -/
theorem hom_bijective_of_depth_two_off_V_t (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A)
    [hc : IsAdicComplete (Ideal.span {t}) A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : Dualizing.IsDualizingComplex K)
    (F G : SheafOfModules.CoherentModules (situation A t ht).U.toScheme.ringCatSheaf)
    (hstrict : SatisfiesStrictDepthInequalities (situation A t ht)
      ((completionFunctor (situation A t ht).U.toScheme (idealOnOpen (situation A t ht))).obj G)
        1 2)
    (hdepth : FormalSectionsII.DepthTwoOffFormalLocus A (Ideal.span {t})
      (IsLocalRing.maximalIdeal A) G.obj) :
    Function.Bijective
      ((completionFunctor (situation A t ht).U.toScheme (idealOnOpen (situation A t ht))).map :
        (F ⟶ G) →
          ((completionFunctor (situation A t ht).U.toScheme
              (idealOnOpen (situation A t ht))).obj F ⟶
            (completionFunctor (situation A t ht).U.toScheme
              (idealOnOpen (situation A t ht))).obj G)) := by
  have : IsAdicComplete (situation A t ht).I (situation A t ht).A := hc
  exact completionFunctor_map_bijective_of_satisfiesStrictDepthInequalities (situation A t ht) G
    1 le_rfl K hK (cohomologicalDimension_span_singleton_le_one A t) hstrict hdepth F

end Grothendieck.Folder58DepthComparison
