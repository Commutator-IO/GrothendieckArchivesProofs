module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithfulComplete

@[expose] public section

/-!
# Folder 58, pages 33 and 41–42: the conditions `(LG)ₙ` and their permanence

Finding `58-lef-permanence-projective-flat`. Page 33 defines, for `X` locally noetherian and `Y`
closed in `X`: the pair `(X, Y)` satisfies `(LG)ₙ` if for every locally free Module `F` of finite
type on `X` the map

  `(*)  Hⁱ(X, F) ⟶ Hⁱ(X_{/Y}, F_{/Y})`

is bijective for `i ≤ n` and injective for `i = n + 1`. Corollaire 1 of page 42 asserts that,
`X` being quasi-projective over a noetherian ring, `(LG)ₙ` (resp. LG, resp. LG stricte) passes
from `(X, Y)` to `(W, g⁻¹(Y))` for every `g : W ⟶ X` projective and flat. Stacks has no
`(LG)ₙ` and no Lef / Leff conditions; they are defined here.

* `LGn I n` is `(LG)ₙ` for the pair `(X, V(I))`, `I` an ideal sheaf on `X` (the formal
  completion depends on `Y` only as a closed set, so any ideal sheaf cutting out `Y` may be
  used). The target of `(*)` is spelled `limₖ Hⁱ(X, F / Iᵏ⁺¹ F)`, the target of the comparison
  map `Stacks.Algebraization.cohomologyToLimit` of [Stacks, Tag 087U]: Stacks has no cohomology
  of the formal completion as an object, and `Hⁱ(X_{/Y}, F_{/Y})` maps onto this limit, with
  equality whenever the tower `Hⁱ⁻¹(X, F / Iᵏ F)` is Mittag-Leffler (EGA 0_III 13.3.1), in
  particular in the proper case below.
* `lgN_of_isProper_of_isAdicComplete`: if `A` is noetherian and `J`-adically complete and
  `X ⟶ Spec A` is proper, the pair `(X, X ×_A V(J))` satisfies `(LG)ₙ` for every `n` (indeed `(*)`
  is bijective in every degree, for every coherent `F`). This is the theorem on formal functions
  ([Stacks, Tag 087U], EGA III 4.1.5).
* `lgN_permanence_of_isProper_of_isAdicComplete`: **Corollaire 1 for `(LG)ₙ` over a complete
  base.** For such `X` and every proper `g : W ⟶ X` (projective and flat in the page; neither is
  needed here) the pair `(W, g⁻¹(Y))` satisfies `(LG)ₙ`, with `g⁻¹(Y)` cut out by `J 𝒪_W`.

## Not formalised

* Corollaire 1 when `(LG)ₙ` for `(X, Y)` is a hypothesis rather than a consequence of
  completeness of the base: the reading's sketch of Théorème (i) (a perfect complex representing
  `Rg_* F`, the comparison theorem EGA III 4.1 and the five lemma in hypercohomology) is not
  formalised.
* LG faible, LG (LG faible on every open neighbourhood `U` of `Y`, SGA 2 X's `Lef(X, Y)`) and LG
  stricte (`Leff(X, Y)`), Remarques 1 and 3 (`(LG)₀ ⇔ LG faible ⇔ LG`), and the LG and LG-stricte
  cases of Corollaire 1. Théorème (iii), which the reading does not verify, is left out.
* Page 43's suggestion that quasi-projectivity of `X` can be dropped.
-/

namespace Grothendieck.Folder58LefPermanence

open AlgebraicGeometry CategoryTheory Stacks.Algebraization Stacks.Cohomology.FormalFunctions

universe u

/-- **The condition `(LG)ₙ` of page 33** for the pair `(X, V(I))`: for every coherent locally
free `F` on `X`, the comparison map `Hⁱ(X, F) ⟶ limₖ Hⁱ(X, F / Iᵏ⁺¹ F)` is bijective for
`i ≤ n` and injective for `i = n + 1`. -/
def LGn {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) (n : ℕ) : Prop :=
  ∀ F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
    _root_.SheafOfModules.IsLocallyFree F.obj →
      (∀ i ≤ n, IsIso (cohomologyToLimit I F i)) ∧ Mono (cohomologyToLimit I F (n + 1))

/-- **`(LG)ₙ` over a complete base.** If `A` is noetherian and `J`-adically complete and
`f : X ⟶ Spec A` is proper, then `(X, V(J 𝒪_X))` satisfies `(LG)ₙ` for every `n`, by the theorem
on formal functions ([Stacks, Tag 087U]). -/
theorem lgN_of_isProper_of_isAdicComplete (A : Type u) [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [IsAdicComplete J A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (n : ℕ) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    LGn (baseIdealSheaf A J f) n := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro F _
  refine ⟨fun i _ => isIso_cohomologyToLimit_of_isProper_of_isAdicComplete A J f F i, ?_⟩
  have := isIso_cohomologyToLimit_of_isProper_of_isAdicComplete A J f F (n + 1)
  exact IsIso.mono_of_iso _

/-- **Corollaire 1 of page 42 for `(LG)ₙ`, over a complete base.** Let `A` be noetherian and
`J`-adically complete, `f : X ⟶ Spec A` proper and `Y = V(J 𝒪_X)`. For every proper
`g : W ⟶ X` (in particular every projective flat one), the pair `(W, g⁻¹(Y))`, with `g⁻¹(Y)`
cut out by `J 𝒪_W`, satisfies `(LG)ₙ`, as `(X, Y)` does. -/
theorem lgN_permanence_of_isProper_of_isAdicComplete (A : Type u) [CommRing A]
    [IsNoetherianRing A] (J : Ideal A) [IsAdicComplete J A] {X W : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (g : W ⟶ X) [IsProper g] (n : ℕ) :
    (letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f;
      LGn (baseIdealSheaf A J f) n) ∧
    (letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (g ≫ f);
      LGn (baseIdealSheaf A J (g ≫ f)) n) :=
  ⟨lgN_of_isProper_of_isAdicComplete A J f n, lgN_of_isProper_of_isAdicComplete A J (g ≫ f) n⟩

end Grothendieck.Folder58LefPermanence
