module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Module.Injective
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

/-!
# Folder 101, pages 10–15: local duality in dimensions one and two

Findings `101-sheaf-duality-dim-one` (page 11) and `101-sheaf-duality-dim-two-fails`
(pages 14–15).

The trusted statements of `Grothendieck.Folder101Ext.isAdicComplete_iff_ext_one` and
`Grothendieck.Folder101DimTwo.not_nonempty_linearEquiv_dual`, written with Mathlib alone and left
unproved. `lake comparator` (`comparator.json`) checks that `Solution.Folder101` proves exactly
these statements, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

open CategoryTheory Abelian IsLocalRing PowerSeries

universe u v

namespace Challenge.Folder101

/-- *Page 11. A discrete valuation ring `A` with fraction field `K` is complete if and only if
`Ext¹_A(K, A) = 0`.* -/
theorem isAdicComplete_iff_ext_one
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] :
    IsAdicComplete (maximalIdeal A) A ↔
      Subsingleton (Ext (ModuleCat.of A K) (ModuleCat.of A A) 1) := by
  sorry

/-- *Pages 14–15. For `A = k[[x, y]]` and `f = x`, `A_f` is not isomorphic to `Hom_A(H, E)` for
any `A`-module `H` and any injective `A`-module `E`: local duality with algebraic Matlis
duals fails in dimension two.* -/
theorem not_nonempty_linearEquiv_dual (k : Type u) [Field k] (H E : Type v) [AddCommGroup H]
    [Module k⟦X⟧⟦X⟧ H] [AddCommGroup E] [Module k⟦X⟧⟦X⟧ E] [Module.Injective k⟦X⟧⟦X⟧ E] :
    ¬Nonempty (Localization.Away (C (X : k⟦X⟧) : k⟦X⟧⟦X⟧) ≃ₗ[k⟦X⟧⟦X⟧] (H →ₗ[k⟦X⟧⟦X⟧] E)) := by
  sorry

end Challenge.Folder101
