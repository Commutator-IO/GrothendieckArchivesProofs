module

public import Grothendieck.AlgebraicGeometry.Folder101DimTwo
public import Grothendieck.AlgebraicGeometry.Folder101Ext

@[expose] public section

/-!
# Folder 101, pages 10–15: local duality in dimensions one and two

The proof of the trusted statements of `Challenge.Folder101`, by
`Grothendieck.Folder101Ext.isAdicComplete_iff_ext_one` and
`Grothendieck.Folder101DimTwo.not_nonempty_linearEquiv_dual`.
-/

open CategoryTheory Abelian IsLocalRing PowerSeries

universe u v

namespace Challenge.Folder101

theorem isAdicComplete_iff_ext_one
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] :
    IsAdicComplete (maximalIdeal A) A ↔
      Subsingleton (Ext (ModuleCat.of A K) (ModuleCat.of A A) 1) :=
  @Grothendieck.Folder101Ext.isAdicComplete_iff_ext_one _ _ _ _ _ _ _ _

theorem not_nonempty_linearEquiv_dual (k : Type u) [Field k] (H E : Type v) [AddCommGroup H]
    [Module k⟦X⟧⟦X⟧ H] [AddCommGroup E] [Module k⟦X⟧⟦X⟧ E] [Module.Injective k⟦X⟧⟦X⟧ E] :
    ¬Nonempty (Localization.Away (C (X : k⟦X⟧) : k⟦X⟧⟦X⟧) ≃ₗ[k⟦X⟧⟦X⟧] (H →ₗ[k⟦X⟧⟦X⟧] E)) :=
  @Grothendieck.Folder101DimTwo.not_nonempty_linearEquiv_dual k _ H E _ _ _ _ _

end Challenge.Folder101
