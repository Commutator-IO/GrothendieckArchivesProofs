module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic

/-!
# The degree of an invertible sheaf on a curve

Let `X` be a scheme over a field `k`, `i : C ⟶ X` a morphism from a scheme `C` of dimension at
most one which is proper over `k` (for instance a closed curve `C ⊆ X` proper over `k`), and `L`
an invertible sheaf on `X`. The degree of `L` on `C` is
`deg_C L = χ(C, i^* L) - χ(C, 𝒪_C)`, where `χ` is the alternating sum of the `k`-dimensions of
the cohomology groups.

## Main definitions

* `MMP.Mori.degreeOn`: the degree `deg_C L` of an invertible sheaf `L` on `X` along a proper
  curve `i : C ⟶ X`.

## Main results

* `MMP.Mori.degreeOn_eq_invertibleCurveDegree`: the degree is the degree of the pull-back
  `i^* L` on the proper curve `C`.
* `MMP.Mori.degreeOn_eq_eulerCharacteristic_sub`: the defining formula
  `χ(C, i^* L) - χ(C, 𝒪_C)`, when the coherence instances needed for `eulerCharacteristic` are
  available.

## Implementation notes

The curve is a morphism `i : C ⟶ X` rather than a closed subscheme, and `C` is only required to
have dimension at most one: neither the closed-immersion condition nor integrality of `C` enters
the definition, which therefore applies verbatim to a closed curve `C ⊆ X`. The structure of
`k`-scheme on `C` is the composite `i ≫ sX`, so `C` is proper over `k` through `X`.

The degree is `AlgebraicGeometry.invertibleCurveDegree` of the pull-back
`(Scheme.Modules.pullback i).obj L`, which is invertible by Stacks Tag 0B8L.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Notation 0.4, 1.34]
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

variable (k : Type u) [Field k] {X C : Scheme.{u}}

/-- The pull-back of an invertible sheaf along a morphism of schemes is invertible
(Stacks Tag 0B8L), at the spelling `AlgebraicGeometry.invertibleCurveDegree` takes. -/
instance isInvertible_pullback_obj (i : C ⟶ X) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 ((Scheme.Modules.pullback i).obj L) :=
  Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf i L (h := hL)

/-- The degree `deg_C L` of an invertible sheaf `L` on a `k`-scheme `X` (structure morphism
`sX`) along a curve `i : C ⟶ X`, where `C` has dimension at most one and is proper over `k`:
the Euler characteristic of the pull-back `i^* L` on `C` minus that of `𝒪_C`. -/
@[mmp "def_km0_line_bundle_degree_curve"]
def degreeOn (sX : X ⟶ Spec (.of k)) (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : ℤ :=
  invertibleCurveDegree k (i ≫ sX) hdim ((Scheme.Modules.pullback i).obj L)

variable (sX : X ⟶ Spec (.of k)) (i : C ⟶ X) [IsProper (i ≫ sX)]
  (hdim : topologicalKrullDim C ≤ 1) (L : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

/-- The degree of `L` along `i` is the degree of the invertible sheaf `i^* L` on the proper
curve `C`. -/
theorem degreeOn_eq_invertibleCurveDegree :
    degreeOn k sX i hdim L =
      invertibleCurveDegree k (i ≫ sX) hdim ((Scheme.Modules.pullback i).obj L) := rfl

/-- The defining formula `deg_C L = χ(C, i^* L) - χ(C, 𝒪_C)`, when the coherence instances
needed for `AlgebraicGeometry.eulerCharacteristic` are available. -/
theorem degreeOn_eq_eulerCharacteristic_sub
    [((Scheme.Modules.pullback i).obj L).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent] :
    degreeOn k sX i hdim L =
      eulerCharacteristic k (i ≫ sX) ((Scheme.Modules.pullback i).obj L) -
        eulerCharacteristic k (i ≫ sX) (SheafOfModules.unit C.ringCatSheaf) := rfl

end MMP.Mori
