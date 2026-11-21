module

public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic

/-!
# Additivity of the degree along a curve

Let `X` be a normal `k`-scheme, quasi-compact over `k`, and `i : C ⟶ X` a curve of dimension at
most one proper over `k`. The degree along `C` is additive on tensor products of invertible
sheaves, `deg_C(L ⊗ M) = deg_C L + deg_C M` [Stacks, Tag 0AYX], and therefore on Cartier
divisors, `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')`, since
`𝒪_X(E + E') ≅ 𝒪_X(E) ⊗ 𝒪_X(E')`. Consequently the intersection number `(D · C)` of a
`ℚ`-Cartier `ℚ`-divisor may be computed with any multiplier, and is additive in `D`.

## Main results

* `MMP.Mori.degreeOn_tensorSheaf`: `deg_C(L ⊗ M) = deg_C L + deg_C M`.
* `MMP.Mori.Divisor.degreeOn_add`: `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')`.
* `MMP.Mori.Divisor.degreeOn_nsmul'`: `deg_C 𝒪_X(nD) = n · deg_C 𝒪_X(D)`.
* `MMP.Mori.QDivisor.intersectionNumber_eq_of_smul`: `(D · C) = (1 / m) · deg_C 𝒪_X(mD)` for
  every `m > 0` such that `mD` is Cartier.
* `MMP.Mori.QDivisor.intersectionNumber_add'`: `((D + D') · C) = (D · C) + (D' · C)`.

## Implementation notes

The degree of the pull-back `i^*(L ⊗ M)` is computed through `i^*(L ⊗ M) ≅ i^*L ⊗ i^*M`
[Stacks, Tag 01CD]; the additivity on `C` holds on every proper scheme of dimension at most one
over `k`, so no integrality of `C` is needed.

## References

* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [R. Hartshorne, *Algebraic geometry*][Har77], II.6.13
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

variable (k : Type u) [Field k] {X C : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (i : C ⟶ X)
  [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)

/-- **Additivity of the degree** [Stacks, Tag 0AYX]: `deg_C(L ⊗ M) = deg_C L + deg_C M` for
invertible sheaves `L` and `M` on `X`. -/
theorem degreeOn_tensorSheaf (L M : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [hLM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj L).obj M)] :
    degreeOn k sX i hdim (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj L).obj M) =
      degreeOn k sX i hdim L + degreeOn k sX i hdim M := by
  have : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨C.toRingedSpace.presheaf,
        C.toRingedSpace.IsSheaf⟩).obj ((Scheme.Modules.pullback i).obj L)).obj
          ((Scheme.Modules.pullback i).obj M)) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible C.presheaf C.ringCatSheaf.2
      _ _
  exact (@invertibleCurveDegree_eq_of_iso k _ C (i ≫ sX) _ hdim _ _
    (isInvertible_pullback_obj i _ (hL := hLM)) this
    (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso i L M)).trans
    (invertibleCurveDegree_tensorSheaf_eq_add k (i ≫ sX) hdim _ _)

/-- The degree along a curve is an isomorphism invariant. -/
theorem degreeOn_eq_of_iso {L L' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    degreeOn k sX i hdim L = degreeOn k sX i hdim L' :=
  invertibleCurveDegree_eq_of_iso k (i ≫ sX) hdim ((Scheme.Modules.pullback i).mapIso e)

section Divisor

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

namespace Divisor

/-- **Additivity of the degree on Cartier divisors**:
`deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')`. -/
theorem degreeOn_add (E E' : Divisor X) (hE : E.IsCartier) (hE' : E'.IsCartier) :
    (E + E').degreeOn k sX i hdim (hE.add hE') =
      E.degreeOn k sX i hdim hE + E'.degreeOn k sX i hdim hE' := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hE.isInvertibleModule_divisorialSheaf
  have := hE'.isInvertibleModule_divisorialSheaf
  have := (hE.add hE').isInvertibleModule_divisorialSheaf
  have := hE.isInvertibleModule_tensorSheaf hE'
  change Mori.degreeOn k sX i hdim (E + E').divisorialSheaf =
    Mori.degreeOn k sX i hdim E.divisorialSheaf + Mori.degreeOn k sX i hdim E'.divisorialSheaf
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso k sX i hdim (hE.divisorialSheafTensorIso hE')).symm

/-- `deg_C 𝒪_X(0) = 0`. -/
theorem degreeOn_zero' : (0 : Divisor X).degreeOn k sX i hdim isCartier_zero = 0 :=
  degreeOn_zero k sX i hdim (degreeOn_add k sX i hdim)

/-- `deg_C 𝒪_X(nD) = n · deg_C 𝒪_X(D)` for a Cartier divisor `D`. -/
theorem degreeOn_nsmul' (D : Divisor X) (hD : D.IsCartier) (n : ℕ) :
    (n • D).degreeOn k sX i hdim (hD.nsmul n) = n * D.degreeOn k sX i hdim hD :=
  degreeOn_nsmul k sX i hdim (degreeOn_add k sX i hdim) D hD n

end Divisor

namespace QDivisor

/-- **Independence of the multiplier.** `(D · C) = (1 / m) · deg_C 𝒪_X(mD)` for every `m > 0`
such that `mD` is a Cartier divisor `E`. -/
theorem intersectionNumber_eq_of_smul (D : QDivisor X) (hD : D.IsQCartier) {m : ℕ}
    (hm : 0 < m) (E : Divisor X) (hE : E.IsCartier) (h : Divisor.toQDivisor E = (m : ℤ) • D) :
    D.intersectionNumber k sX i hdim hD = (E.degreeOn k sX i hdim hE : ℚ) / m :=
  intersectionNumber_eq_of_toQDivisor_eq_smul k sX i hdim (Divisor.degreeOn_add k sX i hdim)
    D hD hm E hE h

/-- **Additivity of the intersection number.** `((D + D') · C) = (D · C) + (D' · C)`. -/
theorem intersectionNumber_add' (D D' : QDivisor X) (hD : D.IsQCartier) (hD' : D'.IsQCartier)
    (hDD' : (D + D').IsQCartier) :
    (D + D').intersectionNumber k sX i hdim hDD' =
      D.intersectionNumber k sX i hdim hD + D'.intersectionNumber k sX i hdim hD' :=
  intersectionNumber_add k sX i hdim (Divisor.degreeOn_add k sX i hdim) D D' hD hD' hDD'

end QDivisor

end Divisor

end MMP.Mori
