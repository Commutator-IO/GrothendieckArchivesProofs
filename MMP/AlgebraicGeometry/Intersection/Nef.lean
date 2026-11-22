module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive

/-!
# Nef divisors and numerical equivalence

Let `X` be a normal scheme of finite type over a field `k`. A *closed curve* `C ⊆ X` is an
integral closed subscheme of dimension one. A `ℚ`-Cartier `ℚ`-divisor `D` on `X` is *nef* if
`(D · C) ≥ 0` for every closed curve `C ⊆ X` proper over `k`; two `ℚ`-Cartier `ℚ`-divisors
`D₁, D₂` are *numerically equivalent*, `D₁ ≡ D₂`, if `(D₁ · C) = (D₂ · C)` for every such curve,
and `D` is *numerically trivial* if `D ≡ 0`. When `X` is proper over `k` every closed curve is
proper over `k`. An invertible sheaf `L` on a `k`-scheme `X`, or a Cartier divisor `D` through
`L = 𝒪_X(D)`, is *nef* if `deg_C L ≥ 0` for every such curve.

## Main definitions

* `MMP.Mori.IsNef`: nef invertible sheaves.
* `MMP.Mori.Divisor.IsNef`: nef Cartier divisors.
* `MMP.Mori.QDivisor.IsNef`: nef `ℚ`-Cartier `ℚ`-divisors.
* `MMP.Mori.QDivisor.NumericallyEquivalent`: numerical equivalence `D₁ ≡ D₂`.
* `MMP.Mori.QDivisor.IsNumericallyTrivial`: numerically trivial `ℚ`-Cartier `ℚ`-divisors.

## Main results

* `MMP.Mori.Divisor.isNef_iff`: a Cartier divisor is nef if and only if its invertible sheaf is.
* `MMP.Mori.QDivisor.isNef_toQDivisor_iff`: a Cartier divisor is nef as a `ℚ`-divisor if and
  only if it is nef as a Cartier divisor.
* `MMP.Mori.QDivisor.IsNef.add`: a sum of nef `ℚ`-divisors is nef.
* `MMP.Mori.QDivisor.NumericallyEquivalent.refl`, `.symm`, `.trans`: numerical equivalence is an
  equivalence relation on `ℚ`-Cartier `ℚ`-divisors.
* `MMP.Mori.QDivisor.NumericallyEquivalent.isNef_iff`: nefness is a numerical property.

## Implementation notes

A closed curve `C ⊆ X` is a closed immersion `i : C ⟶ X` from an integral scheme `C` of
dimension one, and "proper over `k`" is properness of `i ≫ sX`, where `sX` is the structure
morphism of `X`; this is the curve data `MMP.Mori.QDivisor.intersectionNumber` and
`MMP.Mori.degreeOn` take, with `dim C ≤ 1` deduced from `dim C = 1`. Quantifying over closed
immersions rather than over closed subschemes is the same condition, since every closed subscheme
is the image of a closed immersion and the degree is computed on the source.

The definitions do not assume `X` proper over `k`: for proper `X` the properness of `i ≫ sX` is
automatic (a closed immersion is proper, and properness is stable under composition), so the
definitions specialise to the ones for proper `X`, where every closed curve is quantified over.
The `ℚ`-Cartier (resp. Cartier) condition is part of the predicates, so that `D.IsNef` and
`D₁ ≡ D₂` are predicates on divisors alone; the intersection numbers do not depend on the proof
of that condition.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-! ### Nef invertible sheaves and Cartier divisors -/

/-- An invertible sheaf `L` on a `k`-scheme `X` (structure morphism `sX`) is *nef* if
`deg_C L ≥ 0` for every closed curve `C ⊆ X` proper over `k`, that is, every closed immersion
`i : C ⟶ X` from an integral scheme of dimension one with `i ≫ sX` proper. -/
@[mmp "def_km2c_nef_cartier"]
def IsNef (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : Prop :=
  ∀ (C : Scheme.{u}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
    (hC : topologicalKrullDim C = 1), 0 ≤ degreeOn k sX i hC.le L

namespace Divisor

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- A divisor `D` on a normal `k`-scheme `X`, quasi-compact over `k`, is a *nef Cartier divisor*
if it is Cartier and `deg_C 𝒪_X(D) ≥ 0` for every closed curve `C ⊆ X` proper over `k`. -/
@[mmp "def_km2c_nef_cartier"]
def IsNef (D : Divisor X) : Prop :=
  ∃ hD : D.IsCartier,
    ∀ (C : Scheme.{u}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
      (hC : topologicalKrullDim C = 1), 0 ≤ D.degreeOn k sX i hC.le hD

/-- A Cartier divisor is nef if and only if its invertible sheaf `𝒪_X(D)` is. -/
theorem isNef_iff (D : Divisor X) (hD : D.IsCartier) :
    D.IsNef k sX ↔
      haveI := QuasiCompact.compactSpace_of_compactSpace sX
      haveI := hD.isInvertibleModule_divisorialSheaf
      Mori.IsNef k sX D.divisorialSheaf :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hD, h⟩⟩

end Divisor

/-! ### Nef `ℚ`-divisors and numerical equivalence -/

namespace QDivisor

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- A `ℚ`-divisor `D` on a normal `k`-scheme `X`, quasi-compact over `k`, is *nef* if it is
`ℚ`-Cartier and `(D · C) ≥ 0` for every closed curve `C ⊆ X` proper over `k` (every closed curve,
when `X` is proper over `k`). -/
@[mmp "def_km0_nef"]
def IsNef (D : QDivisor X) : Prop :=
  ∃ hD : D.IsQCartier,
    ∀ (C : Scheme.{u}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
      (hC : topologicalKrullDim C = 1), 0 ≤ D.intersectionNumber k sX i hC.le hD

/-- `ℚ`-divisors `D₁, D₂` on a normal `k`-scheme `X`, quasi-compact over `k`, are *numerically
equivalent*, `D₁ ≡ D₂`, if they are `ℚ`-Cartier and `(D₁ · C) = (D₂ · C)` for every closed curve
`C ⊆ X` proper over `k`. -/
@[mmp "def_km0_numerical_equivalence"]
def NumericallyEquivalent (D₁ D₂ : QDivisor X) : Prop :=
  ∃ (h₁ : D₁.IsQCartier) (h₂ : D₂.IsQCartier),
    ∀ (C : Scheme.{u}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
      (hC : topologicalKrullDim C = 1),
      D₁.intersectionNumber k sX i hC.le h₁ = D₂.intersectionNumber k sX i hC.le h₂

omit [QuasiCompact sX] in
/-- The zero `ℚ`-divisor is `ℚ`-Cartier. -/
theorem isQCartier_zero : (0 : QDivisor X).IsQCartier := by
  simpa using isQCartier_toQDivisor (Divisor.isCartier_zero (X := X))

/-- A `ℚ`-divisor `D` is *numerically trivial* if `D ≡ 0`. -/
@[mmp "def_km0_numerically_trivial"]
def IsNumericallyTrivial (D : QDivisor X) : Prop :=
  D.NumericallyEquivalent k sX 0

variable {k sX}

/-- The definition of nefness, for a given proof of the `ℚ`-Cartier condition. -/
theorem isNef_iff (D : QDivisor X) (hD : D.IsQCartier) :
    D.IsNef k sX ↔
      ∀ (C : Scheme.{u}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
        (hC : topologicalKrullDim C = 1), 0 ≤ D.intersectionNumber k sX i hC.le hD :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hD, h⟩⟩

/-- A nef `ℚ`-divisor is `ℚ`-Cartier. -/
theorem IsNef.isQCartier {D : QDivisor X} (h : D.IsNef k sX) : D.IsQCartier := h.1

/-- The definition of numerical equivalence, for given proofs of the `ℚ`-Cartier conditions. -/
theorem numericallyEquivalent_iff (D₁ D₂ : QDivisor X) (h₁ : D₁.IsQCartier)
    (h₂ : D₂.IsQCartier) :
    D₁.NumericallyEquivalent k sX D₂ ↔
      ∀ (C : Scheme.{u}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
        (hC : topologicalKrullDim C = 1),
        D₁.intersectionNumber k sX i hC.le h₁ = D₂.intersectionNumber k sX i hC.le h₂ :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨h₁, h₂, h⟩⟩

/-- A `ℚ`-Cartier `ℚ`-divisor is numerically equivalent to itself. -/
theorem NumericallyEquivalent.refl {D : QDivisor X} (hD : D.IsQCartier) :
    D.NumericallyEquivalent k sX D :=
  ⟨hD, hD, fun _ _ _ _ _ _ => rfl⟩

/-- Numerical equivalence is symmetric. -/
theorem NumericallyEquivalent.symm {D₁ D₂ : QDivisor X} (h : D₁.NumericallyEquivalent k sX D₂) :
    D₂.NumericallyEquivalent k sX D₁ :=
  let ⟨h₁, h₂, h⟩ := h
  ⟨h₂, h₁, fun C i _ _ _ hC => (h C i hC).symm⟩

/-- Numerical equivalence is transitive. -/
theorem NumericallyEquivalent.trans {D₁ D₂ D₃ : QDivisor X}
    (h : D₁.NumericallyEquivalent k sX D₂) (h' : D₂.NumericallyEquivalent k sX D₃) :
    D₁.NumericallyEquivalent k sX D₃ :=
  let ⟨h₁, _, h⟩ := h
  let ⟨_, h₃, h'⟩ := h'
  ⟨h₁, h₃, fun C i _ _ _ hC => (h C i hC).trans (h' C i hC)⟩

/-- Numerically equivalent `ℚ`-divisors have the same intersection number with every closed
curve proper over `k`. -/
theorem NumericallyEquivalent.intersectionNumber_eq {D₁ D₂ : QDivisor X}
    (h : D₁.NumericallyEquivalent k sX D₂) (h₁ : D₁.IsQCartier) (h₂ : D₂.IsQCartier)
    {C : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
    (hC : topologicalKrullDim C = 1) :
    D₁.intersectionNumber k sX i hC.le h₁ = D₂.intersectionNumber k sX i hC.le h₂ :=
  (numericallyEquivalent_iff D₁ D₂ h₁ h₂).mp h C i hC

/-- **Nefness is a numerical property.** -/
theorem NumericallyEquivalent.isNef_iff {D₁ D₂ : QDivisor X}
    (h : D₁.NumericallyEquivalent k sX D₂) : D₁.IsNef k sX ↔ D₂.IsNef k sX := by
  obtain ⟨h₁, h₂, h⟩ := h
  rw [QDivisor.isNef_iff D₁ h₁, QDivisor.isNef_iff D₂ h₂]
  exact forall_congr' fun C => forall_congr' fun i =>
    ⟨fun H _ _ _ hC => (H hC).trans_eq (h C i hC),
      fun H _ _ _ hC => (H hC).trans_eq (h C i hC).symm⟩

/-- A numerically trivial `ℚ`-divisor is `ℚ`-Cartier and meets every closed curve proper over
`k` in degree zero. -/
theorem isNumericallyTrivial_iff (D : QDivisor X) :
    D.IsNumericallyTrivial k sX ↔
      ∃ hD : D.IsQCartier,
        ∀ (C : Scheme.{u}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C]
          [IsProper (i ≫ sX)] (hC : topologicalKrullDim C = 1),
          D.intersectionNumber k sX i hC.le hD = 0 := by
  constructor
  · rintro ⟨hD, h0, h⟩
    refine ⟨hD, fun C i _ _ _ hC => ?_⟩
    rw [h C i hC, intersectionNumber_eq_of_smul k sX i hC.le 0 h0 one_pos 0
      Divisor.isCartier_zero (by simp), Divisor.degreeOn_zero']
    simp
  · rintro ⟨hD, h⟩
    refine ⟨hD, isQCartier_zero, fun C i _ _ _ hC => ?_⟩
    rw [h C i hC, intersectionNumber_eq_of_smul k sX i hC.le 0 isQCartier_zero one_pos 0
      Divisor.isCartier_zero (by simp), Divisor.degreeOn_zero']
    simp

/-- A Cartier divisor is nef as a `ℚ`-divisor if and only if it is nef as a Cartier divisor. -/
theorem isNef_toQDivisor_iff (E : Divisor X) (hE : E.IsCartier) :
    (Divisor.toQDivisor E).IsNef k sX ↔ E.IsNef k sX := by
  rw [QDivisor.isNef_iff _ (isQCartier_toQDivisor hE)]
  refine ⟨fun h => ⟨hE, fun C i _ _ _ hC => ?_⟩, fun ⟨_, h⟩ C i _ _ _ hC => ?_⟩
  · simpa [intersectionNumber_toQDivisor k sX i hC.le E hE] using h C i hC
  · rw [intersectionNumber_toQDivisor k sX i hC.le E hE]
    exact_mod_cast h C i hC

/-- A sum of nef `ℚ`-divisors is nef. -/
theorem IsNef.add {D D' : QDivisor X} (h : D.IsNef k sX) (h' : D'.IsNef k sX) :
    (D + D').IsNef k sX := by
  obtain ⟨hD, h⟩ := h
  obtain ⟨hD', h'⟩ := h'
  refine ⟨hD.add hD', fun C i _ _ _ hC => ?_⟩
  rw [intersectionNumber_add' k sX i hC.le D D' hD hD']
  exact add_nonneg (h C i hC) (h' C i hC)

end QDivisor

end MMP.Mori
