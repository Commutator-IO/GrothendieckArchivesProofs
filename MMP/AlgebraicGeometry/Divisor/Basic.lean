module

public import MMP.Attr
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# Varieties, prime divisors, divisors and rational functions

This file sets up the basic language of Kollár–Mori, Notation 0.4.

A *variety* over a field `k` is an integral separated scheme of finite type over `k`; a *curve*
is a variety of dimension one, and a variety is *normal*, *proper* or *projective* when it is so
as a scheme over `k`.

A *prime divisor* on a scheme `X` is an irreducible and reduced (that is, integral) closed
subscheme of codimension one. A *divisor with coefficients in `R`* is a finite formal
`R`-linear combination of prime divisors, an element of the free `R`-module on the prime
divisors; for `R = ℤ`, `ℚ`, `ℝ` these are the divisors, `ℚ`-divisors and `ℝ`-divisors. The
*support* of such a divisor is the union of the prime divisors with nonzero coefficient.

The *ring of rational functions* of `X` is the product, over the irreducible components `Z` of
`X`, of the local rings `𝒪_{X,η_Z}` at their generic points, and the *sheaf of rational
functions* `𝒦_X` has sections `𝒦_X(U) = ∏_{η_Z ∈ U} 𝒪_{X,η_Z}` with projections as
restrictions. The *smooth locus* of a morphism `f : X ⟶ Y` is the union of the opens of `X` on
which `f` is smooth.

## Main definitions

* `MMP.Mori.IsVariety`, `MMP.Mori.IsCurve`, `MMP.Mori.IsNormalVariety`,
  `MMP.Mori.IsProperVariety`, `MMP.Mori.IsProjectiveVariety`: varieties and their adjectives.
* `MMP.Mori.PrimeDivisor`: prime divisors, with `MMP.Mori.PrimeDivisor.genericPoint` and the
  local ring `MMP.Mori.PrimeDivisor.localRing`.
* `MMP.Mori.DivisorWithCoeffs`: finite `R`-linear combinations of prime divisors, with
  `MMP.Mori.DivisorWithCoeffs.coeff` and `MMP.Mori.DivisorWithCoeffs.mapCoeffs`.
* `MMP.Mori.Divisor`, `MMP.Mori.QDivisor`, `MMP.Mori.RDivisor`: the cases `ℤ`, `ℚ`, `ℝ`, with
  the maps `MMP.Mori.Divisor.toQDivisor`, `MMP.Mori.Divisor.toRDivisor`,
  `MMP.Mori.QDivisor.toRDivisor`.
* `MMP.Mori.DivisorWithCoeffs.supp`: the support, a closed subset, and
  `MMP.Mori.DivisorWithCoeffs.suppIdeal`, the ideal sheaf of its reduced structure.
* `MMP.Mori.RationalFunctions`, `MMP.Mori.rationalFunctionsSheaf`: the ring and the sheaf of
  rational functions, with `MMP.Mori.toRationalFunctionsPresheaf : 𝒪_X ⟶ 𝒦_X`.
* `MMP.Mori.smoothLocus`, `MMP.Mori.IsSmoothScheme`, `MMP.Mori.singularLocus`.

## Main results

* `MMP.Mori.Divisor.tensorEquiv`: `Div(X) ⊗_ℤ R ≃ DivisorWithCoeffs R X`.
* `MMP.Mori.QDivisor.mem_range_toQDivisor_iff`: a divisor is a `ℚ`-divisor with integral
  coefficients.
* `MMP.Mori.DivisorWithCoeffs.mem_supp_iff`, `MMP.Mori.DivisorWithCoeffs.isClosed_supp`: the
  support is the finite union of the prime divisors with nonzero coefficient.
* `MMP.Mori.isSheaf_rationalFunctionsPresheaf`: `𝒦_X` is a sheaf.
* `MMP.Mori.rationalFunctionsEquivStalks`, `MMP.Mori.rationalFunctionsEquivFunctionField`:
  comparison with the rational maps to the affine line (Stacks 01RV) and, for integral `X`,
  with the function field.
* `MMP.Mori.smoothLocus_eq_smoothLocus`: for `f` locally of finite presentation the smooth
  locus is Mathlib's pointwise `AlgebraicGeometry.Scheme.Hom.smoothLocus`.

## Implementation notes

The prime divisors are those of `AlgebraicGeometry.PrimeDivisor`: integral closed subschemes,
presented by their ideal sheaves, whose generic point has closure of codimension one. Nothing
is assumed of `X`; normality is needed only for the theory of principal divisors.

Divisors are finitely supported functions `PrimeDivisor X →₀ R`, the free `R`-module on the
prime divisors. On a Noetherian scheme every locally finite sum is finite, so these agree with
the locally finite Weil divisors `AlgebraicGeometry.WeilDivisor` there.

Kollár–Mori index the ring of rational functions of a Noetherian normal scheme by its connected
components `X_i`, with factors the function fields `K(X_i)`. On such a scheme the connected
components are the irreducible components, and `𝒪_{X,η_i} = 𝒪_{X_i,η_i} = K(X_i)`, so the
product over irreducible components of the local rings at their generic points is the same
ring; that product makes sense for every scheme, and is the ring of rational maps to the affine
line when there are finitely many irreducible components. The index set of `𝒦_X(U)` is the set
of components whose generic point lies in `U`, which is the set of components meeting `U`
(`MMP.Mori.genericPoint_mem_iff`).

The smooth locus is defined, as in the source, as the union of the opens on which the morphism
is smooth; it makes sense for any morphism.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4
* [R. Hartshorne, *Algebraic geometry*][Har77], II.6
* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace MMP.Mori

/-! ### Varieties -/

section Variety

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A *variety* over a field `k` is a scheme `X` with a structure morphism `f : X ⟶ Spec k`
such that `X` is integral and `f` is separated and of finite type. -/
abbrev IsVariety : Prop := AlgebraicGeometry.IsVariety k f

/-- A *curve* over `k` is a variety of dimension one. -/
abbrev IsCurve : Prop := AlgebraicGeometry.IsCurve k f

/-- A variety is *normal* when it is normal as a scheme: every local ring is an integrally
closed domain. -/
@[mmp "def_km0_variety"]
def IsNormalVariety : Prop := IsVariety k f ∧ IsNormal X

/-- A variety is *proper* when its structure morphism is proper. -/
abbrev IsProperVariety : Prop := AlgebraicGeometry.IsProperVariety k f

/-- A variety is *projective* when its structure morphism is projective. -/
abbrev IsProjectiveVariety : Prop := AlgebraicGeometry.IsProjectiveVariety k f

/-- `X` is a variety over `k` if and only if `X` is integral and `f` is separated, locally of
finite type and quasi-compact. -/
theorem isVariety_iff : IsVariety k f ↔
    IsIntegral X ∧ IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f :=
  ⟨fun h => ⟨h.toIsIntegral, h.toIsSeparated, h.toLocallyOfFiniteType, h.toQuasiCompact⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ => @AlgebraicGeometry.IsVariety.mk k _ X f h₁ h₂ h₃ h₄⟩

/-- `X` is a curve over `k` if and only if it is a variety of Krull dimension one. -/
theorem isCurve_iff : IsCurve k f ↔ IsVariety k f ∧ topologicalKrullDim X = 1 :=
  AlgebraicGeometry.isCurve_iff k f

/-- `X` is a proper variety over `k` if and only if it is a variety and `f` is proper. -/
theorem isProperVariety_iff : IsProperVariety k f ↔ IsVariety k f ∧ IsProper f :=
  AlgebraicGeometry.isProperVariety_iff k f

/-- `X` is a projective variety over `k` if and only if it is a variety and `f` is
projective. -/
theorem isProjectiveVariety_iff :
    IsProjectiveVariety k f ↔ IsVariety k f ∧ IsProjectiveMorphism f :=
  AlgebraicGeometry.isProjectiveVariety_iff k f

end Variety

/-! ### Prime divisors -/

/-- A *prime divisor* on a scheme `X` is an irreducible and reduced closed subscheme of
codimension one, that is, an integral closed subscheme whose generic point has closure of
codimension one in `X`. -/
abbrev PrimeDivisor (X : Scheme.{u}) : Type u := AlgebraicGeometry.PrimeDivisor X

namespace PrimeDivisor

variable {X : Scheme.{u}} (D : PrimeDivisor X)

/-- The generic point `η_D` of a prime divisor `D`, as a point of `X`. -/
abbrev genericPoint : X := AlgebraicGeometry.PrimeDivisor.genericPoint D

/-- The local ring `𝒪_{X,D} = 𝒪_{X,η_D}` of `X` along a prime divisor `D`. -/
@[mmp "def_km0_prime_divisor"]
abbrev localRing : CommRingCat.{u} := X.presheaf.stalk D.genericPoint

/-- The closure of the generic point of a prime divisor has codimension one. -/
theorem codimension_closure_genericPoint :
    codimension (IrreducibleCloseds.closureSingleton D.genericPoint) = 1 :=
  D.codimension_closureSingleton_genericPoint

end PrimeDivisor

/-! ### Divisors with coefficients -/

/-- A *divisor with coefficients in `R`* on `X` is a finite formal `R`-linear combination
`∑ dᵢ Dᵢ` of pairwise distinct prime divisors, that is, an element of the free `R`-module on the
prime divisors of `X`. -/
abbrev DivisorWithCoeffs (R : Type*) [Zero R] (X : Scheme.{u}) := PrimeDivisor X →₀ R

/-- A *divisor* (Weil divisor) on `X` is a finite formal `ℤ`-linear combination of pairwise
distinct prime divisors, an element of the free abelian group `Div(X)` on the prime divisors. -/
@[mmp "def_km0_divisor"]
abbrev Divisor (X : Scheme.{u}) := DivisorWithCoeffs ℤ X

/-- A *`ℚ`-divisor* on `X` is a finite formal `ℚ`-linear combination of pairwise distinct prime
divisors, an element of `Div(X) ⊗_ℤ ℚ`. -/
@[mmp "def_km0_q_divisor"]
abbrev QDivisor (X : Scheme.{u}) := DivisorWithCoeffs ℚ X

/-- An *`ℝ`-divisor* on `X` is a finite formal `ℝ`-linear combination of pairwise distinct prime
divisors, an element of `Div(X) ⊗_ℤ ℝ`. -/
@[mmp "def_km0_real_divisor"]
abbrev RDivisor (X : Scheme.{u}) := DivisorWithCoeffs ℝ X

namespace DivisorWithCoeffs

variable {R S T : Type*} {X : Scheme.{u}}

section Zero

variable [Zero R]

/-- The *coefficient* of a prime divisor `E` in `D = ∑ dᵢ Dᵢ`: `dᵢ` if `E = Dᵢ`, and `0` if
`E` is none of the `Dᵢ`. -/
@[mmp "def_km0_divisor"]
def coeff (D : DivisorWithCoeffs R X) (E : PrimeDivisor X) : R := D E

/-- The coefficient of `E` in `D` is the value of `D` at `E`. -/
theorem coeff_apply (D : DivisorWithCoeffs R X) (E : PrimeDivisor X) : D.coeff E = D E := rfl

/-- Two divisors with the same coefficient at every prime divisor are equal. -/
@[ext]
theorem ext' {D D' : DivisorWithCoeffs R X} (h : ∀ E, D.coeff E = D'.coeff E) : D = D' :=
  Finsupp.ext h

/-- The coefficient of `E` in the divisor `r E` is `r`. -/
theorem coeff_single_self (E : PrimeDivisor X) (r : R) :
    coeff (Finsupp.single E r) E = r :=
  Finsupp.single_eq_same

/-- The coefficient of `E'` in the divisor `r E` is `0` when `E ≠ E'`. -/
theorem coeff_single_of_ne {E E' : PrimeDivisor X} (h : E ≠ E') (r : R) :
    coeff (Finsupp.single E r) E' = 0 :=
  Finsupp.single_eq_of_ne' h

/-- Every coefficient of the zero divisor is `0`. -/
@[simp]
theorem coeff_zero (E : PrimeDivisor X) : coeff (0 : DivisorWithCoeffs R X) E = 0 := rfl

/-- The *support* `Supp D` of a divisor `D = ∑ dᵢ Dᵢ` is the closed subset `⋃_{dᵢ ≠ 0} Dᵢ`. -/
@[mmp "def_km0_support"]
def supp (D : DivisorWithCoeffs R X) : Closeds X :=
  D.support.sup fun E => E.idealSheaf.support

/-- The ideal sheaf of the reduced closed subscheme structure on the support `Supp D`. -/
@[mmp "def_km0_support"]
def suppIdeal (D : DivisorWithCoeffs R X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal D.supp

/-- The support `Supp D`, regarded as a reduced closed subscheme of `X`. -/
@[mmp "def_km0_support"]
abbrev suppScheme (D : DivisorWithCoeffs R X) : Scheme.{u} := D.suppIdeal.subscheme

/-- A point lies in `Supp D` if and only if it lies on a prime divisor with nonzero coefficient
in `D`. -/
theorem mem_supp_iff {D : DivisorWithCoeffs R X} {x : X} :
    x ∈ D.supp ↔ ∃ E, D.coeff E ≠ 0 ∧ x ∈ E.support := by
  rw [supp, ← SetLike.mem_coe, Closeds.coe_finset_sup, Finset.sup_eq_iSup]
  simp [PrimeDivisor.support, coeff_apply]

/-- As a set, `Supp D` is the union of the prime divisors with nonzero coefficient in `D`. -/
theorem coe_supp (D : DivisorWithCoeffs R X) :
    (D.supp : Set X) = ⋃ E ∈ D.support, E.support := by
  ext x
  rw [SetLike.mem_coe, mem_supp_iff]
  simp [coeff_apply]

/-- The support of a divisor is a closed subset of `X`. -/
theorem isClosed_supp (D : DivisorWithCoeffs R X) : IsClosed (D.supp : Set X) :=
  D.supp.isClosed

/-- The support of the ideal sheaf `suppIdeal D` is `Supp D`. -/
@[simp]
theorem coe_support_suppIdeal (D : DivisorWithCoeffs R X) :
    (D.suppIdeal.support : Set X) = D.supp := by
  simp [suppIdeal]

/-- The support of the zero divisor is empty. -/
@[simp]
theorem supp_zero : (0 : DivisorWithCoeffs R X).supp = ⊥ := by
  simp [supp]

/-- A prime divisor with nonzero coefficient in `D` is contained in `Supp D`. -/
theorem support_subset_supp {D : DivisorWithCoeffs R X} {E : PrimeDivisor X}
    (h : D.coeff E ≠ 0) : E.support ⊆ D.supp :=
  fun _ hx => mem_supp_iff.mpr ⟨E, h, hx⟩

/-- The support of the divisor `r E` is contained in `E`. -/
theorem supp_single_le (E : PrimeDivisor X) (r : R) :
    supp (Finsupp.single E r : DivisorWithCoeffs R X) ≤ E.idealSheaf.support := by
  intro x hx
  obtain ⟨E', h, hx⟩ := mem_supp_iff.mp hx
  by_cases hE : E = E'
  · exact hE ▸ hx
  · exact absurd (coeff_single_of_ne hE r) h

/-- Changing the coefficients of a divisor along a map `f : R → S` with `f 0 = 0`. -/
def mapCoeffs [Zero S] (f : R → S) (hf : f 0 = 0) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs S X :=
  Finsupp.mapRange f hf D

/-- The coefficient of `E` in `D.mapCoeffs f hf` is `f` of the coefficient of `E` in `D`. -/
@[simp]
theorem coeff_mapCoeffs [Zero S] (f : R → S) (hf : f 0 = 0) (D : DivisorWithCoeffs R X)
    (E : PrimeDivisor X) : (D.mapCoeffs f hf).coeff E = f (D.coeff E) :=
  Finsupp.mapRange_apply

/-- Changing coefficients along an injective map is injective. -/
theorem mapCoeffs_injective [Zero S] {f : R → S} (hf : f 0 = 0) (hinj : Function.Injective f) :
    Function.Injective (mapCoeffs (X := X) f hf) :=
  Finsupp.mapRange_injective f hf hinj

/-- Changing coefficients along `f` and then along `g` is changing them along `g ∘ f`. -/
theorem mapCoeffs_mapCoeffs [Zero S] [Zero T] (f : R → S) (hf : f 0 = 0) (g : S → T)
    (hg : g 0 = 0) (D : DivisorWithCoeffs R X) :
    (D.mapCoeffs f hf).mapCoeffs g hg = D.mapCoeffs (g ∘ f) (by simp [hf, hg]) := by
  ext E
  simp [mapCoeffs]

/-- Changing coefficients along an injective map preserves the support. -/
theorem supp_mapCoeffs [Zero S] {f : R → S} (hf : f 0 = 0) (hinj : Function.Injective f)
    (D : DivisorWithCoeffs R X) : (D.mapCoeffs f hf).supp = D.supp := by
  ext x
  simp only [SetLike.mem_coe, mem_supp_iff, coeff_mapCoeffs, ne_eq]
  refine exists_congr fun E => and_congr_left fun _ => ?_
  rw [← hf]
  exact hinj.ne_iff

end Zero

section AddMonoid

variable [AddCommMonoid R]

/-- The coefficients of `D + D'` are the sums of the coefficients of `D` and `D'`. -/
@[simp]
theorem coeff_add (D D' : DivisorWithCoeffs R X) (E : PrimeDivisor X) :
    (D + D').coeff E = D.coeff E + D'.coeff E := rfl

/-- The coefficient of `E`, as an additive map. -/
def coeffAddMonoidHom (E : PrimeDivisor X) : DivisorWithCoeffs R X →+ R :=
  Finsupp.applyAddHom E

/-- `coeffAddMonoidHom E` sends `D` to its coefficient at `E`. -/
@[simp]
theorem coeffAddMonoidHom_apply (E : PrimeDivisor X) (D : DivisorWithCoeffs R X) :
    coeffAddMonoidHom E D = D.coeff E := rfl

/-- The support of `D + D'` is contained in the union of the supports of `D` and `D'`. -/
theorem supp_add_le (D D' : DivisorWithCoeffs R X) : (D + D').supp ≤ D.supp ⊔ D'.supp := by
  intro x hx
  obtain ⟨E, h, hx⟩ := mem_supp_iff.mp hx
  rw [coeff_add] at h
  by_cases hD : D.coeff E = 0
  · rw [hD, zero_add] at h
    exact Or.inr (mem_supp_iff.mpr ⟨E, h, hx⟩)
  · exact Or.inl (mem_supp_iff.mpr ⟨E, hD, hx⟩)

/-- Changing the coefficients of a divisor along an additive map, as an additive map. -/
def mapCoeffsAddMonoidHom [AddCommMonoid S] (f : R →+ S) :
    DivisorWithCoeffs R X →+ DivisorWithCoeffs S X :=
  Finsupp.mapRange.addMonoidHom f

/-- `mapCoeffsAddMonoidHom f` sends `D` to `D.mapCoeffs f`. -/
@[simp]
theorem mapCoeffsAddMonoidHom_apply [AddCommMonoid S] (f : R →+ S) (D : DivisorWithCoeffs R X) :
    mapCoeffsAddMonoidHom f D = D.mapCoeffs f (map_zero f) := rfl

end AddMonoid

section AddGroup

variable [AddCommGroup R]

/-- The coefficients of `-D` are the negatives of the coefficients of `D`. -/
@[simp]
theorem coeff_neg (D : DivisorWithCoeffs R X) (E : PrimeDivisor X) :
    (-D).coeff E = -D.coeff E := rfl

/-- The coefficients of `D - D'` are the differences of the coefficients of `D` and `D'`. -/
@[simp]
theorem coeff_sub (D D' : DivisorWithCoeffs R X) (E : PrimeDivisor X) :
    (D - D').coeff E = D.coeff E - D'.coeff E := rfl

/-- `-D` and `D` have the same support. -/
@[simp]
theorem supp_neg (D : DivisorWithCoeffs R X) : (-D).supp = D.supp := by
  ext x
  simp [mem_supp_iff]

end AddGroup

section Module

variable [Semiring R] [AddCommMonoid S] [Module R S]

/-- The coefficients of `r • D` are `r` times the coefficients of `D`. -/
@[simp]
theorem coeff_smul (r : R) (D : DivisorWithCoeffs S X) (E : PrimeDivisor X) :
    (r • D).coeff E = r • D.coeff E := rfl

end Module

end DivisorWithCoeffs

open DivisorWithCoeffs

/-! ### The maps `Div(X) → Div(X)_ℚ → Div(X)_ℝ` -/

open scoped Classical in
/-- `Div(X) ⊗_ℤ R` is the module of divisors with coefficients in `R`. -/
def Divisor.tensorEquiv (R : Type*) [AddCommGroup R] (X : Scheme.{u}) :
    TensorProduct ℤ (Divisor X) R ≃ₗ[ℤ] DivisorWithCoeffs R X :=
  TensorProduct.finsuppScalarLeft ℤ R (PrimeDivisor X)

open scoped Classical in
/-- Under `Div(X) ⊗_ℤ R ≃ DivisorWithCoeffs R X`, the coefficient of `E` in `D ⊗ r` is the
coefficient of `E` in `D` times `r`. -/
@[simp]
theorem Divisor.coeff_tensorEquiv_tmul {R : Type*} [AddCommGroup R] {X : Scheme.{u}}
    (D : Divisor X) (r : R) (E : PrimeDivisor X) :
    (Divisor.tensorEquiv R X (D ⊗ₜ r)).coeff E = D.coeff E • r :=
  TensorProduct.finsuppScalarLeft_apply_tmul_apply D r E

variable {X : Scheme.{u}}

/-- A divisor, regarded as a `ℚ`-divisor. -/
@[mmp "def_km0_q_divisor"]
def Divisor.toQDivisor : Divisor X →+ QDivisor X :=
  mapCoeffsAddMonoidHom (Int.castAddHom ℚ)

/-- A divisor, regarded as an `ℝ`-divisor. -/
@[mmp "def_km0_real_divisor"]
def Divisor.toRDivisor : Divisor X →+ RDivisor X :=
  mapCoeffsAddMonoidHom (Int.castAddHom ℝ)

/-- A `ℚ`-divisor, regarded as an `ℝ`-divisor. -/
@[mmp "def_km0_real_divisor"]
def QDivisor.toRDivisor : QDivisor X →+ RDivisor X :=
  mapCoeffsAddMonoidHom (Rat.castHom ℝ).toAddMonoidHom

/-- The coefficients of a divisor regarded as a `ℚ`-divisor are its integer coefficients. -/
@[simp]
theorem Divisor.coeff_toQDivisor (D : Divisor X) (E : PrimeDivisor X) :
    (Divisor.toQDivisor D).coeff E = (D.coeff E : ℚ) := rfl

/-- The coefficients of a divisor regarded as an `ℝ`-divisor are its integer coefficients. -/
@[simp]
theorem Divisor.coeff_toRDivisor (D : Divisor X) (E : PrimeDivisor X) :
    (Divisor.toRDivisor D).coeff E = (D.coeff E : ℝ) := rfl

/-- The coefficients of a `ℚ`-divisor regarded as an `ℝ`-divisor are its rational
coefficients. -/
@[simp]
theorem QDivisor.coeff_toRDivisor (D : QDivisor X) (E : PrimeDivisor X) :
    (QDivisor.toRDivisor D).coeff E = (D.coeff E : ℝ) := rfl

/-- The map from divisors to `ℚ`-divisors is injective. -/
theorem Divisor.toQDivisor_injective : Function.Injective (Divisor.toQDivisor (X := X)) :=
  mapCoeffs_injective (f := ((↑) : ℤ → ℚ)) Int.cast_zero Int.cast_injective

/-- The map from divisors to `ℝ`-divisors is injective. -/
theorem Divisor.toRDivisor_injective : Function.Injective (Divisor.toRDivisor (X := X)) :=
  mapCoeffs_injective (f := ((↑) : ℤ → ℝ)) Int.cast_zero Int.cast_injective

/-- The map from `ℚ`-divisors to `ℝ`-divisors is injective. -/
theorem QDivisor.toRDivisor_injective : Function.Injective (QDivisor.toRDivisor (X := X)) :=
  mapCoeffs_injective (f := ((↑) : ℚ → ℝ)) Rat.cast_zero Rat.cast_injective

/-- The composite `Div(X) → Div(X)_ℚ → Div(X)_ℝ` is the map `Div(X) → Div(X)_ℝ`. -/
theorem QDivisor.toRDivisor_toQDivisor (D : Divisor X) :
    QDivisor.toRDivisor (Divisor.toQDivisor D) = Divisor.toRDivisor D := by
  ext E
  exact Rat.cast_intCast (D E)

/-- A divisor and the `ℚ`-divisor it defines have the same support. -/
@[simp]
theorem Divisor.supp_toQDivisor (D : Divisor X) : (Divisor.toQDivisor D).supp = D.supp :=
  supp_mapCoeffs (f := ((↑) : ℤ → ℚ)) Int.cast_zero Int.cast_injective D

/-- A divisor and the `ℝ`-divisor it defines have the same support. -/
@[simp]
theorem Divisor.supp_toRDivisor (D : Divisor X) : (Divisor.toRDivisor D).supp = D.supp :=
  supp_mapCoeffs (f := ((↑) : ℤ → ℝ)) Int.cast_zero Int.cast_injective D

/-- A `ℚ`-divisor and the `ℝ`-divisor it defines have the same support. -/
@[simp]
theorem QDivisor.supp_toRDivisor (D : QDivisor X) : (QDivisor.toRDivisor D).supp = D.supp :=
  supp_mapCoeffs (f := ((↑) : ℚ → ℝ)) Rat.cast_zero Rat.cast_injective D

/-- A divisor is a `ℚ`-divisor with integral coefficients. -/
theorem QDivisor.mem_range_toQDivisor_iff (D : QDivisor X) :
    D ∈ Set.range (Divisor.toQDivisor (X := X)) ↔ ∀ E, ∃ n : ℤ, D.coeff E = n := by
  refine ⟨?_, fun h => ⟨D.mapCoeffs Rat.num Rat.num_zero, ?_⟩⟩
  · rintro ⟨D', rfl⟩ E
    exact ⟨D'.coeff E, rfl⟩
  · ext E
    obtain ⟨n, hn⟩ := h E
    change (((D E).num : ℤ) : ℚ) = D E
    rw [← coeff_apply, hn, Rat.num_intCast]

/-! ### Rational functions -/

section RationalFunctions

variable (X)

/-- The generic point `η_Z` of an irreducible component `Z` of `X`. -/
abbrev componentGenericPoint (Z : irreducibleComponents X) : X := Z.2.1.genericPoint

/-- `η_Z` is a generic point of the irreducible component `Z`. -/
theorem isGenericPoint_componentGenericPoint (Z : irreducibleComponents X) :
    IsGenericPoint (componentGenericPoint X Z) Z.1 :=
  Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)

variable {X} in
/-- An open `U` contains the generic point of an irreducible component `Z` exactly when it meets
`Z`. -/
theorem genericPoint_mem_iff (Z : irreducibleComponents X) (U : X.Opens) :
    componentGenericPoint X Z ∈ U ↔ ((U : Set X) ∩ Z.1).Nonempty := by
  rw [Set.inter_comm]
  exact (isGenericPoint_componentGenericPoint X Z).mem_open_set_iff U.isOpen

/-- The *ring of rational functions* `K(X) = ∏_Z 𝒪_{X,η_Z}` of a scheme `X`, the product over its
irreducible components `Z` of the local rings at their generic points. For a Noetherian normal
scheme, whose irreducible components are its connected components `Xᵢ` (normal integral
schemes), this is `∏ᵢ K(Xᵢ)`. -/
@[mmp "def_km0_rational_functions"]
abbrev RationalFunctions : Type u :=
  ∀ Z : irreducibleComponents X, X.presheaf.stalk (componentGenericPoint X Z)

/-- The `Z`-th component `φ_Z ∈ 𝒪_{X,η_Z}` of a rational function, as a ring homomorphism. -/
@[mmp "def_km0_rational_functions"]
def RationalFunctions.component (Z : irreducibleComponents X) :
    RationalFunctions X →+* X.presheaf.stalk (componentGenericPoint X Z) :=
  Pi.evalRingHom _ Z

/-- The unit group of `K(X)` is the product of the unit groups of its factors. -/
@[mmp "def_km0_rational_functions"]
def RationalFunctions.unitsEquiv :
    (RationalFunctions X)ˣ ≃*
      ∀ Z : irreducibleComponents X, (X.presheaf.stalk (componentGenericPoint X Z))ˣ :=
  MulEquiv.piUnits

/-- On a reduced scheme every factor `𝒪_{X,η_Z}` of `K(X)` is a field. -/
theorem RationalFunctions.isField_stalk [IsReduced X] (Z : irreducibleComponents X) :
    IsField (X.presheaf.stalk (componentGenericPoint X Z)) := by
  apply isField_stalk_of_closure_mem_irreducibleComponents
  rw [(isGenericPoint_componentGenericPoint X Z).def]
  exact Z.2

/-- The local ring `𝒪_{X,x}` at a point `x` of an irreducible component `Z` maps to the factor
`𝒪_{X,η_Z}` of `K(X)` by generization. -/
@[mmp "def_km0_rational_functions"]
def stalkToRationalFunctions {x : X} {Z : irreducibleComponents X} (hx : x ∈ Z.1) :
    X.presheaf.stalk x ⟶ X.presheaf.stalk (componentGenericPoint X Z) :=
  X.presheaf.stalkSpecializes ((isGenericPoint_componentGenericPoint X Z).specializes hx)

/-- The *sheaf of rational functions* `𝒦_X`, as a presheaf: its sections over `U` are
`∏_{η_Z ∈ U} 𝒪_{X,η_Z}`, the product over the irreducible components meeting `U`, and the
restriction maps are the projections. -/
@[mmp "def_km0_rational_functions"]
def rationalFunctionsPresheaf : TopCat.Presheaf CommRingCat.{u} X where
  obj U := CommRingCat.of
    (∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.unop},
      X.presheaf.stalk (componentGenericPoint X Z.1))
  map {U _} i := CommRingCat.ofHom
    (RingHom.pi fun Z => Pi.evalRingHom
      (fun Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.unop} =>
        X.presheaf.stalk (componentGenericPoint X Z.1)) ⟨Z.1, i.unop.le Z.2⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restriction maps of `𝒦_X` are the projections onto the components meeting the smaller
open. -/
@[simp]
theorem rationalFunctionsPresheaf_map_apply {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (s : ToType ((rationalFunctionsPresheaf X).obj U))
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ V.unop}) :
    (rationalFunctionsPresheaf X).map i s Z = s ⟨Z.1, i.unop.le Z.2⟩ := rfl

/-- The inclusion `𝒪_X ⟶ 𝒦_X`: a section over `U` goes to its germs at the generic points of the
irreducible components meeting `U`. -/
@[mmp "def_km0_rational_functions"]
def toRationalFunctionsPresheaf : X.presheaf ⟶ rationalFunctionsPresheaf X where
  app U := CommRingCat.ofHom
    (RingHom.pi fun Z => (X.presheaf.germ U.unop (componentGenericPoint X Z.1) Z.2).hom)
  naturality {U V} i := by
    ext s
    funext Z
    exact TopCat.Presheaf.germ_res_apply' X.presheaf i _ Z.2 s

/-- The presheaf of rational functions `𝒦_X` is a sheaf. -/
theorem isSheaf_rationalFunctionsPresheaf : (rationalFunctionsPresheaf X).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hmem : ∀ Z : irreducibleComponents X, componentGenericPoint X Z ∈ iSup U →
      ∃ i, componentGenericPoint X Z ∈ U i := fun Z h => Opens.mem_iSup.mp h
  have hagree : ∀ (i j : ι) (Z : irreducibleComponents X) (hi : componentGenericPoint X Z ∈ U i)
      (hj : componentGenericPoint X Z ∈ U j), sf i ⟨Z, hi⟩ = sf j ⟨Z, hj⟩ :=
    fun i j Z hi hj => congrFun (hsf i j) ⟨Z, ⟨hi, hj⟩⟩
  refine ⟨fun Z => sf (hmem Z.1 Z.2).choose ⟨Z.1, (hmem Z.1 Z.2).choose_spec⟩, ?_, ?_⟩
  · intro i
    funext Z
    exact hagree _ _ _ _ _
  · intro s hs
    funext Z
    exact (congrFun (hs _) ⟨Z.1, (hmem Z.1 Z.2).choose_spec⟩).symm ▸ rfl

/-- The *sheaf of rational functions* `𝒦_X` of a scheme `X`, with `𝒦_X(U) = ∏_{η_Z ∈ U} 𝒪_{X,η_Z}`
over the irreducible components `Z` meeting `U`. -/
@[mmp "def_km0_rational_functions"]
def rationalFunctionsSheaf : TopCat.Sheaf CommRingCat.{u} X :=
  ⟨rationalFunctionsPresheaf X, isSheaf_rationalFunctionsPresheaf X⟩

/-- The global sections of `𝒦_X` are the rational functions `K(X)`. -/
def rationalFunctionsPresheafTopEquiv :
    ToType ((rationalFunctionsPresheaf X).obj (op ⊤)) ≃+* RationalFunctions X where
  toFun s Z := s ⟨Z, trivial⟩
  invFun φ Z := φ Z.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- For a scheme with finitely many irreducible components, the ring of rational maps from `X`
to the affine line (Stacks 01RV) is `K(X)`. -/
def rationalFunctionsEquivStalks [Finite (irreducibleComponents X)] :=
  (Stacks.Chow.rationalFunctionsEquivStalks X).1

/-- For an integral scheme `K(X)` is the function field. -/
def rationalFunctionsEquivFunctionField [IsIntegral X] :
    RationalFunctions X ≃+* X.functionField := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  exact (rationalFunctionsEquivStalks X).symm.trans
    (Stacks.Chow.rationalFunctionsEquivFunctionField X).1

end RationalFunctions

/-! ### The smooth locus -/

section SmoothLocus

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The *smooth locus* `X_sm` of `f : X ⟶ Y`: the union of all opens `U ⊆ X` on which `f` is
smooth. -/
@[mmp "def_km0_smooth_locus"]
def smoothLocus : X.Opens := sSup {U : X.Opens | Smooth (U.ι ≫ f)}

/-- `X` is *smooth* (non-singular) over `Y` when its smooth locus is all of `X`. -/
@[mmp "def_km0_smooth_locus"]
def IsSmoothScheme : Prop := smoothLocus f = ⊤

/-- The *singular locus* `Sing(X) = X ∖ X_sm`, a closed subset. -/
@[mmp "def_km0_smooth_locus"]
def singularLocus : Closeds X := (smoothLocus f).compl

variable {f} in
/-- A point lies in the smooth locus of `f` if and only if it has an open neighbourhood on
which `f` is smooth. -/
theorem mem_smoothLocus_iff {x : X} :
    x ∈ smoothLocus f ↔ ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f) := by
  rw [smoothLocus, Opens.mem_sSup]
  exact ⟨fun ⟨U, hU, hx⟩ => ⟨U, hx, hU⟩, fun ⟨U, hx, hU⟩ => ⟨U, hU, hx⟩⟩

variable {f} in
/-- A point lies in the singular locus of `f` if and only if it is not in the smooth locus. -/
theorem mem_singularLocus_iff {x : X} : x ∈ singularLocus f ↔ x ∉ smoothLocus f := Iff.rfl

/-- An open on which `f` is smooth is contained in the smooth locus of `f`. -/
theorem le_smoothLocus {U : X.Opens} (hU : Smooth (U.ι ≫ f)) : U ≤ smoothLocus f :=
  le_sSup hU

/-- For a morphism locally of finite presentation (for example a scheme of finite type over a
field), the smooth locus is the set of points at which `f` is smooth. -/
theorem smoothLocus_eq_smoothLocus [LocallyOfFinitePresentation f] :
    smoothLocus f = f.smoothLocus := by
  ext x
  rw [SetLike.mem_coe, mem_smoothLocus_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨U, hx, hU⟩
    have h := (U.ι ≫ f).smoothLocus_eq_top
    rw [← Scheme.Hom.preimage_smoothLocus_eq] at h
    exact (h ▸ trivial : (⟨x, hx⟩ : U) ∈ U.ι ⁻¹ᵁ f.smoothLocus)
  · intro hx
    refine ⟨f.smoothLocus, hx, ?_⟩
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      Scheme.Opens.ι_preimage_self]

/-- For `f` locally of finite presentation, `X` is smooth over `Y` if and only if `f` is
smooth. -/
theorem isSmoothScheme_iff [LocallyOfFinitePresentation f] : IsSmoothScheme f ↔ Smooth f := by
  rw [IsSmoothScheme, smoothLocus_eq_smoothLocus, Scheme.Hom.smoothLocus_eq_top_iff]

end SmoothLocus

end MMP.Mori
