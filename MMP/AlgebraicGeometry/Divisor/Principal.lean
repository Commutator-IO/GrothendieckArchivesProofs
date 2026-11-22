module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FibreStalkBridges
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE

/-!
# Principal divisors, linear equivalence and Cartier divisors

Let `X` be a locally Noetherian normal scheme. Every point of `X` lies on exactly one irreducible
component, and for a prime divisor `D` with generic point `η_D` on the component `X_{i(D)}` the
local ring `𝒪_{X,D} = 𝒪_{X,η_D}` is a discrete valuation ring whose fraction field is the factor
`𝒪_{X,η_{i(D)}} = K(X_{i(D)})` of the ring of rational functions `K(X)`. For a unit `φ` of `K(X)`
the order `v_D(φ)` is the normalized valuation of `𝒪_{X,D}` applied to the component
`φ_{i(D)}`. When `X` is moreover quasi-compact, hence Noetherian, only finitely many prime
divisors have `v_D(φ) ≠ 0`, and the *principal divisor* is `div(φ) = ∑_D v_D(φ) D`; `div` is a
homomorphism `K(X)^× → Div(X)`. Two divisors are *linearly equivalent* if their difference is
principal.

A divisor `D` is *Cartier* if every point has an open neighbourhood `U` on which `D` agrees with
some `div(φ)` at every prime divisor meeting `U`; a `ℚ`-divisor is *`ℚ`-Cartier* if a nonzero
integral multiple of it is a Cartier divisor, and its *Cartier index* is the least positive such
multiple. Finally the *multiplicity* of a prime divisor `D` along an irreducible closed subset `Z`
is the largest power of the maximal ideal of `𝒪_{X,Z}` containing the ideal of `D` there.

## Main definitions

* `MMP.Mori.PrimeDivisor.component`: the irreducible component of `X` containing `D`.
* `MMP.Mori.PrimeDivisor.valuation`, `MMP.Mori.PrimeDivisor.ord`: the order of vanishing `v_D`.
* `MMP.Mori.principalDivisor`, `MMP.Mori.principalDivisorHom`: `div(φ)` and `div` as a group
  homomorphism.
* `MMP.Mori.Divisor.LinearlyEquivalent`: linear equivalence of divisors.
* `MMP.Mori.Divisor.IsLocalEquation`, `MMP.Mori.Divisor.IsCartier`: local equations and Cartier
  divisors, with the subgroup `MMP.Mori.Divisor.cartierSubgroup`.
* `MMP.Mori.QDivisor.IsCartierDivisor`, `MMP.Mori.QDivisor.IsQCartier`,
  `MMP.Mori.QDivisor.cartierIndex`: `ℚ`-Cartier `ℚ`-divisors and the Cartier index `m_D`.
* `MMP.Mori.PrimeDivisor.multiplicityAlong`: the multiplicity `mult_Z D`.

## Main results

* `MMP.Mori.eq_of_mem_irreducibleComponents`, `MMP.Mori.PrimeDivisor.eq_component`: on a normal
  scheme a point, and so a prime divisor, lies on exactly one irreducible component.
* `MMP.Mori.isFractionRing_stalkToRationalFunctions`: `𝒪_{X,η_Z}` is the fraction field of
  `𝒪_{X,x}` for `x ∈ Z`.
* `MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing`: `𝒪_{X,D}` is a discrete valuation
  ring, and `MMP.Mori.PrimeDivisor.ord_eq_one_of_irreducible`,
  `MMP.Mori.PrimeDivisor.ord_eq_zero_of_isUnit`: `v_D` is its normalized valuation.
* `MMP.Mori.finite_ord_ne_zero`: `v_D(φ) ≠ 0` for only finitely many `D` [Har77, II.6.1].
* `MMP.Mori.principalDivisor_mul`, `MMP.Mori.Divisor.linearlyEquivalent_equivalence`.
* `MMP.Mori.Divisor.isCartier_principalDivisor`, `MMP.Mori.Divisor.IsCartier.neg`,
  `MMP.Mori.QDivisor.IsQCartier.exists_pos`, `MMP.Mori.QDivisor.cartierIndex_pos`,
  `MMP.Mori.QDivisor.cartierIndex_le`.

## Implementation notes

The component `X_{i(D)}` is chosen among the irreducible components containing `D`; on a normal
scheme there is only one (`MMP.Mori.PrimeDivisor.eq_component`), so nothing depends on the
choice. The valuation `v_D` is `Ring.ordFrac` of `𝒪_{X,D}` (Stacks 02MD, the extension of
`a ↦ length(𝒪_{X,D}/(a))` to the fraction field), transported to `𝒪_{X,η_{i(D)}}` along the
identification of the latter with the fraction field; on the discrete valuation ring `𝒪_{X,D}`
this is the normalized valuation.

The order `v_D` and the Cartier condition need only that `X` be locally Noetherian and normal;
the principal divisor needs finiteness of its support, and is defined under the hypotheses
`IsLocallyNoetherian X` and `CompactSpace X`, which together say that `X` is Noetherian.

The multiplicity is defined through the ideal `I_{D,η_Z}` of `D` in `𝒪_{X,Z}` rather than through a
chosen local equation `g` of `D` at `η_Z`: when `D` is Cartier at `η_Z` (for instance on a smooth
variety) `I_{D,η_Z} = (g)`, and then `I_{D,η_Z} ⊆ 𝔪_Z^s` if and only if `g ∈ 𝔪_Z^s`
(`MMP.Mori.PrimeDivisor.multiplicityAlong_eq_of_stalkIdeal_eq_span`). It takes values in `ℕ∞`,
and is finite whenever `𝒪_{X,Z}` is Noetherian and `I_{D,η_Z} ≠ 0`, by Krull's intersection
theorem.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4,
  Lemma 2.29
* [R. Hartshorne, *Algebraic geometry*][Har77], II.6
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Order Topology
open scoped WithZero

universe u

namespace MMP.Mori

variable {X : Scheme.{u}}

/-! ### The local ring along a prime divisor and the function field of its component -/

/-- On a normal scheme, the local ring `𝒪_{X,η_Z}` at the generic point of an irreducible
component `Z` is the fraction field of the local ring `𝒪_{X,x}` at any point `x` of `Z`, through
the generization map. -/
theorem isFractionRing_stalkToRationalFunctions [IsNormal X] {x : X}
    {Z : irreducibleComponents X} (hx : x ∈ Z.1) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk (componentGenericPoint X Z)) :=
      (stalkToRationalFunctions X hx).hom.toAlgebra
    IsFractionRing (X.presheaf.stalk x) (X.presheaf.stalk (componentGenericPoint X Z)) := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk (componentGenericPoint X Z)) :=
      (stalkToRationalFunctions X hx).hom.toAlgebra
  let P := (IsLocalRing.maximalIdeal (X.presheaf.stalk (componentGenericPoint X Z))).under
    (X.presheaf.stalk x)
  have hloc : IsLocalization P.primeCompl (X.presheaf.stalk (componentGenericPoint X Z)) :=
    Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes
      ((isGenericPoint_componentGenericPoint X Z).specializes hx)
  have hm : IsLocalRing.maximalIdeal (X.presheaf.stalk (componentGenericPoint X Z)) = ⊥ :=
    (IsLocalRing.isField_iff_maximalIdeal_eq).mp (RationalFunctions.isField_stalk X Z)
  have hM : P.primeCompl = nonZeroDivisors (X.presheaf.stalk x) := by
    ext a
    rw [mem_nonZeroDivisors_iff_ne_zero]
    refine ⟨fun ha h => ha (h ▸ P.zero_mem), fun ha h => ha ?_⟩
    have h' : algebraMap _ (X.presheaf.stalk (componentGenericPoint X Z)) a ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk (componentGenericPoint X Z)) := h
    rw [hm, Ideal.mem_bot] at h'
    exact IsLocalization.injective (M := P.primeCompl) _ (Ideal.primeCompl_le_nonZeroDivisors P)
      (h'.trans (map_zero _).symm)
  exact (hM ▸ hloc : IsLocalization (nonZeroDivisors (X.presheaf.stalk x))
    (X.presheaf.stalk (componentGenericPoint X Z)))

/-- On a normal scheme the generization map `𝒪_{X,x} ⟶ 𝒪_{X,η_Z}` is injective. -/
theorem stalkToRationalFunctions_injective [IsNormal X] {x : X}
    {Z : irreducibleComponents X} (hx : x ∈ Z.1) :
    Function.Injective (stalkToRationalFunctions X hx).hom := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk (componentGenericPoint X Z)) :=
      (stalkToRationalFunctions X hx).hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions hx
  exact IsFractionRing.injective (X.presheaf.stalk x)
    (X.presheaf.stalk (componentGenericPoint X Z))

/-- On a normal scheme the generic point of an irreducible component `Z` through `x` is the point
of `Spec 𝒪_{X,x}` given by the zero ideal of the domain `𝒪_{X,x}`. -/
theorem componentGenericPoint_eq_fromSpecStalk [IsNormal X] {x : X}
    {Z : irreducibleComponents X} (hx : x ∈ Z.1) :
    componentGenericPoint X Z = X.fromSpecStalk x ⟨⊥, Ideal.isPrime_bot⟩ := by
  have h := Scheme.SpecMap_stalkSpecializes_fromSpecStalk
    ((isGenericPoint_componentGenericPoint X Z).specializes hx)
  have h1 := congrArg (fun f => f (IsLocalRing.closedPoint _)) h
  simp only [Scheme.fromSpecStalk_closedPoint] at h1
  rw [← h1]
  refine congrArg (X.fromSpecStalk x) (PrimeSpectrum.ext ?_)
  ext a
  change (X.presheaf.stalkSpecializes _).hom a ∈ IsLocalRing.maximalIdeal _ ↔ a = 0
  rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp (RationalFunctions.isField_stalk X Z),
    Ideal.mem_bot]
  exact ⟨fun ha => stalkToRationalFunctions_injective hx (ha.trans (map_zero _).symm),
    fun ha => ha ▸ map_zero _⟩

/-- On a normal scheme every point lies on exactly one irreducible component. -/
theorem eq_of_mem_irreducibleComponents [IsNormal X] {x : X}
    {Z Z' : irreducibleComponents X} (hx : x ∈ Z.1) (hx' : x ∈ Z'.1) : Z = Z' := by
  have h : componentGenericPoint X Z = componentGenericPoint X Z' := by
    rw [componentGenericPoint_eq_fromSpecStalk hx, componentGenericPoint_eq_fromSpecStalk hx']
  apply Subtype.ext
  rw [← (isGenericPoint_componentGenericPoint X Z).def,
    ← (isGenericPoint_componentGenericPoint X Z').def, h]

/-- On a Noetherian scheme, only finitely many points of codimension one lie in the closure of a
point `η` but outside an open neighbourhood `U` of `η`. -/
theorem finite_coheight_eq_one_mem_closure_notMem [NoetherianSpace X] (η : X) (U : X.Opens)
    (hη : η ∈ U) :
    {z : X | z ∈ closure {η} ∧ z ∉ U ∧ coheight z = 1}.Finite := by
  have hlt : ∀ {a b : X}, a ≤ b → a ≠ b → a < b := fun hab hne ↦
    lt_iff_le_not_ge.mpr ⟨hab, fun h ↦ hne (Specializes.antisymm h hab).eq⟩
  set S : Set X := closure {η} ∩ (U : Set X)ᶜ with hS
  have hSc : IsClosed S := isClosed_closure.inter U.isOpen.isClosed_compl
  obtain ⟨𝒮, h𝒮fin, h𝒮closed, h𝒮irr, h𝒮cover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hSc
  lift 𝒮 to Finset (Set X) using h𝒮fin
  have key : ∀ z : X, z ∈ closure {η} → z ∉ U → coheight z = 1 →
      closure ({z} : Set X) ∈ 𝒮 := by
    intro z hzη hzU hzc
    have hcl : closure ({z} : Set X) ⊆ ⋃₀ (𝒮 : Set (Set X)) := by
      rw [← h𝒮cover]
      exact closure_minimal (Set.singleton_subset_iff.mpr ⟨hzη, hzU⟩) hSc
    obtain ⟨t, htS, hzt⟩ := isIrreducible_iff_sUnion_isClosed.mp
      isIrreducible_singleton.closure 𝒮 (fun s hs ↦ h𝒮closed s hs) hcl
    set τ := (h𝒮irr t htS).genericPoint with hτdef
    have hgen : closure ({τ} : Set X) = t :=
      (h𝒮irr t htS).isGenericPoint_genericPoint (h𝒮closed t htS)
    have hτS : τ ∈ S := by
      rw [h𝒮cover]
      exact Set.mem_sUnion_of_mem (hgen ▸ subset_closure rfl) htS
    have hτη : τ < η :=
      hlt (specializes_iff_mem_closure.mpr hτS.1) fun h ↦ hτS.2 (h ▸ hη)
    have hone : (1 : ℕ∞) ≤ coheight τ := le_trans le_add_self (coheight_add_one_le hτη)
    have hzτ : z ≤ τ := specializes_iff_mem_closure.mpr (hgen ▸ hzt (subset_closure rfl))
    have hz : z = τ := by
      by_contra hne
      have hstep := coheight_add_one_le (hlt hzτ hne)
      rw [hzc] at hstep
      exact absurd ((by gcongr : (1 : ℕ∞) + 1 ≤ coheight τ + 1).trans hstep) (by decide)
    rw [hz, hgen]
    exact htS
  refine Set.Finite.of_finite_image (f := fun z ↦ closure ({z} : Set X))
    (𝒮.finite_toSet.subset ?_) ?_
  · rintro - ⟨z, ⟨hzη, hzU, hzc⟩, rfl⟩
    exact key z hzη hzU hzc
  · intro a _ b _ hab
    exact (show IsGenericPoint a (closure ({b} : Set X)) from hab).eq isGenericPoint_closure

namespace PrimeDivisor

variable (D : PrimeDivisor X)

/-- Some irreducible component of `X` contains the closure of the generic point of `D`. -/
theorem exists_component :
    ∃ Z ∈ irreducibleComponents X, closure {D.genericPoint} ⊆ Z :=
  exists_mem_irreducibleComponents_subset_of_isIrreducible _ isIrreducible_singleton.closure

/-- An irreducible component `X_{i(D)}` of `X` containing the prime divisor `D`. On a normal
scheme it is the only one (`MMP.Mori.PrimeDivisor.eq_component`). -/
@[mmp "def_km0_principal_divisor"]
def component : irreducibleComponents X :=
  ⟨D.exists_component.choose, D.exists_component.choose_spec.1⟩

/-- `D` is contained in its chosen component `X_{i(D)}`. -/
theorem support_subset_component : D.support ⊆ D.component.1 := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact D.exists_component.choose_spec.2

/-- The generic point of `D` lies in its chosen component `X_{i(D)}`. -/
theorem genericPoint_mem_component : D.genericPoint ∈ D.component.1 :=
  D.exists_component.choose_spec.2 (subset_closure rfl)

/-- On a normal scheme a prime divisor lies in exactly one irreducible component. -/
@[mmp "def_km0_principal_divisor"]
theorem eq_component [IsNormal X] {Z : irreducibleComponents X}
    (hZ : D.support ⊆ Z.1) : Z = D.component := by
  have hD : D.genericPoint ∈ D.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  exact eq_of_mem_irreducibleComponents (hZ hD) D.genericPoint_mem_component

/-- The generic point of the component of `D` specializes to the generic point of `D`. -/
theorem specializes_genericPoint :
    componentGenericPoint X D.component ⤳ D.genericPoint :=
  (isGenericPoint_componentGenericPoint X D.component).specializes D.genericPoint_mem_component

/-- The generic point of a prime divisor has codimension one. -/
theorem coheight_genericPoint : coheight D.genericPoint = 1 :=
  AlgebraicGeometry.PrimeDivisor.coheight_genericPoint D

/-- The generization map `𝒪_{X,D} ⟶ 𝒪_{X,η_{i(D)}}` into the factor of `K(X)` along the component
of `D`. -/
abbrev toComponent : D.localRing ⟶ X.presheaf.stalk (componentGenericPoint X D.component) :=
  stalkToRationalFunctions X D.genericPoint_mem_component

variable [IsLocallyNoetherian X] [IsNormal X]

/-- The order of vanishing `v_D` along `D`, on the factor `𝒪_{X,η_{i(D)}}` of `K(X)`, the fraction
field of the one-dimensional normal Noetherian local domain `𝒪_{X,D}`: the extension to the
fraction field of `a ↦ length(𝒪_{X,D}/(a))`, which is the normalized valuation of the discrete
valuation ring `𝒪_{X,D}`. -/
def valuation : X.presheaf.stalk (componentGenericPoint X D.component) →*₀ ℤᵐ⁰ :=
  letI := D.toComponent.hom.toAlgebra
  haveI := isFractionRing_stalkToRationalFunctions D.genericPoint_mem_component
  haveI : Ring.KrullDimLE 1 D.localRing := krullDimLE_of_coheight_le D.coheight_genericPoint.le
  (Ring.ordFrac D.localRing).comp
    (IsLocalization.algEquiv (nonZeroDivisors D.localRing)
      (X.presheaf.stalk (componentGenericPoint X D.component))
      (FractionRing D.localRing)).toRingEquiv.toMonoidWithZeroHom

/-- `v_D` takes the value `1` on the image of a unit of `𝒪_{X,D}`. -/
theorem valuation_toComponent_of_isUnit {a : D.localRing} (ha : IsUnit a) :
    D.valuation (D.toComponent.hom a) = 1 := by
  let := D.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions D.genericPoint_mem_component
  have : Ring.KrullDimLE 1 D.localRing := krullDimLE_of_coheight_le D.coheight_genericPoint.le
  change Ring.ordFrac D.localRing (IsLocalization.algEquiv (nonZeroDivisors D.localRing) _
    (FractionRing D.localRing) (algebraMap D.localRing _ a)) = 1
  rw [AlgEquiv.commutes]
  exact Ring.ordFrac_of_isUnit ha

/-- The order of vanishing `v_D` on the units of `K(X)`, as a homomorphism to `Multiplicative ℤ`:
`v_D(φ) = v_D(φ_{i(D)})`. -/
def ordHom : (RationalFunctions X)ˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    ((Units.map D.valuation.toMonoidHom).comp
      (Units.map (RationalFunctions.component X D.component).toMonoidHom))

/-- The *order of vanishing* `v_D(φ) ∈ ℤ` of a unit `φ` of `K(X)` along the prime divisor `D`:
the normalized valuation of the discrete valuation ring `𝒪_{X,D}` applied to the component
`φ_{i(D)}` of `φ` in the function field of the component of `X` containing `D`. -/
@[mmp "def_km0_principal_divisor"]
def ord (φ : (RationalFunctions X)ˣ) : ℤ := Multiplicative.toAdd (D.ordHom φ)

/-- `v_D(φ)` is the additive form of `ordHom D φ`. -/
theorem ord_def (φ : (RationalFunctions X)ˣ) : D.ord φ = Multiplicative.toAdd (D.ordHom φ) := rfl

/-- `v_D(φψ) = v_D(φ) + v_D(ψ)`. -/
@[mmp "def_km0_principal_divisor", simp]
theorem ord_mul (φ ψ : (RationalFunctions X)ˣ) : D.ord (φ * ψ) = D.ord φ + D.ord ψ := by
  simp [ord]

/-- `v_D(1) = 0`. -/
@[simp]
theorem ord_one : D.ord 1 = 0 := by
  simp [ord]

/-- `v_D(φ⁻¹) = -v_D(φ)`. -/
@[simp]
theorem ord_inv (φ : (RationalFunctions X)ˣ) : D.ord φ⁻¹ = -D.ord φ := by
  simp [ord]

/-- `v_D(φ / ψ) = v_D(φ) - v_D(ψ)`. -/
@[simp]
theorem ord_div (φ ψ : (RationalFunctions X)ˣ) : D.ord (φ / ψ) = D.ord φ - D.ord ψ := by
  simp [ord]

/-- `v_D(φ ^ n) = n v_D(φ)` for a natural number `n`. -/
@[simp]
theorem ord_pow (φ : (RationalFunctions X)ˣ) (n : ℕ) : D.ord (φ ^ n) = n • D.ord φ := by
  simp [ord]

/-- `v_D(φ ^ n) = n v_D(φ)` for an integer `n`. -/
@[simp]
theorem ord_zpow (φ : (RationalFunctions X)ˣ) (n : ℤ) : D.ord (φ ^ n) = n • D.ord φ := by
  simp [ord]

/-- If the component `φ_{i(D)}` of `φ` is the image of a unit of `𝒪_{X,D}`, then `v_D(φ) = 0`. -/
theorem ord_eq_zero_of_isUnit {φ : (RationalFunctions X)ˣ} {a : D.localRing} (ha : IsUnit a)
    (hφ : D.toComponent.hom a = (φ : RationalFunctions X) D.component) : D.ord φ = 0 := by
  have h : D.valuation ((φ : RationalFunctions X) D.component) = 1 := by
    rw [← hφ, D.valuation_toComponent_of_isUnit ha]
  have : D.ordHom φ = 1 := by
    apply WithZero.unitsWithZeroEquiv.symm.injective
    ext
    simpa [ordHom, RationalFunctions.component] using h
  simp [ord, this]

/-- `v_D(φ)` is read off the valuation of the component `φ_{i(D)}`. -/
theorem valuation_component (φ : (RationalFunctions X)ˣ) :
    D.valuation ((φ : RationalFunctions X) D.component) = WithZero.exp (D.ord φ) := by
  simp [ord, ordHom, RationalFunctions.component, WithZero.exp]

/-- On a locally Noetherian normal scheme the local ring `𝒪_{X,D}` along a prime divisor is a
discrete valuation ring: a one-dimensional Noetherian normal local domain. -/
theorem isDiscreteValuationRing_localRing : IsDiscreteValuationRing D.localRing := by
  have h5 : IsNoetherianRing D.localRing ∧ IsLocalRing D.localRing ∧ IsDomain D.localRing ∧
      IsIntegrallyClosed D.localRing ∧ ringKrullDim D.localRing = 1 :=
    ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal _, by
      rw [ringKrullDim_stalk_eq_coheight, D.coheight_genericPoint]; rfl⟩
  obtain ⟨_, h⟩ := ((_root_.isDiscreteValuationRing_tfae D.localRing).out 5 1).mp h5
  exact h

/-- `v_D` is the *normalized* valuation of the discrete valuation ring `𝒪_{X,D}`: it takes the
value `1` on a uniformizer. -/
theorem valuation_toComponent_of_irreducible {ϖ : D.localRing} (hϖ : Irreducible ϖ) :
    D.valuation (D.toComponent.hom ϖ) = WithZero.exp 1 := by
  let := D.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions D.genericPoint_mem_component
  have : Ring.KrullDimLE 1 D.localRing := krullDimLE_of_coheight_le D.coheight_genericPoint.le
  have := D.isDiscreteValuationRing_localRing
  change Ring.ordFrac D.localRing (IsLocalization.algEquiv (nonZeroDivisors D.localRing) _
    (FractionRing D.localRing) (algebraMap D.localRing _ ϖ)) = _
  rw [AlgEquiv.commutes]
  exact Ring.ordFrac_irreducible hϖ

/-- If the component `φ_{i(D)}` of `φ` is the image of a uniformizer of `𝒪_{X,D}`, then
`v_D(φ) = 1`. -/
theorem ord_eq_one_of_irreducible {φ : (RationalFunctions X)ˣ} {ϖ : D.localRing}
    (hϖ : Irreducible ϖ) (hφ : D.toComponent.hom ϖ = (φ : RationalFunctions X) D.component) :
    D.ord φ = 1 := by
  have h := D.valuation_component φ
  rw [← hφ, D.valuation_toComponent_of_irreducible hϖ] at h
  exact (WithZero.exp_injective h).symm

end PrimeDivisor

/-! ### Principal divisors -/

section Principal

variable [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X]

/-- A unit `φ` of `K(X)` has nonzero order `v_D(φ)` along only finitely many prime divisors
`D`. -/
theorem finite_ord_ne_zero (φ : (RationalFunctions X)ˣ) :
    {D : PrimeDivisor X | D.ord φ ≠ 0}.Finite := by
  have hex : ∀ Z : irreducibleComponents X, ∃ (V : X.Opens) (hV : componentGenericPoint X Z ∈ V)
      (g : Γ(X, V)), X.presheaf.germ V _ hV g = (φ : RationalFunctions X) Z :=
    fun Z => X.presheaf.exists_germ_eq _
  choose V hV g hg using hex
  have hunit : ∀ Z, componentGenericPoint X Z ∈ X.basicOpen (g Z) := fun Z => by
    rw [Scheme.mem_basicOpen X (g Z) _ (hV Z), hg]
    exact φ.isUnit.map (Pi.evalRingHom _ Z)
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have : Finite (irreducibleComponents X) :=
    (NoetherianSpace.finite_irreducibleComponents (α := X)).to_subtype
  have hfin : (⋃ Z, {z : X | z ∈ closure {componentGenericPoint X Z} ∧
      z ∉ X.basicOpen (g Z) ∧ coheight z = 1}).Finite :=
    Set.finite_iUnion fun Z => finite_coheight_eq_one_mem_closure_notMem _ _ (hunit Z)
  refine Set.Finite.of_finite_image (hfin.subset ?_)
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
  rintro - ⟨D, hD, rfl⟩
  refine Set.mem_iUnion.mpr ⟨D.component, ?_, fun hmem => hD ?_, D.coheight_genericPoint⟩
  · rw [(isGenericPoint_componentGenericPoint X D.component).def]
    exact D.genericPoint_mem_component
  · have hDV : D.genericPoint ∈ V D.component := X.basicOpen_le _ hmem
    refine D.ord_eq_zero_of_isUnit (a := X.presheaf.germ _ _ hDV (g _))
      ((Scheme.mem_basicOpen X _ _ hDV).mp hmem) ?_
    rw [← hg]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

/-- The *principal divisor* `div(φ) = ∑_D v_D(φ) D` of a unit `φ` of the ring of rational
functions `K(X)` of a Noetherian normal scheme `X`, the sum over the finitely many prime
divisors `D` with `v_D(φ) ≠ 0` (`MMP.Mori.finite_ord_ne_zero`). -/
@[mmp "def_km0_principal_divisor"]
def principalDivisor (φ : (RationalFunctions X)ˣ) : Divisor X :=
  Finsupp.ofSupportFinite (fun D => D.ord φ) (finite_ord_ne_zero φ)

/-- The coefficient of `div(φ)` at a prime divisor `D` is `v_D(φ)`. -/
@[simp]
theorem coeff_principalDivisor (φ : (RationalFunctions X)ˣ) (D : PrimeDivisor X) :
    (principalDivisor φ).coeff D = D.ord φ := rfl

/-- `div(φψ) = div(φ) + div(ψ)`. -/
@[simp]
theorem principalDivisor_mul (φ ψ : (RationalFunctions X)ˣ) :
    principalDivisor (φ * ψ) = principalDivisor φ + principalDivisor ψ := by
  ext D
  simp

/-- `div(1) = 0`. -/
@[simp]
theorem principalDivisor_one : principalDivisor (1 : (RationalFunctions X)ˣ) = 0 := by
  ext D
  simp

/-- `div(φ⁻¹) = -div(φ)`. -/
@[simp]
theorem principalDivisor_inv (φ : (RationalFunctions X)ˣ) :
    principalDivisor φ⁻¹ = -principalDivisor φ := by
  ext D
  simp

/-- `div(φ / ψ) = div(φ) - div(ψ)`. -/
@[simp]
theorem principalDivisor_div (φ ψ : (RationalFunctions X)ˣ) :
    principalDivisor (φ / ψ) = principalDivisor φ - principalDivisor ψ := by
  ext D
  simp

/-- `div : K(X)^× → Div(X)` as a homomorphism of groups. -/
@[mmp "def_km0_principal_divisor"]
def principalDivisorHom : Additive (RationalFunctions X)ˣ →+ Divisor X where
  toFun φ := principalDivisor φ.toMul
  map_zero' := principalDivisor_one
  map_add' φ ψ := principalDivisor_mul φ.toMul ψ.toMul

/-- `principalDivisorHom` sends `φ` to `div(φ)`. -/
@[simp]
theorem principalDivisorHom_apply (φ : Additive (RationalFunctions X)ˣ) :
    principalDivisorHom φ = principalDivisor φ.toMul := rfl

/-! ### Linear equivalence -/

/-- Divisors `D₁, D₂` on a Noetherian normal scheme are *linearly equivalent*, `D₁ ∼ D₂`, if
`D₁ - D₂ = div(φ)` for some unit `φ` of `K(X)`. -/
@[mmp "def_km0_linear_equivalence"]
def Divisor.LinearlyEquivalent (D₁ D₂ : Divisor X) : Prop :=
  ∃ φ : (RationalFunctions X)ˣ, D₁ - D₂ = principalDivisor φ

namespace Divisor

/-- Linear equivalence is reflexive: `D ∼ D`. -/
@[refl]
theorem LinearlyEquivalent.refl (D : Divisor X) : D.LinearlyEquivalent D :=
  ⟨1, by simp⟩

/-- Linear equivalence is symmetric: `D₁ ∼ D₂` implies `D₂ ∼ D₁`. -/
@[symm]
theorem LinearlyEquivalent.symm {D₁ D₂ : Divisor X} (h : D₁.LinearlyEquivalent D₂) :
    D₂.LinearlyEquivalent D₁ := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ⁻¹, by rw [principalDivisor_inv, ← hφ, neg_sub]⟩

/-- Linear equivalence is transitive: `D₁ ∼ D₂` and `D₂ ∼ D₃` imply `D₁ ∼ D₃`. -/
@[trans]
theorem LinearlyEquivalent.trans {D₁ D₂ D₃ : Divisor X} (h₁₂ : D₁.LinearlyEquivalent D₂)
    (h₂₃ : D₂.LinearlyEquivalent D₃) : D₁.LinearlyEquivalent D₃ := by
  obtain ⟨φ, hφ⟩ := h₁₂
  obtain ⟨ψ, hψ⟩ := h₂₃
  exact ⟨φ * ψ, by rw [principalDivisor_mul, ← hφ, ← hψ, sub_add_sub_cancel]⟩

/-- Linear equivalence is an equivalence relation on `Div(X)`. -/
theorem linearlyEquivalent_equivalence :
    Equivalence (LinearlyEquivalent (X := X)) :=
  ⟨LinearlyEquivalent.refl, LinearlyEquivalent.symm, LinearlyEquivalent.trans⟩

/-- `D₁ ∼ D₂` if and only if `D₁ - D₂` lies in the subgroup of principal divisors. -/
theorem linearlyEquivalent_iff_sub_mem_range {D₁ D₂ : Divisor X} :
    D₁.LinearlyEquivalent D₂ ↔ D₁ - D₂ ∈ (principalDivisorHom (X := X)).range :=
  ⟨fun ⟨φ, hφ⟩ => ⟨Additive.ofMul φ, hφ.symm⟩, fun ⟨φ, hφ⟩ => ⟨φ.toMul, hφ.symm⟩⟩

/-- A principal divisor is linearly equivalent to `0`. -/
theorem linearlyEquivalent_principalDivisor_zero (φ : (RationalFunctions X)ˣ) :
    (principalDivisor φ).LinearlyEquivalent 0 :=
  ⟨φ, sub_zero _⟩

/-- If `D₁ ∼ D₂` and `E₁ ∼ E₂`, then `D₁ + E₁ ∼ D₂ + E₂`. -/
theorem LinearlyEquivalent.add {D₁ D₂ E₁ E₂ : Divisor X} (hD : D₁.LinearlyEquivalent D₂)
    (hE : E₁.LinearlyEquivalent E₂) : (D₁ + E₁).LinearlyEquivalent (D₂ + E₂) := by
  obtain ⟨φ, hφ⟩ := hD
  obtain ⟨ψ, hψ⟩ := hE
  exact ⟨φ * ψ, by rw [principalDivisor_mul, ← hφ, ← hψ]; abel⟩

/-- If `D₁ ∼ D₂`, then `-D₁ ∼ -D₂`. -/
theorem LinearlyEquivalent.neg {D₁ D₂ : Divisor X} (h : D₁.LinearlyEquivalent D₂) :
    (-D₁).LinearlyEquivalent (-D₂) := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ⁻¹, by rw [principalDivisor_inv, ← hφ]; abel⟩

end Divisor

end Principal

/-! ### Cartier divisors -/

section Cartier

variable [IsLocallyNoetherian X] [IsNormal X]

namespace Divisor

/-- A unit `φ` of `K(X)` is a *local equation* of the divisor `D` on the open `U` if `D` and
`div(φ)` have the same coefficient at every prime divisor meeting `U`:
`D|_U = div(φ)|_U`. -/
@[mmp "def_km0_cartier_weil_divisor"]
def IsLocalEquation (D : Divisor X) (U : X.Opens) (φ : (RationalFunctions X)ˣ) : Prop :=
  ∀ E : PrimeDivisor X, (E.support ∩ U).Nonempty → D.coeff E = E.ord φ

/-- A divisor `D` on a normal scheme is *Cartier* if every point has an open neighbourhood `U`
on which `D` has a local equation, a unit `φ` of `K(X)` with `D|_U = div(φ)|_U`. -/
@[mmp "def_km0_cartier_weil_divisor"]
def IsCartier (D : Divisor X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ φ : (RationalFunctions X)ˣ, D.IsLocalEquation U φ

/-- A local equation of `D` on `U` is a local equation of `D` on every open `V ≤ U`. -/
theorem IsLocalEquation.mono {D : Divisor X} {U V : X.Opens} {φ : (RationalFunctions X)ˣ}
    (h : D.IsLocalEquation U φ) (hVU : V ≤ U) : D.IsLocalEquation V φ :=
  fun E ⟨x, hxE, hxV⟩ => h E ⟨x, hxE, hVU hxV⟩

/-- `1` is a local equation of the zero divisor on every open `U`. -/
theorem isLocalEquation_zero (U : X.Opens) : (0 : Divisor X).IsLocalEquation U 1 :=
  fun E _ => by simp

/-- If `φ` and `ψ` are local equations of `D` and `D'` on `U`, then `φψ` is one of `D + D'`. -/
theorem IsLocalEquation.add {D D' : Divisor X} {U : X.Opens} {φ ψ : (RationalFunctions X)ˣ}
    (h : D.IsLocalEquation U φ) (h' : D'.IsLocalEquation U ψ) :
    (D + D').IsLocalEquation U (φ * ψ) :=
  fun E hE => by rw [DivisorWithCoeffs.coeff_add, h E hE, h' E hE, PrimeDivisor.ord_mul]

/-- If `φ` is a local equation of `D` on `U`, then `φ⁻¹` is one of `-D`. -/
theorem IsLocalEquation.neg {D : Divisor X} {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (h : D.IsLocalEquation U φ) : (-D).IsLocalEquation U φ⁻¹ :=
  fun E hE => by rw [DivisorWithCoeffs.coeff_neg, h E hE, PrimeDivisor.ord_inv]

/-- The zero divisor is Cartier. -/
theorem isCartier_zero : (0 : Divisor X).IsCartier :=
  fun _ => ⟨⊤, trivial, 1, isLocalEquation_zero ⊤⟩

/-- The sum of two Cartier divisors is Cartier. -/
theorem IsCartier.add {D D' : Divisor X} (h : D.IsCartier) (h' : D'.IsCartier) :
    (D + D').IsCartier := by
  intro x
  obtain ⟨U, hxU, φ, hφ⟩ := h x
  obtain ⟨U', hxU', ψ, hψ⟩ := h' x
  exact ⟨U ⊓ U', ⟨hxU, hxU'⟩, φ * ψ,
    (hφ.mono inf_le_left).add (hψ.mono inf_le_right)⟩

/-- The negative of a Cartier divisor is Cartier. -/
theorem IsCartier.neg {D : Divisor X} (h : D.IsCartier) : (-D).IsCartier := by
  intro x
  obtain ⟨U, hxU, φ, hφ⟩ := h x
  exact ⟨U, hxU, φ⁻¹, hφ.neg⟩

/-- `-D` is Cartier if and only if `D` is Cartier. -/
@[simp]
theorem isCartier_neg {D : Divisor X} : (-D).IsCartier ↔ D.IsCartier :=
  ⟨fun h => neg_neg D ▸ h.neg, IsCartier.neg⟩

/-- The difference of two Cartier divisors is Cartier. -/
theorem IsCartier.sub {D D' : Divisor X} (h : D.IsCartier) (h' : D'.IsCartier) :
    (D - D').IsCartier := by
  rw [sub_eq_add_neg]
  exact h.add h'.neg

/-- A natural multiple `nD` of a Cartier divisor `D` is Cartier. -/
theorem IsCartier.nsmul {D : Divisor X} (h : D.IsCartier) (n : ℕ) : (n • D).IsCartier := by
  induction n with
  | zero => simpa using isCartier_zero
  | succ n ih => simpa [succ_nsmul] using ih.add h

/-- An integral multiple `nD` of a Cartier divisor `D` is Cartier. -/
theorem IsCartier.zsmul {D : Divisor X} (h : D.IsCartier) (n : ℤ) : (n • D).IsCartier := by
  cases n with
  | ofNat n => simpa using h.nsmul n
  | negSucc n => simpa [negSucc_zsmul] using (h.nsmul (n + 1)).neg

/-- The *Cartier divisors*, as an additive subgroup of `Div(X)`. -/
def cartierSubgroup : AddSubgroup (Divisor X) where
  carrier := {D | D.IsCartier}
  zero_mem' := isCartier_zero
  add_mem' := IsCartier.add
  neg_mem' := IsCartier.neg

/-- A divisor lies in `cartierSubgroup` if and only if it is Cartier. -/
@[simp]
theorem mem_cartierSubgroup {D : Divisor X} : D ∈ cartierSubgroup ↔ D.IsCartier := Iff.rfl

/-- `φ` is a local equation of `div(φ)` on every open `U`. -/
theorem isLocalEquation_principalDivisor [CompactSpace X] (φ : (RationalFunctions X)ˣ)
    (U : X.Opens) : (principalDivisor φ).IsLocalEquation U φ :=
  fun _ _ => rfl

/-- A principal divisor is Cartier, with the same global local equation everywhere. -/
theorem isCartier_principalDivisor [CompactSpace X] (φ : (RationalFunctions X)ˣ) :
    (principalDivisor φ).IsCartier :=
  fun _ => ⟨⊤, trivial, φ, isLocalEquation_principalDivisor φ ⊤⟩

/-- A divisor linearly equivalent to a Cartier divisor is Cartier. -/
theorem IsCartier.of_linearlyEquivalent [CompactSpace X] {D₁ D₂ : Divisor X}
    (h : D₁.LinearlyEquivalent D₂) (h₂ : D₂.IsCartier) : D₁.IsCartier := by
  obtain ⟨φ, hφ⟩ := h
  rw [show D₁ = principalDivisor φ + D₂ by rw [← hφ, sub_add_cancel]]
  exact (isCartier_principalDivisor φ).add h₂

end Divisor

/-! ### `ℚ`-Cartier divisors and the Cartier index -/

namespace QDivisor

/-- A `ℚ`-divisor *is a Cartier divisor* if it has integral coefficients and the corresponding
divisor is Cartier. -/
@[mmp "def_km0_q_cartier"]
def IsCartierDivisor (D : QDivisor X) : Prop :=
  ∃ D' : Divisor X, Divisor.toQDivisor D' = D ∧ D'.IsCartier

/-- The `ℚ`-divisor of a divisor `D` is a Cartier divisor if and only if `D` is Cartier. -/
theorem isCartierDivisor_toQDivisor {D : Divisor X} :
    (Divisor.toQDivisor D).IsCartierDivisor ↔ D.IsCartier := by
  refine ⟨fun ⟨D', hD', h⟩ => ?_, fun h => ⟨D, rfl, h⟩⟩
  rwa [← Divisor.toQDivisor_injective hD']

/-- If the `ℚ`-divisor `D` is a Cartier divisor, then so is `-D`. -/
theorem IsCartierDivisor.neg {D : QDivisor X} (h : D.IsCartierDivisor) :
    (-D).IsCartierDivisor := by
  obtain ⟨D', hD', h⟩ := h
  exact ⟨-D', by rw [map_neg, hD'], h.neg⟩

/-- A `ℚ`-divisor `D` on a normal scheme is *`ℚ`-Cartier* if there is a nonzero integer `m` such
that `mD` is a divisor (has integral coefficients) and is Cartier. -/
@[mmp "def_km0_q_cartier"]
def IsQCartier (D : QDivisor X) : Prop :=
  ∃ m : ℤ, m ≠ 0 ∧ (m • D).IsCartierDivisor

/-- A `ℚ`-Cartier `ℚ`-divisor has a positive integral multiple that is a Cartier divisor. -/
theorem IsQCartier.exists_pos {D : QDivisor X} (h : D.IsQCartier) :
    ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartierDivisor := by
  obtain ⟨m, hm, hD⟩ := h
  refine ⟨m.natAbs, Int.natAbs_pos.mpr hm, ?_⟩
  rcases Int.natAbs_eq m with h | h
  · rwa [← h]
  · rw [Int.natCast_natAbs, abs_of_neg (by omega : m < 0), neg_smul]
    exact hD.neg

/-- A `ℚ`-divisor `D` is `ℚ`-Cartier if and only if `mD` is a Cartier divisor for some positive
integer `m`. -/
theorem isQCartier_iff_exists_pos {D : QDivisor X} :
    D.IsQCartier ↔ ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartierDivisor :=
  ⟨IsQCartier.exists_pos, fun ⟨m, hm, h⟩ => ⟨m, by omega, h⟩⟩

/-- The `ℚ`-divisor of a Cartier divisor is `ℚ`-Cartier. -/
theorem isQCartier_toQDivisor {D : Divisor X} (h : D.IsCartier) :
    (Divisor.toQDivisor D).IsQCartier :=
  ⟨1, one_ne_zero, by rw [one_smul]; exact isCartierDivisor_toQDivisor.mpr h⟩

open Classical in
/-- The *Cartier index* `m_D` of a `ℚ`-Cartier `ℚ`-divisor `D`: the least positive integer `m`
such that `mD` is a divisor and is Cartier. -/
@[mmp "def_km0_cartier_index"]
def cartierIndex (D : QDivisor X) (h : D.IsQCartier) : ℕ :=
  Nat.find h.exists_pos

/-- The Cartier index `m_D` is positive. -/
theorem cartierIndex_pos {D : QDivisor X} (h : D.IsQCartier) : 0 < D.cartierIndex h := by
  classical
  exact (Nat.find_spec h.exists_pos).1

/-- `m_D D` is a Cartier divisor, where `m_D` is the Cartier index of `D`. -/
theorem isCartierDivisor_cartierIndex_smul {D : QDivisor X} (h : D.IsQCartier) :
    (((D.cartierIndex h : ℕ) : ℤ) • D).IsCartierDivisor := by
  classical
  exact (Nat.find_spec h.exists_pos).2

/-- The Cartier index `m_D` is at most every positive integer `m` such that `mD` is a Cartier
divisor. -/
theorem cartierIndex_le {D : QDivisor X} (h : D.IsQCartier) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • D).IsCartierDivisor) : D.cartierIndex h ≤ m := by
  classical
  exact Nat.find_min' h.exists_pos ⟨hm, hmD⟩

end QDivisor

end Cartier

/-! ### Multiplicity of a prime divisor along an irreducible closed subset -/

/-- The *multiplicity* `mult_Z D` of a prime divisor `D` along an irreducible closed subset `Z`:
the largest `s ≥ 0` with `I_{D,η_Z} ⊆ 𝔪_Z^s`, where `I_{D,η_Z} ⊆ 𝒪_{X,Z}` is the ideal of `D`
at the generic point `η_Z` of `Z` and `𝔪_Z` is the maximal ideal of `𝒪_{X,Z}`. When `D` has a
local equation `g` at `η_Z`, so that `I_{D,η_Z} = (g)`, this is the largest `s` with
`g ∈ 𝔪_Z^s` (`MMP.Mori.PrimeDivisor.multiplicityAlong_eq_of_stalkIdeal_eq_span`). -/
@[mmp "def_km2b_multiplicity_along"]
def PrimeDivisor.multiplicityAlong (D : PrimeDivisor X) (Z : IrreducibleCloseds X) : ℕ∞ :=
  ⨆ (s : ℕ) (_ : D.idealSheaf.stalkIdeal Z.isIrreducible.genericPoint ≤
    IsLocalRing.maximalIdeal (X.presheaf.stalk Z.isIrreducible.genericPoint) ^ s), (s : ℕ∞)

/-- If `g` generates the ideal of `D` at the generic point of `Z`, the multiplicity of `D` along
`Z` is the largest `s` with `g ∈ 𝔪_Z^s`. -/
theorem PrimeDivisor.multiplicityAlong_eq_of_stalkIdeal_eq_span (D : PrimeDivisor X)
    (Z : IrreducibleCloseds X) {g : X.presheaf.stalk Z.isIrreducible.genericPoint}
    (hg : D.idealSheaf.stalkIdeal Z.isIrreducible.genericPoint = Ideal.span {g}) :
    D.multiplicityAlong Z = ⨆ (s : ℕ) (_ : g ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk Z.isIrreducible.genericPoint) ^ s), (s : ℕ∞) := by
  simp only [multiplicityAlong, hg, Ideal.span_singleton_le_iff_mem]

end MMP.Mori
