module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Principal
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.Topology.Noetherian.IrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Local

/-!
# The divisorial sheaf `𝒪_X(D)`

Let `X` be a locally Noetherian normal scheme and `D = ∑ d_E E` a divisor on `X`. The
*divisorial sheaf* `𝒪_X(D)` is the subsheaf of the sheaf of rational functions `𝒦_X` whose
sections over an open `U` are the `φ ∈ 𝒦_X(U) = ∏_{η_Z ∈ U} 𝒪_{X,η_Z}` such that, on every
irreducible component `Z` of `X` meeting `U`, the component `φ_Z ∈ K(Z)` is zero or satisfies
`v_E(φ_Z) + d_E ≥ 0` for every prime divisor `E ⊆ Z` meeting `U`. In particular
`𝒪_X(D)(∅) = 0`, and for integral `X` the sections over a nonempty `U` are
`{0} ∪ {φ ∈ K(X)^× : v_E(φ) + d_E ≥ 0 for every E meeting U}`.

The sections form a `Γ(X, U)`-submodule of `𝒦_X(U)`, compatibly with restriction, so `𝒪_X(D)` is
an `𝒪_X`-module. It is functorial in `D` for the order, linearly equivalent divisors have
isomorphic divisorial sheaves, `𝒪_X(0) ≅ 𝒪_X` by algebraic Hartogs, and on a Noetherian normal
scheme the divisorial sheaf of a Cartier divisor is invertible.

## Main definitions

* `MMP.Mori.PrimeDivisor.OrdGE`: `v_E(f) ≥ n` for an element `f` of the factor of `K(X)` on the
  component of `E`, zero allowed.
* `MMP.Mori.Divisor.IsDivisorialSection`, `MMP.Mori.Divisor.divisorialSubmodule`: the sections of
  `𝒪_X(D)` over `U`, as a predicate and as a `Γ(X, U)`-submodule of `𝒦_X(U)`.
* `MMP.Mori.Divisor.divisorialSheaf`: the divisorial sheaf `𝒪_X(D)`, an object of `X.Modules`.
* `MMP.Mori.Divisor.divisorialSheafInclusion`: `𝒪_X(D) ⟶ 𝒪_X(D')` for `D ≤ D'`.
* `MMP.Mori.Divisor.divisorialSheafMulIso`: multiplication by a unit `ψ` of `K(X)`,
  `𝒪_X(D) ≅ 𝒪_X(D')` when `D = D' + div ψ`.
* `MMP.Mori.Divisor.structureSheafToDivisorialSheaf`: `𝒪_X ⟶ 𝒪_X(D)` for effective `D`.
* `MMP.Mori.Divisor.divisorialSheafZeroIso`: `𝒪_X(0) ≅ 𝒪_X`.

## Main results

* `MMP.Mori.Divisor.isSheaf_divisorialPresheafAb`: the sections of `𝒪_X(D)` form a sheaf.
* `MMP.Mori.Divisor.LinearlyEquivalent.divisorialSheafIso`: `D₁ ∼ D₂` gives
  `𝒪_X(D₁) ≅ 𝒪_X(D₂)`.
* `MMP.Mori.toRationalFunctionsPresheaf_app_injective`: on a normal scheme `𝒪_X(U) → 𝒦_X(U)` is
  injective.
* `MMP.Mori.Divisor.IsDivisorialSection.exists_eq`: algebraic Hartogs, every section of
  `𝒪_X(0)` over `U` is a regular function on `U`.
* `MMP.Mori.Divisor.IsCartier.isInvertibleModule_divisorialSheaf`,
  `MMP.Mori.Divisor.IsCartier.isLocallyTrivial_divisorialSheaf`: for a Cartier divisor `D` on a
  Noetherian normal scheme, `𝒪_X(D)` is invertible, that is, locally isomorphic to `𝒪_X`.

## Implementation notes

The condition defining a section is stated prime divisor by prime divisor: for each `E` meeting
`U`, the component `φ_{i(E)}` on the irreducible component containing `E` is zero or has
`v_E ≥ -d_E`. Since on a normal scheme each prime divisor lies on exactly one irreducible
component, this is the source's condition "`φ_Z = 0` or `v_E(φ_Z) + d_E ≥ 0` for all `E ⊆ Z`
meeting `U`" for each component `Z` meeting `U`. The order `v_E` is
`MMP.Mori.PrimeDivisor.valuation`, the normalized valuation of the discrete valuation ring
`𝒪_{X,E}`, valued in `ℤᵐ⁰`, so that `v_E(f) ≥ n` reads `exp n ≤ v_E(f)`.

Algebraic Hartogs is proved stalkwise: a height-one prime of `𝒪_{X,x}` is the center of a prime
divisor through `x` (`MMP.Mori.exists_primeDivisor_isLocalization`), so Stacks Tag 031T (2) applies
to the Noetherian normal domain `𝒪_{X,x}`; the local regular functions glue because `𝒪_X → 𝒦_X` is
injective and each point has a neighbourhood meeting a single irreducible component.

The invertibility of `𝒪_X(D)` for Cartier `D` assumes `X` quasi-compact, so that the principal
divisor of a local equation is defined. Invertibility is `Stacks.Ample.IsInvertibleModule`
(Stacks Tag 01CS), equivalently local triviality.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4
* [R. Hartshorne, *Algebraic geometry*][Har77], II.6
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Order

universe u

namespace MMP.Mori

variable {X : Scheme.{u}}

namespace PrimeDivisor

variable (E : PrimeDivisor X) [IsLocallyNoetherian X] [IsNormal X]

/-- The valuation `v_E` satisfies the ultrametric inequality
`min (v_E(f), v_E(g)) ≤ v_E(f + g)` for `f + g ≠ 0`. -/
theorem valuation_add {f g : X.presheaf.stalk (componentGenericPoint X E.component)}
    (h : f + g ≠ 0) : min (E.valuation f) (E.valuation g) ≤ E.valuation (f + g) := by
  let := E.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  have := E.isDiscreteValuationRing_localRing
  let e := IsLocalization.algEquiv (nonZeroDivisors E.localRing)
    (X.presheaf.stalk (componentGenericPoint X E.component)) (FractionRing E.localRing)
  change min (Ring.ordFrac E.localRing (e f)) (Ring.ordFrac E.localRing (e g)) ≤
    Ring.ordFrac E.localRing (e (f + g))
  rw [map_add]
  exact Ring.ordFrac_add _ _ (map_add e f g ▸ (map_ne_zero_iff e e.injective).mpr h)

/-- `v_E(-f) = v_E(f)`. -/
theorem valuation_neg (f : X.presheaf.stalk (componentGenericPoint X E.component)) :
    E.valuation (-f) = E.valuation f := by
  let := E.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  have := E.isDiscreteValuationRing_localRing
  let e := IsLocalization.algEquiv (nonZeroDivisors E.localRing)
    (X.presheaf.stalk (componentGenericPoint X E.component)) (FractionRing E.localRing)
  change Ring.ordFrac E.localRing (e (-f)) = Ring.ordFrac E.localRing (e f)
  rw [map_neg, Ring.ordFrac_eq_valuation_inv, Ring.ordFrac_eq_valuation_inv, Valuation.map_neg]

/-- A nonzero element of the local ring `𝒪_{X,E}` has `v_E ≥ 0` in `K(X)`. -/
theorem one_le_valuation_toComponent {a : E.localRing} (ha : a ≠ 0) :
    1 ≤ E.valuation (E.toComponent.hom a) := by
  let := E.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  have := E.isDiscreteValuationRing_localRing
  change 1 ≤ Ring.ordFrac E.localRing (IsLocalization.algEquiv (nonZeroDivisors E.localRing) _
    (FractionRing E.localRing) (algebraMap E.localRing _ a))
  rw [AlgEquiv.commutes]
  exact Ring.ordFrac_ge_one_of_ne_zero ha

/-- An element of the factor `𝒪_{X,η_{i(E)}}` of `K(X)` with `v_E ≥ 0` lies in the local ring
`𝒪_{X,E}`. -/
theorem exists_toComponent_eq_of_one_le_valuation
    {f : X.presheaf.stalk (componentGenericPoint X E.component)} (hf : 1 ≤ E.valuation f) :
    ∃ b : E.localRing, E.toComponent.hom b = f := by
  let := E.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  have := E.isDiscreteValuationRing_localRing
  let e := IsLocalization.algEquiv (nonZeroDivisors E.localRing)
    (X.presheaf.stalk (componentGenericPoint X E.component)) (FractionRing E.localRing)
  change 1 ≤ Ring.ordFrac E.localRing (e f) at hf
  by_cases hf0 : e f = 0
  · exact ⟨0, by rw [map_zero, (map_eq_zero_iff e e.injective).mp hf0]⟩
  rw [Ring.ordFrac_eq_valuation_inv, one_le_inv₀ (by
    rwa [zero_lt_iff, ne_eq, Valuation.zero_iff])] at hf
  have hall : ∀ v : IsDedekindDomain.HeightOneSpectrum E.localRing,
      v.valuation (FractionRing E.localRing) (e f) ≤ 1 := fun v => by
    have hv : v = IsDiscreteValuationRing.maximalIdeal E.localRing :=
      IsDedekindDomain.HeightOneSpectrum.ext
        (IsLocalRing.eq_maximalIdeal (v.isPrime.isMaximal v.ne_bot))
    rwa [hv]
  obtain ⟨b, hb⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one _ _ hall
  exact ⟨b, e.injective ((e.commutes b).trans hb)⟩

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- If the prime divisor `E` meets the open `U`, then its generic point lies in `U`. -/
theorem genericPoint_mem_of_nonempty {U : X.Opens} (h : (E.support ∩ U).Nonempty) :
    E.genericPoint ∈ U := by
  obtain ⟨x, hxE, hxU⟩ := h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
  exact (specializes_iff_mem_closure.mpr hxE).mem_open U.isOpen hxU

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- If the prime divisor `E` meets the open `U`, then the generic point of the irreducible
component containing `E` lies in `U`. -/
theorem componentGenericPoint_mem_of_nonempty {U : X.Opens} (h : (E.support ∩ U).Nonempty) :
    componentGenericPoint X E.component ∈ U :=
  E.specializes_genericPoint.mem_open U.isOpen (E.genericPoint_mem_of_nonempty h)

/-- `v_E(f) ≥ n`: the element `f` of the factor `𝒪_{X,η_{i(E)}}` of `K(X)` is zero, or has
order of vanishing at least `n` along `E`. -/
def OrdGE (n : ℤ) (f : X.presheaf.stalk (componentGenericPoint X E.component)) : Prop :=
  f = 0 ∨ WithZero.exp n ≤ E.valuation f

variable {E}

/-- `v_E(0) ≥ n` for every `n`. -/
@[simp]
theorem OrdGE.zero (n : ℤ) : E.OrdGE n 0 := Or.inl rfl

/-- If `v_E(f) ≥ n` and `v_E(g) ≥ n`, then `v_E(f + g) ≥ n`. -/
theorem OrdGE.add {n : ℤ} {f g : X.presheaf.stalk (componentGenericPoint X E.component)}
    (hf : E.OrdGE n f) (hg : E.OrdGE n g) : E.OrdGE n (f + g) := by
  by_cases hfg : f + g = 0
  · exact Or.inl hfg
  refine Or.inr ?_
  rcases hf with rfl | hf
  · rcases hg with rfl | hg
    · exact absurd (add_zero _) hfg
    · rwa [zero_add]
  rcases hg with rfl | hg
  · rwa [add_zero]
  exact (le_min hf hg).trans (E.valuation_add hfg)

/-- If `v_E(f) ≥ n`, then `v_E(-f) ≥ n`. -/
theorem OrdGE.neg {n : ℤ} {f : X.presheaf.stalk (componentGenericPoint X E.component)}
    (hf : E.OrdGE n f) : E.OrdGE n (-f) := by
  rcases hf with rfl | hf
  · exact Or.inl neg_zero
  · exact Or.inr (by rwa [E.valuation_neg])

/-- If `v_E(f) ≥ n` and `m ≤ n`, then `v_E(f) ≥ m`. -/
theorem OrdGE.mono {m n : ℤ} {f : X.presheaf.stalk (componentGenericPoint X E.component)}
    (hf : E.OrdGE n f) (hmn : m ≤ n) : E.OrdGE m f :=
  hf.imp_right ((WithZero.exp_le_exp.mpr hmn).trans)

/-- If `v_E(f) ≥ n`, then `v_E(a f) ≥ n` for every `a` in the local ring `𝒪_{X,E}`. -/
theorem OrdGE.toComponent_mul {n : ℤ} {f : X.presheaf.stalk (componentGenericPoint X E.component)}
    (hf : E.OrdGE n f) (a : E.localRing) : E.OrdGE n (E.toComponent.hom a * f) := by
  by_cases h : E.toComponent.hom a * f = 0
  · exact Or.inl h
  refine Or.inr ?_
  have ha : a ≠ 0 := by
    rintro rfl
    exact h (by rw [map_zero, zero_mul])
  have hf' : f ≠ 0 := by
    rintro rfl
    exact h (mul_zero _)
  rw [map_mul]
  exact (hf.resolve_left hf').trans (le_mul_of_one_le_left' (E.one_le_valuation_toComponent ha))

/-- If `v_E(f) ≥ m` and `v_E(g) ≥ n`, then `v_E(f g) ≥ m + n`. -/
theorem OrdGE.mul {m n : ℤ} {f g : X.presheaf.stalk (componentGenericPoint X E.component)}
    (hf : E.OrdGE m f) (hg : E.OrdGE n g) : E.OrdGE (m + n) (f * g) := by
  rcases hf with rfl | hf
  · exact Or.inl (zero_mul _)
  rcases hg with rfl | hg
  · exact Or.inl (mul_zero _)
  refine Or.inr ?_
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' hf hg

end PrimeDivisor

/-! ### `𝒦_X` as an `𝒪_X`-module -/

section Module

/-- `𝒦_X(U)` is a `Γ(X, U)`-algebra through `𝒪_X ⟶ 𝒦_X`; this makes `𝒦_X` an `𝒪_X`-module. -/
instance rationalFunctionsAlgebra (U : X.Opens) :
    Algebra Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) :=
  ((toRationalFunctionsPresheaf X).app (op U)).hom.toAlgebra

/-- The component of `r • φ` at `Z` is the germ of `r` at the generic point of `Z` times `φ_Z`. -/
theorem rationalFunctions_smul_apply {U : X.Opens} (r : Γ(X, U))
    (φ : ToType ((rationalFunctionsPresheaf X).obj (op U)))
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}) :
    (r • φ) Z = X.presheaf.germ U _ Z.2 r * φ Z := rfl

/-- Restriction in `𝒦_X` is semilinear: `(r • φ)|_V = r|_V • φ|_V`. -/
theorem rationalFunctionsPresheaf_map_smul {U V : X.Opens} (i : V ⟶ U) (r : Γ(X, U))
    (φ : ToType ((rationalFunctionsPresheaf X).obj (op U))) :
    (rationalFunctionsPresheaf X).map i.op (r • φ) =
      X.presheaf.map i.op r • (rationalFunctionsPresheaf X).map i.op φ := by
  funext Z
  simp only [rationalFunctions_smul_apply, rationalFunctionsPresheaf_map_apply]
  rw [TopCat.Presheaf.germ_res_apply]

/-- Every point lies on some irreducible component. -/
theorem exists_mem_irreducibleComponents {α : Type*} [TopologicalSpace α] (x : α) :
    ∃ Z : irreducibleComponents α, x ∈ Z.1 :=
  ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
    mem_irreducibleComponent⟩

/-- On a normal scheme, a section of `𝒪_X` over `U` is determined by its image in `𝒦_X(U)`: its
germs at the generic points of the irreducible components meeting `U`. -/
theorem toRationalFunctionsPresheaf_app_injective [IsNormal X] (U : X.Opens) :
    Function.Injective ((toRationalFunctionsPresheaf X).app (op U)) := by
  intro s t hst
  refine TopCat.Presheaf.section_ext X.sheaf U s t fun x hx => ?_
  obtain ⟨Z, hxZ⟩ := exists_mem_irreducibleComponents x
  have hZU : componentGenericPoint X Z ∈ U := (genericPoint_mem_iff Z U).mpr ⟨x, hx, hxZ⟩
  have h := congrFun hst ⟨Z, hZU⟩
  change X.presheaf.germ U _ hZU s = X.presheaf.germ U _ hZU t at h
  rw [← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hx
      ((isGenericPoint_componentGenericPoint X Z).specializes hxZ),
    ← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hx
      ((isGenericPoint_componentGenericPoint X Z).specializes hxZ)] at h
  exact stalkToRationalFunctions_injective hxZ h

/-- The component at `Z` of the image of `s ∈ Γ(X, U)` in `𝒦_X(U)` is the germ of `s` at the
generic point of `Z`. -/
theorem toRationalFunctionsPresheaf_app_apply {U : X.Opens} (s : Γ(X, U))
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}) :
    (toRationalFunctionsPresheaf X).app (op U) s Z = X.presheaf.germ U _ Z.2 s := rfl

/-- The map `𝒪_X(U) → 𝒦_X(U)` commutes with restriction along `V ⊆ U`. -/
theorem toRationalFunctionsPresheaf_app_map {U V : X.Opens} (i : V ⟶ U) (s : Γ(X, U)) :
    (toRationalFunctionsPresheaf X).app (op V) (X.presheaf.map i.op s) =
      (rationalFunctionsPresheaf X).map i.op ((toRationalFunctionsPresheaf X).app (op U) s) := by
  funext Z
  exact TopCat.Presheaf.germ_res_apply X.presheaf i _ Z.2 s

end Module

/-! ### Height-one primes of a local ring and prime divisors -/

section HeightOne

/-- A height-one prime `q` of the local ring `𝒪_{X,x}` of a locally Noetherian scheme is the
center of a prime divisor `E` through `x`: the generic point of `E` specializes to `x`, and
`𝒪_{X,E}` is the localization of `𝒪_{X,x}` at `q`. -/
theorem exists_primeDivisor_isLocalization {x : X} (q : PrimeSpectrum (X.presheaf.stalk x))
    (hq : q.asIdeal.height = 1) :
    ∃ (E : PrimeDivisor X) (h : E.genericPoint ⤳ x),
      letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
      IsLocalization.AtPrime (X.presheaf.stalk E.genericPoint) q.asIdeal := by
  have hyx : X.fromSpecStalk x q ⤳ x := Scheme.range_fromSpecStalk.le ⟨q, rfl⟩
  have hP : (IsLocalRing.maximalIdeal (X.presheaf.stalk (X.fromSpecStalk x q))).comap
      (X.presheaf.stalkSpecializes hyx).hom = q.asIdeal := by
    have h := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hyx
    have h1 := congrArg (fun f => f (IsLocalRing.closedPoint _)) h
    simp only [Scheme.fromSpecStalk_closedPoint] at h1
    exact congrArg PrimeSpectrum.asIdeal ((X.fromSpecStalk x).isEmbedding.injective h1)
  have hloc := Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes hyx
  let := (X.presheaf.stalkSpecializes hyx).hom.toAlgebra
  have hloc' : IsLocalization.AtPrime (X.presheaf.stalk (X.fromSpecStalk x q)) q.asIdeal := by
    convert hloc
    exact hP.symm
  have hcoh : coheight (X.fromSpecStalk x q) = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight (X.fromSpecStalk x q)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal, hq] at h1
    exact (WithBot.coe_injective h1).symm
  have key : ∀ w : X, w = X.fromSpecStalk x q → ∃ h : w ⤳ x,
      letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
      IsLocalization.AtPrime (X.presheaf.stalk w) q.asIdeal := by
    rintro w rfl
    exact ⟨hyx, hloc'⟩
  exact ⟨_, key _ (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh)⟩

end HeightOne

/-! ### Neighbourhoods meeting a single irreducible component -/

/-- On a locally Noetherian normal scheme, every point `x` on the irreducible component `Z` has
an open neighbourhood meeting no other irreducible component. -/
theorem exists_mem_opens_forall_irreducibleComponents_eq [IsLocallyNoetherian X] [IsNormal X]
    {x : X} {Z : irreducibleComponents X} (hxZ : x ∈ Z.1) :
    ∃ V : X.Opens, x ∈ V ∧ ∀ Z' : irreducibleComponents X, ((Z'.1 : Set X) ∩ V).Nonempty →
      Z' = Z := by
  classical
  have hlf := IsLocallyNoetherianSpace.locallyFinite_image_irreducibleComponents
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X) (f := id) Topology.IsClosedEmbedding.id
  simp only [Set.image_id] at hlf
  obtain ⟨t, ht, hfin⟩ := hlf x
  obtain ⟨V₀, hV₀t, hV₀open, hxV₀⟩ := mem_nhds_iff.mp ht
  set F : Set (irreducibleComponents X) :=
    {C | ((C : Set X) ∩ t).Nonempty ∧ x ∉ (C : Set X)} with hF
  have hFfin : F.Finite := hfin.subset fun C hC => hC.1
  refine ⟨⟨V₀ ∩ ⋂ C ∈ F, ((C : Set X))ᶜ, hV₀open.inter (hFfin.isOpen_biInter fun C _ =>
      (isClosed_of_mem_irreducibleComponents (C : Set X) C.2).isOpen_compl)⟩, ⟨hxV₀, ?_⟩, ?_⟩
  · exact Set.mem_iInter₂.mpr fun C hC => hC.2
  · rintro C ⟨z, hzC, hzV₀, hzI⟩
    refine eq_of_mem_irreducibleComponents (Classical.byContradiction fun hxC => ?_) hxZ
    simp only [Set.mem_iInter] at hzI
    exact hzI C ⟨⟨z, hzC, hV₀t hzV₀⟩, hxC⟩ hzC

/-! ### The divisorial sheaf -/

variable (X) in
/-- The structure sheaf `𝒪_X`, as an `𝒪_X`-module. -/
abbrev structureSheafModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

section Divisorial

variable [IsLocallyNoetherian X] [IsNormal X]

namespace Divisor

/-- A section `φ` of `𝒦_X` over `U` is a section of `𝒪_X(D)` when, for every prime divisor `E`
meeting `U`, the component `φ_{i(E)}` of `φ` on the irreducible component of `X` containing `E`
is zero or satisfies `v_E(φ_{i(E)}) + d_E ≥ 0`, where `d_E` is the coefficient of `E` in `D`. -/
@[mmp "def_km0_divisorial_sheaf"]
def IsDivisorialSection (D : Divisor X) (U : X.Opens)
    (φ : ToType ((rationalFunctionsPresheaf X).obj (op U))) : Prop :=
  ∀ (E : PrimeDivisor X) (h : (E.support ∩ U).Nonempty),
    E.OrdGE (-D.coeff E) (φ ⟨E.component, E.componentGenericPoint_mem_of_nonempty h⟩)

/-- The sections `𝒪_X(D)(U) ⊆ 𝒦_X(U)`, as a `Γ(X, U)`-submodule. -/
@[mmp "def_km0_divisorial_sheaf"]
def divisorialSubmodule (D : Divisor X) (U : X.Opens) :
    Submodule Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) where
  carrier := {φ | D.IsDivisorialSection U φ}
  zero_mem' := fun E _ => PrimeDivisor.OrdGE.zero _
  add_mem' := fun hφ hψ E h => (hφ E h).add (hψ E h)
  smul_mem' := fun r φ hφ E h => by
    have hE := E.genericPoint_mem_of_nonempty h
    rw [rationalFunctions_smul_apply, ← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hE
      E.specializes_genericPoint]
    exact (hφ E h).toComponent_mul _

/-- `φ ∈ 𝒪_X(D)(U)` if and only if `φ` is a section of `𝒪_X(D)` over `U`. -/
@[simp]
theorem mem_divisorialSubmodule {D : Divisor X} {U : X.Opens}
    {φ : ToType ((rationalFunctionsPresheaf X).obj (op U))} :
    φ ∈ D.divisorialSubmodule U ↔ D.IsDivisorialSection U φ := Iff.rfl

/-- The restriction to `V ⊆ U` of a section of `𝒪_X(D)` over `U` is a section over `V`. -/
theorem IsDivisorialSection.map {D : Divisor X} {U V : X.Opens} (i : V ⟶ U)
    {φ : ToType ((rationalFunctionsPresheaf X).obj (op U))} (hφ : D.IsDivisorialSection U φ) :
    D.IsDivisorialSection V ((rationalFunctionsPresheaf X).map i.op φ) := fun E h =>
  hφ E (h.mono (Set.inter_subset_inter_right _ i.le))

/-- The restriction `𝒪_X(D)(U) → 𝒪_X(D)(V)` along `V ⊆ U`, the restriction of `𝒦_X`. -/
def divisorialRestrict (D : Divisor X) {U V : X.Opens} (i : V ⟶ U) :
    D.divisorialSubmodule U →+ D.divisorialSubmodule V where
  toFun φ := ⟨(rationalFunctionsPresheaf X).map i.op φ.1, φ.2.map i⟩
  map_zero' := Subtype.ext (map_zero ((rationalFunctionsPresheaf X).map i.op).hom)
  map_add' φ ψ := Subtype.ext (map_add ((rationalFunctionsPresheaf X).map i.op).hom φ.1 ψ.1)

/-- The restriction in `𝒪_X(D)` is the restriction in `𝒦_X`. -/
@[simp]
theorem coe_divisorialRestrict (D : Divisor X) {U V : X.Opens} (i : V ⟶ U)
    (φ : D.divisorialSubmodule U) :
    (D.divisorialRestrict i φ : ToType ((rationalFunctionsPresheaf X).obj (op V))) =
      (rationalFunctionsPresheaf X).map i.op φ.1 := rfl

/-- `𝒪_X(D)` as a presheaf of abelian groups. -/
def divisorialPresheafAb (D : Divisor X) : TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of (D.divisorialSubmodule U.unop)
  map i := AddCommGrpCat.ofHom (D.divisorialRestrict i.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sections of `𝒪_X(D)` over `U` form a `Γ(X, U)`-module. -/
instance (D : Divisor X) (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (D.divisorialPresheafAb.obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (D.divisorialSubmodule U.unop))

/-- `𝒪_X(D)` as a presheaf of `𝒪_X`-modules. -/
def divisorialPresheafOfModules (D : Divisor X) : X.PresheafOfModules :=
  PresheafOfModules.ofPresheaf D.divisorialPresheafAb fun _ _ i r φ =>
    Subtype.ext (rationalFunctionsPresheaf_map_smul i.unop r φ.1)

/-- The presheaf of abelian groups `𝒪_X(D)` is a sheaf. -/
theorem isSheaf_divisorialPresheafAb (D : Divisor X) : D.divisorialPresheafAb.IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hmem : ∀ Z : irreducibleComponents X, componentGenericPoint X Z ∈ iSup U →
      ∃ i, componentGenericPoint X Z ∈ U i := fun Z h => Opens.mem_iSup.mp h
  have hagree : ∀ (i j : ι) (Z : irreducibleComponents X) (hi : componentGenericPoint X Z ∈ U i)
      (hj : componentGenericPoint X Z ∈ U j), (sf i).1 ⟨Z, hi⟩ = (sf j).1 ⟨Z, hj⟩ :=
    fun i j Z hi hj => congrFun (congrArg Subtype.val (hsf i j)) ⟨Z, ⟨hi, hj⟩⟩
  let s : ToType ((rationalFunctionsPresheaf X).obj (op (iSup U))) :=
    fun Z => (sf (hmem Z.1 Z.2).choose).1 ⟨Z.1, (hmem Z.1 Z.2).choose_spec⟩
  have hs : D.IsDivisorialSection (iSup U) s := by
    intro E h
    obtain ⟨x, hxE, hxU⟩ := h
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxU
    have hEj : (E.support ∩ U j).Nonempty := ⟨x, hxE, hj⟩
    have key := (sf j).2 E hEj
    rwa [← hagree _ j _ _ (E.componentGenericPoint_mem_of_nonempty hEj)] at key
  refine ⟨⟨s, hs⟩, fun i => Subtype.ext (funext fun Z => hagree _ _ _ _ _), fun t ht => ?_⟩
  refine Subtype.ext (funext fun Z => ?_)
  have := congrFun (congrArg Subtype.val (ht (hmem Z.1 Z.2).choose))
    ⟨Z.1, (hmem Z.1 Z.2).choose_spec⟩
  exact this.symm ▸ rfl

/-- The *divisorial sheaf* `𝒪_X(D)` of a divisor `D` on a locally Noetherian normal scheme `X`:
the sub-`𝒪_X`-module of the sheaf of rational functions `𝒦_X` whose sections over `U` are the
`φ ∈ 𝒦_X(U) = ∏_{η_Z ∈ U} 𝒪_{X,η_Z}` such that, on each irreducible component `Z` meeting `U`,
the component `φ_Z` is zero or satisfies `v_E(φ_Z) + d_E ≥ 0` for every prime divisor `E ⊆ Z`
meeting `U`. -/
@[mmp "def_km0_divisorial_sheaf"]
def divisorialSheaf (D : Divisor X) : X.Modules where
  val := D.divisorialPresheafOfModules
  isSheaf := D.isSheaf_divisorialPresheafAb

/-- The sections of `𝒪_X(D)` over `U` are the elements of `D.divisorialSubmodule U`. -/
theorem divisorialSheaf_sections (D : Divisor X) (U : X.Opens) :
    (Γ(D.divisorialSheaf, U) : Type u) = D.divisorialSubmodule U := rfl

variable {D D' D'' : Divisor X}

/-- A morphism `𝒪_X(D) ⟶ 𝒪_X(D')` given by `Γ(X, U)`-linear maps on sections commuting with
restriction. -/
def divisorialSheafHomMk
    (f : ∀ U : X.Opens, D.divisorialSubmodule U →ₗ[Γ(X, U)] D'.divisorialSubmodule U)
    (hf : ∀ (U V : X.Opens) (i : V ⟶ U) (φ : D.divisorialSubmodule U),
      f V (D.divisorialRestrict i φ) = D'.divisorialRestrict i (f U φ)) :
    D.divisorialSheaf ⟶ D'.divisorialSheaf :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (f U.unop).toAddMonoidHom
      naturality U V i := by
        ext φ
        exact hf U.unop V.unop i.unop φ }
    fun U r φ => (f U.unop).map_smul r φ⟩

/-- On sections over `U`, `divisorialSheafHomMk f hf` is `f U`. -/
@[simp]
theorem divisorialSheafHomMk_app
    (f : ∀ U : X.Opens, D.divisorialSubmodule U →ₗ[Γ(X, U)] D'.divisorialSubmodule U) (hf)
    (U : X.Opens) (φ : D.divisorialSubmodule U) :
    (divisorialSheafHomMk f hf).app U φ = f U φ := rfl

/-- Two morphisms `𝒪_X(D) ⟶ 𝒪_X(D')` are equal if they agree, as sections of `𝒦_X`, on every
section of `𝒪_X(D)`. -/
theorem divisorialSheaf_hom_ext {f g : D.divisorialSheaf ⟶ D'.divisorialSheaf}
    (h : ∀ (U : X.Opens) (φ : D.divisorialSubmodule U), (f.app U φ).1 = (g.app U φ).1) :
    f = g :=
  Scheme.Modules.hom_ext f g fun U => by
    ext φ
    exact Subtype.ext (h U φ)

/-! #### Inclusions -/

/-- For `D ≤ D'`, a section of `𝒪_X(D)` over `U` is a section of `𝒪_X(D')` over `U`. -/
theorem IsDivisorialSection.mono {U : X.Opens}
    {φ : ToType ((rationalFunctionsPresheaf X).obj (op U))} (hφ : D.IsDivisorialSection U φ)
    (h : D ≤ D') : D'.IsDivisorialSection U φ := fun E hE =>
  (hφ E hE).mono (neg_le_neg (h E))

/-- For `D ≤ D'`, `𝒪_X(D)(U) ⊆ 𝒪_X(D')(U)` as submodules of `𝒦_X(U)`. -/
theorem divisorialSubmodule_mono (h : D ≤ D') (U : X.Opens) :
    D.divisorialSubmodule U ≤ D'.divisorialSubmodule U := fun _ hφ => hφ.mono h

/-- For `D ≤ D'`, the inclusion `𝒪_X(D) ⟶ 𝒪_X(D')` of subsheaves of `𝒦_X`. -/
def divisorialSheafInclusion (h : D ≤ D') : D.divisorialSheaf ⟶ D'.divisorialSheaf :=
  divisorialSheafHomMk (fun U => Submodule.inclusion (divisorialSubmodule_mono h U))
    fun _ _ _ _ => rfl

/-- The inclusion `𝒪_X(D) ⟶ 𝒪_X(D')` is the identity on underlying sections of `𝒦_X`. -/
@[simp]
theorem coe_divisorialSheafInclusion_app (h : D ≤ D') (U : X.Opens)
    (φ : D.divisorialSubmodule U) :
    ((divisorialSheafInclusion h).app U φ).1 = φ.1 := rfl

/-- The inclusion `𝒪_X(D) ⟶ 𝒪_X(D)` is the identity. -/
@[simp]
theorem divisorialSheafInclusion_refl :
    divisorialSheafInclusion (le_refl D) = 𝟙 D.divisorialSheaf :=
  divisorialSheaf_hom_ext fun _ _ => rfl

/-- For `D ≤ D' ≤ D''`, the inclusions `𝒪_X(D) ⟶ 𝒪_X(D') ⟶ 𝒪_X(D'')` compose to the inclusion
`𝒪_X(D) ⟶ 𝒪_X(D'')`. -/
@[simp, reassoc]
theorem divisorialSheafInclusion_comp (h : D ≤ D') (h' : D' ≤ D'') :
    divisorialSheafInclusion h ≫ divisorialSheafInclusion h' =
      divisorialSheafInclusion (h.trans h') :=
  divisorialSheaf_hom_ext fun _ _ => rfl

/-- For `D ≤ D'`, the inclusion `𝒪_X(D) ⟶ 𝒪_X(D')` is a monomorphism. -/
instance (h : D ≤ D') : Mono (divisorialSheafInclusion h) := by
  refine ⟨fun g₁ g₂ hg => Scheme.Modules.hom_ext _ _ fun U => ?_⟩
  ext φ
  exact Subtype.ext (congrArg (fun f => (f.app U φ).1) hg)

/-! #### Multiplication by a rational function -/

/-- Multiplication by a unit `ψ` of `K(X)` maps `𝒪_X(D)(U)` to `𝒪_X(D')(U)` when
`D = D' + div(ψ)`, coefficientwise. -/
def divisorialMulLinearMap (ψ : (RationalFunctions X)ˣ)
    (h : ∀ E : PrimeDivisor X, D.coeff E = D'.coeff E + E.ord ψ) (U : X.Opens) :
    D.divisorialSubmodule U →ₗ[Γ(X, U)] D'.divisorialSubmodule U where
  toFun φ := ⟨fun Z => (ψ : RationalFunctions X) Z.1 * φ.1 Z, fun E hE => by
    have hψ : E.OrdGE (E.ord ψ) ((ψ : RationalFunctions X) E.component) :=
      Or.inr (E.valuation_component ψ).ge
    refine (hψ.mul (φ.2 E hE)).mono (le_of_eq ?_)
    rw [h E]
    ring⟩
  map_add' φ φ' := Subtype.ext (funext fun Z => mul_add _ _ _)
  map_smul' r φ := Subtype.ext (funext fun Z => mul_left_comm _ _ _)

/-- The component at `Z` of `ψ φ` is `ψ_Z φ_Z`. -/
@[simp]
theorem coe_divisorialMulLinearMap_apply (ψ : (RationalFunctions X)ˣ)
    (h : ∀ E : PrimeDivisor X, D.coeff E = D'.coeff E + E.ord ψ) (U : X.Opens)
    (φ : D.divisorialSubmodule U) (Z) :
    (divisorialMulLinearMap ψ h U φ).1 Z = (ψ : RationalFunctions X) Z.1 * φ.1 Z := rfl

/-- Multiplication by a unit `ψ` of `K(X)`, a morphism `𝒪_X(D) ⟶ 𝒪_X(D')` when
`D = D' + div(ψ)` coefficientwise. -/
def divisorialSheafMul (ψ : (RationalFunctions X)ˣ)
    (h : ∀ E : PrimeDivisor X, D.coeff E = D'.coeff E + E.ord ψ) :
    D.divisorialSheaf ⟶ D'.divisorialSheaf :=
  divisorialSheafHomMk (divisorialMulLinearMap ψ h) fun _ _ _ _ => rfl

/-- Multiplication by a unit `ψ` of `K(X)` is an isomorphism `𝒪_X(D) ≅ 𝒪_X(D')` when
`D = D' + div(ψ)` coefficientwise, with inverse the multiplication by `ψ⁻¹`. -/
def divisorialSheafMulIso (ψ : (RationalFunctions X)ˣ)
    (h : ∀ E : PrimeDivisor X, D.coeff E = D'.coeff E + E.ord ψ) :
    D.divisorialSheaf ≅ D'.divisorialSheaf where
  hom := divisorialSheafMul ψ h
  inv := divisorialSheafMul ψ⁻¹ fun E => by rw [h E, PrimeDivisor.ord_inv]; ring
  hom_inv_id := divisorialSheaf_hom_ext fun U φ => funext fun Z => by
    change (ψ⁻¹ : (RationalFunctions X)ˣ).1 Z.1 * ((ψ : RationalFunctions X) Z.1 * φ.1 Z) = φ.1 Z
    rw [← mul_assoc, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Pi.one_apply, one_mul]
  inv_hom_id := divisorialSheaf_hom_ext fun U φ => funext fun Z => by
    change (ψ : RationalFunctions X) Z.1 * ((ψ⁻¹ : (RationalFunctions X)ˣ).1 Z.1 * φ.1 Z) = φ.1 Z
    rw [← mul_assoc, ← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Pi.one_apply, one_mul]

/-- Linearly equivalent divisors have isomorphic divisorial sheaves: if `D₁ - D₂ = div(ψ)`, then
multiplication by `ψ` is an isomorphism `𝒪_X(D₁) ≅ 𝒪_X(D₂)`. -/
def LinearlyEquivalent.divisorialSheafIso [CompactSpace X] {D₁ D₂ : Divisor X}
    (h : D₁.LinearlyEquivalent D₂) : D₁.divisorialSheaf ≅ D₂.divisorialSheaf :=
  divisorialSheafMulIso h.choose fun E => by
    have := congrArg (DivisorWithCoeffs.coeff · E) h.choose_spec
    simp only [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor] at this
    rw [← this]
    ring

/-- If `D₁ ∼ D₂`, then `𝒪_X(D₁)` and `𝒪_X(D₂)` are isomorphic. -/
theorem LinearlyEquivalent.nonempty_divisorialSheaf_iso [CompactSpace X] {D₁ D₂ : Divisor X}
    (h : D₁.LinearlyEquivalent D₂) : Nonempty (D₁.divisorialSheaf ≅ D₂.divisorialSheaf) :=
  ⟨h.divisorialSheafIso⟩

/-! #### The structure sheaf -/

/-- For an effective divisor `D`, the constant `1` is a section of `𝒪_X(D)` over every `U`. -/
theorem IsDivisorialSection.one (hD : 0 ≤ D) (U : X.Opens) :
    D.IsDivisorialSection U 1 := fun E _ =>
  Or.inr (by
    change WithZero.exp _ ≤ E.valuation 1
    rw [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]
    exact neg_nonpos.mpr (hD E))

/-- For an effective divisor `D`, the image in `𝒦_X(U)` of a regular function on `U` is a
section of `𝒪_X(D)` over `U`. -/
theorem isDivisorialSection_algebraMap (hD : 0 ≤ D) {U : X.Opens} (r : Γ(X, U)) :
    D.IsDivisorialSection U (algebraMap Γ(X, U) _ r) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (D.divisorialSubmodule U).smul_mem r (IsDivisorialSection.one hD U)

/-- For an effective divisor `D`, the section `1` of `𝒪_X(D)`. -/
def divisorialSheafOneSection (hD : 0 ≤ D) : D.divisorialSheaf.sections :=
  PresheafOfModules.sectionsMk (M := D.divisorialSheaf.val)
    (fun U => (⟨1, IsDivisorialSection.one hD U.unop⟩ : D.divisorialSubmodule U.unop))
    fun _ _ i => Subtype.ext (map_one ((rationalFunctionsPresheaf X).map i).hom)

/-- For an effective divisor `D`, the inclusion `𝒪_X ⟶ 𝒪_X(D)`, sending a regular function to its
image in `𝒦_X`. -/
def structureSheafToDivisorialSheaf (hD : 0 ≤ D) :
    structureSheafModule X ⟶ D.divisorialSheaf :=
  (SheafOfModules.unitHomEquiv _).symm (divisorialSheafOneSection hD)

/-- The map `𝒪_X ⟶ 𝒪_X(D)` sends a regular function on `U` to its image in `𝒦_X(U)`. -/
@[simp]
theorem coe_structureSheafToDivisorialSheaf_app (hD : 0 ≤ D) (U : X.Opens) (r : Γ(X, U)) :
    ((structureSheafToDivisorialSheaf hD).app U r).1 =
      (toRationalFunctionsPresheaf X).app (op U) r :=
  funext fun _ => mul_one _

/-! #### Algebraic Hartogs -/

/-- **Algebraic Hartogs, stalkwise.** If `φ` is a section of `𝒪_X(0)` over `U`, then at every
point `x ∈ U` on the irreducible component `Z` the component `φ_Z` is the image of an element of
the local ring `𝒪_{X,x}` (Stacks Tag 031T (2)). -/
theorem IsDivisorialSection.exists_stalk_eq {U : X.Opens}
    {φ : ToType ((rationalFunctionsPresheaf X).obj (op U))}
    (hφ : (0 : Divisor X).IsDivisorialSection U φ) {x : X} (hx : x ∈ U)
    {Z : irreducibleComponents X} (hxZ : x ∈ Z.1) :
    ∃ r : X.presheaf.stalk x, (stalkToRationalFunctions X hxZ).hom r =
      φ ⟨Z, (genericPoint_mem_iff Z U).mpr ⟨x, hx, hxZ⟩⟩ := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk (componentGenericPoint X Z)) :=
    (stalkToRationalFunctions X hxZ).hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions hxZ
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  let e := IsLocalization.algEquiv (nonZeroDivisors (X.presheaf.stalk x))
    (X.presheaf.stalk (componentGenericPoint X Z)) (FractionRing (X.presheaf.stalk x))
  set z := φ ⟨Z, (genericPoint_mem_iff Z U).mpr ⟨x, hx, hxZ⟩⟩ with hz
  suffices hloc : ∀ q : PrimeSpectrum (X.presheaf.stalk x), q.asIdeal.height = 1 →
      ∃ a s : X.presheaf.stalk x, s ∉ q.asIdeal ∧
        z * algebraMap _ (X.presheaf.stalk (componentGenericPoint X Z)) s =
          algebraMap _ (X.presheaf.stalk (componentGenericPoint X Z)) a by
    obtain ⟨r, hr⟩ :=
      Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
      (FractionRing (X.presheaf.stalk x)) (z := e z) fun q hq => by
        obtain ⟨a, s, hs, h⟩ := hloc q hq
        refine ⟨a, s, hs, ?_⟩
        rw [← e.commutes, ← e.commutes, ← map_mul, h]
    exact ⟨r, e.injective ((e.commutes r).trans hr)⟩
  intro q hq
  obtain ⟨E, h, hE⟩ := exists_primeDivisor_isLocalization q hq
  have hxE : x ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp h
  have hEU : (E.support ∩ U).Nonempty := ⟨x, hxE, hx⟩
  have hZ : Z = E.component :=
    eq_of_mem_irreducibleComponents hxZ (E.support_subset_component hxE)
  subst hZ
  have hcomp : ∀ t : X.presheaf.stalk x, E.toComponent.hom ((X.presheaf.stalkSpecializes h).hom t)
      = algebraMap _ (X.presheaf.stalk (componentGenericPoint X E.component)) t := fun t => by
    change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes
        ((isGenericPoint_componentGenericPoint X E.component).specializes
          E.genericPoint_mem_component)).hom t =
      (X.presheaf.stalkSpecializes
        ((isGenericPoint_componentGenericPoint X E.component).specializes hxZ)).hom t
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  rcases hφ E hEU with h0 | hv
  · refine ⟨0, 1, fun h1 => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), ?_⟩
    rw [map_zero, hz, h0, zero_mul]
  · rw [DivisorWithCoeffs.coeff_zero, neg_zero, WithZero.exp_zero] at hv
    obtain ⟨b, hb⟩ := E.exists_toComponent_eq_of_one_le_valuation hv
    let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl b
    refine ⟨a, s, s.2, ?_⟩
    have hspec := IsLocalization.mk'_spec (X.presheaf.stalk E.genericPoint) a s
    have := congrArg E.toComponent.hom hspec
    rw [map_mul, hb] at this
    rw [hz, ← hcomp, ← hcomp]
    exact this

/-- **Algebraic Hartogs.** On a locally Noetherian normal scheme, every section of `𝒪_X(0)` over
`U` is the image of a regular function on `U`. -/
theorem IsDivisorialSection.exists_eq {U : X.Opens}
    {φ : ToType ((rationalFunctionsPresheaf X).obj (op U))}
    (hφ : (0 : Divisor X).IsDivisorialSection U φ) :
    ∃ s : Γ(X, U), (toRationalFunctionsPresheaf X).app (op U) s = φ := by
  have hloc : ∀ x : U, ∃ (W : X.Opens) (_ : (x : X) ∈ W) (iWU : W ⟶ U) (t : Γ(X, W)),
      (toRationalFunctionsPresheaf X).app (op W) t =
        (rationalFunctionsPresheaf X).map iWU.op φ := by
    intro x
    obtain ⟨Z, hxZ⟩ := exists_mem_irreducibleComponents (x : X)
    obtain ⟨r, hr⟩ := hφ.exists_stalk_eq x.2 hxZ
    obtain ⟨V, hxV, hV⟩ := exists_mem_opens_forall_irreducibleComponents_eq hxZ
    obtain ⟨W₀, hxW₀, t₀, ht₀⟩ := X.presheaf.exists_germ_eq r
    refine ⟨W₀ ⊓ V ⊓ U, ⟨⟨hxW₀, hxV⟩, x.2⟩, homOfLE inf_le_right,
      X.presheaf.map (homOfLE (inf_le_left.trans inf_le_left)).op t₀, ?_⟩
    funext ⟨Z', hZ'⟩
    have hZ'Z : Z' = Z := hV Z' ⟨_, (isGenericPoint_componentGenericPoint X Z').mem, hZ'.1.2⟩
    subst hZ'Z
    rw [toRationalFunctionsPresheaf_app_apply, rationalFunctionsPresheaf_map_apply,
      TopCat.Presheaf.germ_res_apply, ← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf
      hxW₀ ((isGenericPoint_componentGenericPoint X Z').specializes hxZ), ht₀]
    exact hr
  choose W hxW iWU t ht using hloc
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 W t := by
    intro i j
    apply toRationalFunctionsPresheaf_app_injective
    refine (toRationalFunctionsPresheaf_app_map (Opens.infLELeft (W i) (W j)) (t i)).trans ?_
    refine Eq.trans ?_
      (toRationalFunctionsPresheaf_app_map (Opens.infLERight (W i) (W j)) (t j)).symm
    rw [ht i, ht j]
    rfl
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W U iWU
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩) t hcompat
  refine ⟨s, funext fun ⟨Z, hZ⟩ => ?_⟩
  exact congrArg (· ⟨Z, hxW ⟨_, hZ⟩⟩)
    ((toRationalFunctionsPresheaf_app_map (iWU ⟨_, hZ⟩) s).symm.trans
      ((congrArg _ (hs ⟨_, hZ⟩)).trans (ht ⟨_, hZ⟩)))

/-- On a locally Noetherian normal scheme, the map `𝒪_X ⟶ 𝒪_X(0)` is an isomorphism. -/
instance isIso_structureSheafToDivisorialSheaf_zero :
    IsIso (structureSheafToDivisorialSheaf (le_refl (0 : Divisor X))) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun r r' h => ?_, fun φ => ?_⟩
  · apply toRationalFunctionsPresheaf_app_injective U
    have := congrArg Subtype.val h
    exact (coe_structureSheafToDivisorialSheaf_app _ U r).symm.trans
      (this.trans (coe_structureSheafToDivisorialSheaf_app _ U r'))
  · obtain ⟨s, hs⟩ := IsDivisorialSection.exists_eq φ.2
    exact ⟨s, Subtype.ext ((coe_structureSheafToDivisorialSheaf_app _ U s).trans hs)⟩

/-- `𝒪_X(0) ≅ 𝒪_X` on a locally Noetherian normal scheme. -/
def divisorialSheafZeroIso :
    (0 : Divisor X).divisorialSheaf ≅ structureSheafModule X :=
  (asIso (structureSheafToDivisorialSheaf (le_refl (0 : Divisor X)))).symm

/-! #### Restriction to an open subscheme -/

/-- If `D ≤ D'` agree at every prime divisor meeting `U`, the inclusion `𝒪_X(D) ⟶ 𝒪_X(D')` is
bijective on sections over `U`. -/
theorem isIso_divisorialSheafInclusion_app (h : D ≤ D') {U : X.Opens}
    (hU : ∀ E : PrimeDivisor X, (E.support ∩ U).Nonempty → D.coeff E = D'.coeff E) :
    IsIso ((divisorialSheafInclusion h).app U) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun φ ψ hφψ => ?_, fun φ => ?_⟩
  · have := congrArg Subtype.val hφψ
    exact Subtype.ext this
  refine ⟨⟨φ.1, fun E hE => ?_⟩, rfl⟩
  rw [hU E hE]
  exact φ.2 E hE

/-- If `D ≤ D'` agree at every prime divisor meeting `U`, the inclusion `𝒪_X(D) ⟶ 𝒪_X(D')`
restricts to an isomorphism `𝒪_X(D)|_U ≅ 𝒪_X(D')|_U`. -/
theorem isIso_restrict_divisorialSheafInclusion (h : D ≤ D') {U : X.Opens}
    (hU : ∀ E : PrimeDivisor X, (E.support ∩ U).Nonempty → D.coeff E = D'.coeff E) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (divisorialSheafInclusion h)) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  exact isIso_divisorialSheafInclusion_app h fun E hE =>
    hU E (hE.mono (Set.inter_subset_inter_right _ (U.ι.image_le_opensRange V |>.trans
      (by rw [Scheme.Opens.opensRange_ι]))))

/-- If `D₁` and `D₂` have the same coefficient at every prime divisor meeting `U`, then
`𝒪_X(D₁)|_U ≅ 𝒪_X(D₂)|_U`, through `𝒪_X(D₁ ⊓ D₂)|_U`. -/
def restrictDivisorialSheafIsoOfEqOn {D₁ D₂ : Divisor X} {U : X.Opens}
    (hU : ∀ E : PrimeDivisor X, (E.support ∩ U).Nonempty → D₁.coeff E = D₂.coeff E) :
    D₁.divisorialSheaf.restrict U.ι ≅ D₂.divisorialSheaf.restrict U.ι := by
  haveI := isIso_restrict_divisorialSheafInclusion (inf_le_left : D₁ ⊓ D₂ ≤ D₁) (U := U)
    fun E hE => by
      change D₁ E ⊓ D₂ E = D₁ E
      rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply, hU E hE, inf_idem]
  haveI := isIso_restrict_divisorialSheafInclusion (inf_le_right : D₁ ⊓ D₂ ≤ D₂) (U := U)
    fun E hE => by
      change D₁ E ⊓ D₂ E = D₂ E
      rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply, hU E hE, inf_idem]
  exact (asIso ((Scheme.Modules.restrictFunctor U.ι).map
      (divisorialSheafInclusion (inf_le_left : D₁ ⊓ D₂ ≤ D₁)))).symm ≪≫
    asIso ((Scheme.Modules.restrictFunctor U.ι).map
      (divisorialSheafInclusion (inf_le_right : D₁ ⊓ D₂ ≤ D₂)))

/-- If `ψ` is a local equation of `D` on `U`, then multiplication by `ψ` trivializes `𝒪_X(D)` on
`U`: `𝒪_X(D)|_U ≅ 𝒪_X(D - div ψ)|_U ≅ 𝒪_X(0)|_U ≅ 𝒪_U`. -/
def IsLocalEquation.restrictDivisorialSheafIso [CompactSpace X] {U : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation U ψ) :
    D.divisorialSheaf.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctor U.ι).mapIso
      (divisorialSheafMulIso ψ (D' := D - principalDivisor ψ) fun E => by
        rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, sub_add_cancel]) ≪≫
    restrictDivisorialSheafIsoOfEqOn (D₂ := 0) (fun E hE => by
      rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hψ E hE, sub_self,
        DivisorWithCoeffs.coeff_zero]) ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso divisorialSheafZeroIso ≪≫
    Scheme.Modules.restrictUnitIso U.ι

/-- **The divisorial sheaf of a Cartier divisor is invertible** (Hartshorne II.6.11 for normal
schemes): on a Noetherian normal scheme, if `D` is Cartier then `𝒪_X(D)` is an invertible
`𝒪_X`-module (see `IsLocalEquation.restrictDivisorialSheafIso` for the local trivializations). -/
theorem IsCartier.isInvertibleModule_divisorialSheaf [CompactSpace X] (hD : D.IsCartier) :
    Stacks.Ample.IsInvertibleModule X D.divisorialSheaf :=
  Stacks.AlgebraicGeometry.TwistMapsInvertible.isInvertibleModule_of_forall_exists_restrict_isoUnit
    _ fun x => by
      obtain ⟨U, hxU, ψ, hψ⟩ := hD x
      exact ⟨U, hxU, ⟨hψ.restrictDivisorialSheafIso⟩⟩

/-- On a Noetherian normal scheme, the divisorial sheaf of a Cartier divisor is locally
isomorphic to `𝒪_X`. -/
theorem IsCartier.isLocallyTrivial_divisorialSheaf [CompactSpace X] (hD : D.IsCartier) :
    Stacks.SheafOfModules.Invertible.IsLocallyTrivial D.divisorialSheaf :=
  (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isLocallyTrivial X _).mp
    hD.isInvertibleModule_divisorialSheaf

end Divisor

end Divisorial

end MMP.Mori
