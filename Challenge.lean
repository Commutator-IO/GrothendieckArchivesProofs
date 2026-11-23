module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import Mathlib.CategoryTheory.Abelian.Monomorphisms
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Order.Sum.Order
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

@[expose] public section

/-!
# Trusted statements

The statements that `lake comparator` (`comparator.json`) checks against `Solution`: each is
written with Mathlib alone and left unproved, and `Solution` proves the same statement, under the
same name, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`. One section per folder (and one for problem 3 of the Buffalo
lectures), each in its own namespace `Challenge.<folder>`.
-/

section BuffaloProblemThree

/-!
## Buffalo, problem 3: `2` is not presentable in `Setᵒᵖ`

The trusted statement of `Buffalo.ProblemThree.not_isPresentable`.
-/

open CategoryTheory Opposite

namespace Challenge.BuffaloProblemThree

/-- *In `Setᵒᵖ` the object `2` is not presentable.* -/
theorem not_isPresentable : ¬ IsPresentable.{0} (op Bool : Typeᵒᵖ) := by
  sorry

end Challenge.BuffaloProblemThree

end BuffaloProblemThree

section Folder1

/-!
## Folder 1, page 124: Corollaire 3 in finite dimension

Finding `1-mixed-schwarz-fredholm-coefficients`.

The trusted statement of `Grothendieck.Folder1.corollaire3`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Challenge.Folder1

/-- *For complex square matrices `A`, `B`: `|det(1 + A + B)|` is at most the half-sum, and its
square at most the product, of `det(1 + |A| + |B|)` and `det(1 + |A*| + |B*|)`.* -/
theorem corollaire3 {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    ‖det (1 + (A + B))‖ ≤
        ((det (1 + (CFC.abs A + CFC.abs B))).re + (det (1 + (CFC.abs Aᴴ + CFC.abs Bᴴ))).re) / 2 ∧
      ‖det (1 + (A + B))‖ ^ 2 ≤
        (det (1 + (CFC.abs A + CFC.abs B))).re * (det (1 + (CFC.abs Aᴴ + CFC.abs Bᴴ))).re := by
  sorry

end Challenge.Folder1

end Folder1

section Folder100

/-!
## Folder 100, page 38: points of dimension one avoiding countably many closed sets

Finding `100-baire-dimension-one-points`.

The trusted statement of `Grothendieck.Folder100.Baire.exists_coheight_eq_one`.
-/

open IsLocalRing

namespace Challenge.Folder100

/-- *Let `R` be a complete noetherian local domain which is not a field. Countably many proper
closed subsets of `Spec R` miss some point `x` with `dim closure {x} = 1`.* -/
theorem exists_coheight_eq_one {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsDomain R] (hR : ¬ IsField R) {ι : Type*} [Countable ι]
    (Z : ι → Set (PrimeSpectrum R)) (hZ : ∀ i, IsClosed (Z i)) (hZu : ∀ i, Z i ≠ Set.univ) :
    ∃ x : PrimeSpectrum R, Order.coheight x = 1 ∧ ∀ i, x ∉ Z i := by
  sorry

end Challenge.Folder100

end Folder100

section Folder101

/-!
## Folder 101, pages 10–15: local duality in dimensions one and two

Findings `101-sheaf-duality-dim-one` (page 11) and `101-sheaf-duality-dim-two-fails`
(pages 14–15).

The trusted statements of `Grothendieck.Folder101Ext.isAdicComplete_iff_ext_one` and
`Grothendieck.Folder101DimTwo.not_nonempty_linearEquiv_dual`.
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

end Folder101

section Folder104

/-!
## Folder 104, page 4: the globular complex

The trusted statement of `Grothendieck.Folder104.globulaire_complexe`.
-/

namespace Challenge.Folder104

/-- *For sources and targets `sₙ, tₙ : Fₙ → Fₙ₋₁` satisfying the globular identities
`sₙ₋₁ sₙ = sₙ₋₁ tₙ` and `tₙ₋₁ sₙ = tₙ₋₁ tₙ`, the maps `tₙ − sₙ : ℤ[Fₙ] → ℤ[Fₙ₋₁]` compose
to zero.* -/
theorem globulaire_complexe {F₂ F₁ F₀ : Type*} (s₂ t₂ : F₂ → F₁) (s₁ t₁ : F₁ → F₀)
    (hs : s₁ ∘ s₂ = s₁ ∘ t₂) (ht : t₁ ∘ s₂ = t₁ ∘ t₂) :
    (Finsupp.lmapDomain ℤ ℤ t₁ - Finsupp.lmapDomain ℤ ℤ s₁) ∘ₗ
      (Finsupp.lmapDomain ℤ ℤ t₂ - Finsupp.lmapDomain ℤ ℤ s₂) = 0 := by
  sorry

end Challenge.Folder104

end Folder104

section Folder113

/-!
## Folder 113, page 3: the Karoubi envelope as free completion under retracts

The trusted statement of `Grothendieck.Folder113.enveloppe_libre`.
-/

open CategoryTheory CategoryTheory.Idempotents

universe v u v' u'

namespace Challenge.Folder113

/-- *Restriction along `P → Kar P` is an equivalence `Fun(Kar P, D) ≌ Fun(P, D)` for every
idempotent complete category `D`.* -/
theorem enveloppe_libre (P : Type u) [Category.{v} P] (D : Type u') [Category.{v'} D]
    [IsIdempotentComplete D] :
    ((Functor.whiskeringLeft P (Karoubi P) D).obj (toKaroubi P)).IsEquivalence := by
  sorry

end Challenge.Folder113

end Folder113

section Folder125

/-!
## Folder 125: the chain of equivalences of feuillet 2, and the lemma of feuillet 3

The trusted statements of `Grothendieck.Folder125.etage1_iff_etage2` and
`Grothendieck.Folder125.lemme_III18`.
-/

namespace Challenge.Folder125

/-- *Feuillet 2, premier étage ⇔ deuxième étage. In a long exact sequence
`⋯ → L p → G p → C p → L (p+1) → ⋯`, the terms `C p` vanish for all `p ≥ m` if and only if
`L p → G p` is bijective for `p > m` and surjective for `p = m`.* -/
theorem etage1_iff_etage2 {L G C : ℕ → Type*} [∀ p, AddCommGroup (L p)] [∀ p, AddCommGroup (G p)]
    [∀ p, AddCommGroup (C p)]
    (a : ∀ p, L p →+ G p) (b : ∀ p, G p →+ C p) (δ : ∀ p, C p →+ L (p + 1))
    (exG : ∀ p, Function.Exact (a p) (b p))
    (exC : ∀ p, Function.Exact (b p) (δ p))
    (exL : ∀ p, Function.Exact (δ p) (a (p + 1))) (m : ℕ) :
    (∀ p, m ≤ p → ∀ c : C p, c = 0) ↔
      (∀ p, m < p → Function.Bijective (a p)) ∧ Function.Surjective (a m) := by
  sorry

/-- *Feuillet 3 (III-18), affine form. `R` noetherian, `B` a finite `R`-module, `u : Rⁿ → B` an
isomorphism on the germs at `𝔭`: then `u` is an isomorphism over a neighbourhood `D(f)`
of `𝔭`.* -/
theorem lemme_III18 {R : Type*} [CommRing R] [IsNoetherianRing R] {B : Type*} [AddCommGroup B]
    [Module R B] [Module.Finite R B] {n : ℕ} (u : (Fin n → R) →ₗ[R] B) (p : Ideal R) [p.IsPrime]
    (hu : Function.Bijective (LocalizedModule.map p.primeCompl u)) :
    ∃ f : R, f ∉ p ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers f) u) := by
  sorry

end Challenge.Folder125

end Folder125

section Folder126

/-!
## Folder 126, pages 17–23: the trusted statement

The statement of `Grothendieck.Folder126Glue.radicial_etale_factorisation`.

*Let `f : X ⟶ Y` be finite and universally open, and suppose every geometric fibre of `f` has
exactly `n` points. Then `f` factors as `X ⟶ E ⟶ Y` with `X ⟶ E` integral, universally injective
and surjective (a universal homeomorphism) and `E ⟶ Y` finite étale, and every `Y`-morphism from
`X` to an étale `Y`-scheme factors uniquely through `X ⟶ E`.*

The universal homeomorphism of the proof is a notion of AxiomMath/Stacks; here it is spelled
with Mathlib's integral, universally injective and surjective morphisms (Stacks 04DF).
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Challenge.Folder126

theorem radicial_etale_factorisation {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [UniversallyOpen f] (n : ℕ)
    (hn : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ Y),
      Nonempty ({q : Spec (.of K) ⟶ X // q ≫ f = p} ≃ Fin n)) :
    ∃ (E : Scheme.{u}) (g : X ⟶ E) (h : E ⟶ Y),
      IsIntegralHom g ∧ UniversallyInjective g ∧ Surjective g ∧ IsFinite h ∧ Etale h ∧
        g ≫ h = f ∧
      ∀ {E' : Scheme.{u}} (e : E' ⟶ Y), Etale e → ∀ v : X ⟶ E', v ≫ e = f →
        ∃! u : E ⟶ E', u ≫ e = h ∧ g ≫ u = v := by
  sorry

end Challenge.Folder126

end Folder126

section Folder128

/-!
## Folder 128, page 23: Lemme 2

The trusted statement of `Grothendieck.Folder128.Infinitesimal.lemme2`.
-/

namespace Challenge.Folder128

/-- *Let `C` be integral over `B` with finitely many maximal ideals, distinct maximal ideals of
`C` lying over distinct ideals of `B`, and every residue extension purely inseparable. Then
for every `u ∈ M_n(C)` there is `v ∈ M_n(B)` with `u + φ(v)` invertible.* (Without the
page's hypothesis (i).) -/
theorem lemme2 {B : Type*} {C : Type*} [CommRing B] [CommRing C] [Algebra B C]
    [Algebra.IsIntegral B C] [Finite (MaximalSpectrum C)]
    (hinj : ∀ 𝔫 𝔫' : MaximalSpectrum C,
      𝔫.asIdeal.comap (algebraMap B C) = 𝔫'.asIdeal.comap (algebraMap B C) → 𝔫 = 𝔫')
    (hrad : ∀ 𝔫 : MaximalSpectrum C,
      IsPurelyInseparable (B ⧸ 𝔫.asIdeal.comap (algebraMap B C)) (C ⧸ 𝔫.asIdeal))
    {n : Type*} [Fintype n] [DecidableEq n] (u : Matrix n n C) :
    ∃ v : Matrix n n B, IsUnit (u + v.map (algebraMap B C)) := by
  sorry

end Challenge.Folder128

end Folder128

section Folder13

/-!
## Folder 13, page 47: the Tate case of the « double niveau » question

The trusted statement of `Grothendieck.Folder13.tate`.
-/

open Complex

namespace Challenge.Folder13

/-- *« c'est une puissance de Tate, et ça marche ». For the Tate motive `ℚ(n)`, the rationals
lying in the de Rham line `(2πi)ⁿ ℚ̄` are all of `ℚ` when `n = 0` and only `0` otherwise.*
The transcendence of `π` (Lindemann, not in Mathlib) is a hypothesis. -/
theorem tate (hπ : Transcendental ℚ (Real.pi : ℂ)) (n : ℤ) :
    {q : ℚ | ∃ α : ℂ, IsAlgebraic ℚ α ∧ (q : ℂ) = (2 * Real.pi * I) ^ n * α} =
      if n = 0 then Set.univ else {0} := by
  sorry

end Challenge.Folder13

end Folder13

section Folder136

/-!
## Folder 136, pages 26–31: the binomial lemma behind the « ombres »

Théorème 1 of finding `136-shadow-full-faithfulness`.

The trusted statement of `Grothendieck.Folder136.binomial_shadow_existsUnique`.
-/

namespace Challenge.Folder136

/-- *If `c_{l,k} ξ_k = c_{l,k−i} ξ_{k+l}` for `k ≥ N`, `l ≥ 0`, with `c_{a,b} = binom(a+b, a)`,
there is a unique `ξ` with `ξ_k = binom(k, i) ξ` for every `k ≥ N`.* -/
theorem binomial_shadow_existsUnique {A : Type*} [AddCommGroup A] (ξ : ℕ → A) (N i : ℕ)
    (h : ∀ k l, N ≤ k → (k + l).choose l • ξ k = (k + l - i).choose l • ξ (k + l)) :
    ∃! x : A, ∀ k, N ≤ k → ξ k = k.choose i • x := by
  sorry

end Challenge.Folder136

end Folder136

section Folder145

/-!
## Folder 145, pages 34–35: the unit-exponent exercise

Finding `145-unit-exponent-exercise`.

The trusted statement of `Grothendieck.Folder145.dihedral_witness`.
-/

open DihedralGroup

namespace Challenge.Folder145

/-- *The dihedral witness: for `m` odd, `(sr 0 · sr 1)⁻¹ ^ m · sr 0 ^ m · sr 1 ^ m = 1` in
`DihedralGroup N` if and only if `m ≡ 1 (mod N)`.* -/
theorem dihedral_witness (N : ℕ) {m : ℕ} (hm : Odd m) :
    ((sr 0 * sr 1 : DihedralGroup N)⁻¹) ^ m * (sr 0) ^ m * (sr 1) ^ m = 1 ↔
      (m : ZMod N) = 1 := by
  sorry

end Challenge.Folder145

end Folder145

section Folder153

/-!
## Folder 153, page 7: the Pascal matrix and `k[[T]]⁺`

The trusted statements of `Grothendieck.Folder153.pascal_det` and
`Grothendieck.Folder153.geom_not_finite_coaddition`.
-/

namespace Challenge.Folder153

/-- *The Pascal matrix `(binom(p + q, p))_{p, q < N}` has determinant `1`.* -/
theorem pascal_det (k : Type*) [CommRing k] (N : ℕ) :
    (Matrix.of fun p q : Fin N => (((p : ℕ) + q).choose p : k)).det = 1 := by
  sorry

/-- *Page 7: `k[[T]]⁺` does not satisfy 3a). The coefficients of `F(X + Y)` for
`F = ∑_{m ≥ 1} T^m` are not those of a finite sum `∑ᵢ aᵢ(X) bᵢ(Y)`.* -/
theorem geom_not_finite_coaddition (k : Type*) [CommRing k] [Nontrivial k] (n : ℕ)
    (a b : Fin n → ℕ → k) :
    ¬ ∀ p q : ℕ, (if p = 0 ∧ q = 0 then 0 else ((p + q).choose p : k)) = ∑ i, a i p * b i q := by
  sorry

end Challenge.Folder153

end Folder153

section Folder16

/-!
## Folder 16: the algebraic inverse of Lefschetz, and the pseudo-inverse

Finding `16-algebraic-iso-suffices` (pages 47–48).

The trusted statements of `Grothendieck.Folder16.inverse_Lefschetz_algebrique` and
`Grothendieck.Folder16.pseudo_inverse_unique`.
-/

namespace Challenge.Folder16

/-- *Pages 47–48, « un isomorphisme algébrique quelconque ». With « algebraic » read as
membership in given sets of maps satisfying `D(X)`: if `u : W → V` is some algebraic
isomorphism and `v : V → W` is an algebraic isomorphism, then `v⁻¹` is algebraic.* -/
theorem inverse_Lefschetz_algebrique
    {K : Type*} {V : Type*} {W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    (F : Subfield K) (𝒜V : Subring (Module.End K V))
    (𝒜WV : Set (W →ₗ[K] V)) (𝒜VW : Set (V →ₗ[K] W))
    (hsmul : ∀ c ∈ F, ∀ g ∈ 𝒜V, c • g ∈ 𝒜V)
    (hD : ∀ g ∈ 𝒜V, ∀ j, g.charpoly.coeff j ∈ F)
    (hcomp₁ : ∀ g ∈ 𝒜V, ∀ h ∈ 𝒜WV, g ∘ₗ h ∈ 𝒜WV)
    (hcomp₂ : ∀ h ∈ 𝒜WV, ∀ k ∈ 𝒜VW, h ∘ₗ k ∈ 𝒜V)
    {u : W →ₗ[K] V} (hu : u ∈ 𝒜WV) (hub : Function.Bijective u)
    {v : V →ₗ[K] W} (hv : v ∈ 𝒜VW) (hvb : Function.Bijective v) :
    ∃ v' ∈ 𝒜WV, v' ∘ₗ v = LinearMap.id ∧ v ∘ₗ v' = LinearMap.id := by
  sorry

/-- *Pages 14–15, « unique quand il existe ». A pseudo-inverse `Λ` of `L` with `ΛLΛ = Λ` is
determined by the two idempotents `ΛL` and `LΛ`.* -/
theorem pseudo_inverse_unique {E : Type*} [Ring E] {L Λ Λ' : E} (h : Λ * L * Λ = Λ)
    (h' : Λ' * L * Λ' = Λ') (hl : Λ * L = Λ' * L) (hr : L * Λ = L * Λ') : Λ = Λ' := by
  sorry

end Challenge.Folder16

end Folder16

section Folder161_2

/-!
## Folder 161-2: monadicity and the Gabriel–Ulmer characterisation

The trusted statements of `Grothendieck.Folder161_2.monadicite` and
`Grothendieck.Folder161_2.caracterisation_gabriel_ulmer`.
-/

open CategoryTheory Limits

universe w v u u₁ u₂

-- `Folder126` imports `Mathlib.Combinatorics.Quiver.ReflQuiver` for its own statement; here the
-- arrows of a category go through `CategoryStruct.toQuiver`, as in `Solution`.
attribute [-instance] CategoryTheory.catToReflQuiver

namespace Challenge.Folder161_2

/-- *Page 33. « Un foncteur `U : A → B` admettant un adjoint à gauche `F` est monadique si `U`
est conservatif et si `A` a et `U` préserve les coégalisateurs des paires réflexives. »* -/
theorem monadicite {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
    {F : B ⥤ A} {U : A ⥤ B} (adj : F ⊣ U) [HasReflexiveCoequalizers A]
    [U.ReflectsIsomorphisms]
    (hU : ∀ ⦃X Y : A⦄ (f g : X ⟶ Y), IsReflexivePair f g → PreservesColimit (parallelPair f g) U) :
    (Monad.comparison adj).IsEquivalence := by
  sorry

/-- *Page 61, Corollaire. A cocomplete, locally small category is locally presentable if and
only if it has a small dense full subcategory made of presentable objects.* -/
theorem caracterisation_gabriel_ulmer
    (C : Type u) [Category.{v} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C] :
    IsLocallyPresentable.{w} C ↔
      ∃ P : ObjectProperty C, ObjectProperty.Small.{w} P ∧ P.ι.IsDense ∧
        ∀ X, P X → IsPresentable.{w} X := by
  sorry

end Challenge.Folder161_2

end Folder161_2

section Folder161_6

/-!
## Folder 161-6, pages 4–14: the golden number

The trusted statement of `Grothendieck.Folder161_6.cos_two_pi_div_five`.
-/

open Real

namespace Challenge.Folder161_6

/-- *`cos(2π/5) = (√5 − 1)/4`, so that `η = 2 cos(2π/5)` satisfies `η² + η − 1 = 0`.* -/
theorem cos_two_pi_div_five : cos (2 * π / 5) = (√5 - 1) / 4 := by
  sorry

end Challenge.Folder161_6

end Folder161_6

section Folder19

/-!
## Folder 19, pages 4, 14–15 and 80: the trusted statements

The statements of `Grothendieck.Folder19.proposition_page80`, `Grothendieck.Folder19.beck_iff`
and `Grothendieck.Folder19.gabriel_popescu`.

`Mathlib.CategoryTheory.Abelian.Monomorphisms` is imported although no statement needs it: it and
`Mathlib.CategoryTheory.Abelian.CommSq` (imported through Gabriel–Popescu) both declare
`CategoryTheory.Abelian.instIsStableUnderCobaseChangeMonomorphisms`, the Solution's environment
has both, and `lake comparator` rejects the constant unless the Challenge's has both too.

*Page 80. For every `n`, there are `n` functors between presheaf topoi on a small category — here
the poset `ℤ ⊕ ℤ` — each right adjoint to the previous one, none of them fully faithful.*
-/

open CategoryTheory Limits

universe v u₁ u₂

-- `Folder126` imports `Mathlib.Combinatorics.Quiver.ReflQuiver` for its own statement; here the
-- arrows of a category go through `CategoryStruct.toQuiver`, as in `Solution`.
attribute [-instance] CategoryTheory.catToReflQuiver

namespace Challenge.Folder19

theorem proposition_page80 (n : ℕ) :
    ∃ G : Fin n → (((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type) ⥤ ((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type)),
      (∀ (i : Fin n) (h : i.1 + 1 < n), Nonempty (G i ⊣ G ⟨i.1 + 1, h⟩)) ∧
      ∀ i, ¬ ((G i).Full ∧ (G i).Faithful) := by
  sorry

/-- *Page 4, Théorème 1.12 b), in the form the reading corrects it to (Beck's theorem): the
comparison functor of `f ⊣ g` is an equivalence if and only if `f` is conservative and, for
every `f`-split pair `(u, v)`, `Ker(u, v)` exists and `f` commutes with it.* The « il faut »
of the manuscript, with condition C in place of `f`-split pairs, is false. -/
theorem beck_iff {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
    {f : A ⥤ B} {g : B ⥤ A} (adj : f ⊣ g) : (Comonad.comparison adj).IsEquivalence ↔
    f.ReflectsIsomorphisms ∧ ∀ ⦃X Y : A⦄ (u v : X ⟶ Y), f.IsCosplitPair u v →
      HasEqualizer u v ∧ PreservesLimit (parallelPair u v) f := by
  sorry

/-- *Pages 14–15, Gabriel–Popescu, as corrected by the reading. Let `C` be a Grothendieck
category with a generator `U`. Then `Hom_C(U, -)` is fully faithful and its left adjoint
`- ⊗_R U` is exact.* -/
theorem gabriel_popescu {C : Type u₁} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] (U : C) (hU : IsSeparator U) :
    (preadditiveCoyonedaObj U).Full ∧ (preadditiveCoyonedaObj U).Faithful ∧
      PreservesFiniteLimits (IsGrothendieckAbelian.tensorObj U) ∧
      PreservesFiniteColimits (IsGrothendieckAbelian.tensorObj U) := by
  sorry

end Challenge.Folder19

end Folder19

section Folder22

/-!
## Folder 22: Lemme 3.3 and the obstruction of pages 22 and 24

Finding `22-power-series-discrete-obstruction` (pages 22, 24).

The trusted statements of `Grothendieck.Folder22.lemme3_3` and
`Grothendieck.Folder22.no_derivation`.
-/

open PowerSeries TensorProduct

namespace Challenge.Folder22

/-- *Lemme 3.3. For `M` finitely presented, `M ⊗_A ∏ P_i → ∏ (M ⊗_A P_i)` is an isomorphism.* -/
theorem lemme3_3 {A : Type*} [CommRing A] {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] :
    Function.Bijective (TensorProduct.piRightHom A A M P) := by
  sorry

/-- *Pages 22, 24. Let `M` be a free `k`-module with basis `b`, and `a₀, a₁, …` in `k`. There
is no derivation `D : k⟦t⟧ → k⟦t⟧ ⊗_k M` with `D(aₙ) = 1 ⊗ b(iₙ)` for infinitely many
distinct indices `iₙ`.* -/
theorem no_derivation {k : Type*} [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]
    {R : Type*} [CommRing R] [Algebra R k] [Nontrivial k] {ι : Type*} (b : Module.Basis ι k M)
    (e : ℕ → ι) (he : Function.Injective e) (a : ℕ → k) (D : Derivation R k⟦X⟧ (k⟦X⟧ ⊗[k] M))
    (hD : ∀ n, D (C (a n)) = 1 ⊗ₜ b (e n)) : False := by
  sorry

end Challenge.Folder22

end Folder22

section Folder39

/-!
## Folder 39, pages 18–19: the formal preparation theorem

The trusted statements of `Grothendieck.Folder39.preparation_adique` and
`Grothendieck.Folder39.preparation_discrete`.
-/

open PowerSeries Polynomial

namespace Challenge.Folder39

/-- *Adic case. `A` complete and separated for the `I`-adic topology, `aᵢ ∈ I` for `i < N`,
`a_N` a unit: `F` is regular, and every `G` is uniquely `QF + r` with `deg r < N`.* -/
theorem preparation_adique
    {A : Type*} [CommRing A] (I : Ideal A) [IsAdicComplete I A] (F : A⟦X⟧) (N : ℕ)
    (h1 : ∀ i < N, coeff i F ∈ I) (h2 : IsUnit (coeff N F)) :
    (∀ H : A⟦X⟧, F * H = 0 → H = 0) ∧
      ∀ G : A⟦X⟧, ∃! qr : A⟦X⟧ × A[X], qr.2.degree < N ∧ G = qr.1 * F + qr.2 := by
  sorry

/-- *Discrete case. Over any commutative ring, if `a₀, …, a_{N-1}` are nilpotent and `a_N` is a
unit, `F` is regular and every `G` is uniquely `QF + r` with `deg r < N`.* -/
theorem preparation_discrete {A : Type*} [CommRing A] (F : A⟦X⟧) (N : ℕ)
    (h1 : ∀ i < N, IsNilpotent (coeff i F)) (h2 : IsUnit (coeff N F)) :
    (∀ H : A⟦X⟧, F * H = 0 → H = 0) ∧
      ∀ G : A⟦X⟧, ∃! qr : A⟦X⟧ × A[X], qr.2.degree < N ∧ G = qr.1 * F + qr.2 := by
  sorry

end Challenge.Folder39

end Folder39

section Folder42

/-!
## Folder 42, page 3: the topological step of Lemme 1

The trusted statement of `Grothendieck.Folder42.isOpen_of_stableUnderGeneralization`, written with
Mathlib alone and left unproved. `lake comparator` (`comparator.json`) checks that
`Solution.Folder42` proves exactly this statement, through the untrusted imports of this repository,
with no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

open TopologicalSpace

namespace Challenge.Folder42

/-- *In a noetherian sober space, a set `E` stable under generisation that contains, with each
of its points `x`, a neighbourhood of `x` in `closure {x}`, is open.* -/
theorem isOpen_of_stableUnderGeneralization
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
    {E : Set X} (hgen : StableUnderGeneralization E)
    (hloc : ∀ x ∈ E, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ∩ closure {x} ⊆ E) : IsOpen E := by
  sorry

end Challenge.Folder42

end Folder42

section Folder5

/-!
## Folder 5, page 4: Legendre's formula for `p^i`

Finding `5-universal-artinian-pd-normal-form`: the integrality of the coefficients `qᵢ`.

The trusted statement of `Grothendieck.Folder5.sub_one_mul_padicValNat_factorial_pow`, written with
Mathlib alone and left unproved. `lake comparator` (`comparator.json`) checks that
`Solution.Folder5` proves exactly this statement, through the untrusted imports of this repository,
with no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

open Nat

namespace Challenge.Folder5

/-- *`(p − 1) v_p((p^i)!) = p^i − 1`.* -/
theorem sub_one_mul_padicValNat_factorial_pow (p : ℕ) [hp : Fact p.Prime] (i : ℕ) :
    (p - 1) * padicValNat p (p ^ i)! = p ^ i - 1 := by
  sorry

end Challenge.Folder5

end Folder5

section Folder53

/-!
## Folder 53, page 9: the Galois argument, in topological form

The trusted statement of `Grothendieck.Folder53.irreducibleSpace_of_stable`.
-/

open scoped Pointwise

namespace Challenge.Folder53

/-- *Let `p : X' → X` be closed and generalizing with `X` irreducible, `X'` and `X` sober, and a
group `G` acting on `X'` by homeomorphisms, transitively on the fibres of `p`. If an
irreducible `G`-stable set `S` contains a point through which only one irreducible
component of `X'` passes, then `X'` is irreducible.* -/
theorem irreducibleSpace_of_stable
    {X' : Type*} {X : Type*} {G : Type*} [TopologicalSpace X'] [TopologicalSpace X]
    [Group G] [MulAction G X'] [ContinuousConstSMul G X']
    [QuasiSober X'] [QuasiSober X] [IrreducibleSpace X]
    (p : X' → X) (hpc : IsClosedMap p) (hpg : GeneralizingMap p)
    (horb : ∀ x y, p x = p y → ∃ g : G, g • x = y)
    {S : Set X'} (hS : IsIrreducible S) (hSG : ∀ g : G, g • S ⊆ S) {s : X'} (hs : s ∈ S)
    (huniq : ∀ C ∈ irreducibleComponents X', ∀ D ∈ irreducibleComponents X',
      s ∈ C → s ∈ D → C = D) :
    IrreducibleSpace X' := by
  sorry

end Challenge.Folder53

end Folder53

section Folder55

/-!
## Folder 55, page 13: the corollary of Lemme B

The trusted statement of `Grothendieck.Folder55.isNoetherianRing_of_tilde`.
-/

namespace Challenge.Folder55

/-- *`Γ(X, 𝒪_X)` is noetherian. If increasing sequences in a class `C` are stationary (Lemme
B), and every finitely generated ideal `I` gives a member `Ĩ` of `C`, monotonically, with
`Γ(Ĩ) = I` (Lemme A and its Corollaire 1), then `A` is noetherian.* -/
theorem isNoetherianRing_of_tilde {A P : Type*} [CommRing A] [PartialOrder P] (C : P → Prop)
    (hB : ∀ s : ℕ → P, Monotone s → (∀ k, C (s k)) → ∃ k₀, ∀ k ≥ k₀, s k = s k₀)
    (tilde : Ideal A → P) (Γ : P → Ideal A)
    (htilde_mono : ∀ I J : Ideal A, I.FG → J.FG → I ≤ J → tilde I ≤ tilde J)
    (htilde_mem : ∀ I : Ideal A, I.FG → C (tilde I))
    (hΓ : ∀ I : Ideal A, I.FG → Γ (tilde I) = I) :
    IsNoetherianRing A := by
  sorry

end Challenge.Folder55

end Folder55

section Folder74

/-!
## Folder 74, page 116: the maps `φ_a` on the relation `xyz = 1`

The trusted statement of `Grothendieck.Folder74.p116`.
-/

namespace Challenge.Folder74

/-- *On the relation `xyz = 1` of a group `G`, the maps `(x, y, z) ↦ (x, a⁻¹z⁻¹, a⁻¹y⁻¹)` all
preserve the relation if and only if every element of `G` has order dividing 2.* -/
theorem p116 {G : Type*} [Group G] :
    (∀ a x y z : G, x * y * z = 1 → x * (a⁻¹ * z⁻¹) * (a⁻¹ * y⁻¹) = 1) ↔
      ∀ g : G, g * g = 1 := by
  sorry

end Challenge.Folder74

end Folder74

section Folder77

/-!
## Folder 77: the local step of Proposition 8.5

Finding `77-discriminant-extension-across-2`.

The trusted statement of `Grothendieck.Folder77.prop85_local`.
-/

open IsLocalRing

namespace Challenge.Folder77

/-- *`R` local with maximal ideal `2R`, `C` a nonzero finite unramified `R`-algebra without
`2`-torsion, `v ∈ C` with `v² = 4ⁿΔ`. Then `Δ = b² − 4c` in `R`.* -/
theorem prop85_local {R : Type*} {C : Type*} [CommRing R] [IsLocalRing R] [CommRing C] [Algebra R C]
    [Algebra.FormallyUnramified R C] [Module.Finite R C] [Nontrivial C]
    (hm : maximalIdeal R = Ideal.span {2}) (h2C : ∀ x : C, 2 * x = 0 → x = 0)
    {Δ : R} {v : C} {n : ℕ} (hv : v ^ 2 = 4 ^ n * algebraMap R C Δ) :
    ∃ b c : R, b ^ 2 - 4 * c = Δ := by
  sorry

end Challenge.Folder77

end Folder77

section Folder84

/-!
## Folder 84, page 64: the product of quadratic algebras

Finding `84-product-quadratic-algebras-formula`.

The trusted statement of `Grothendieck.Folder84.identity_page64`.
-/

namespace Challenge.Folder84

/-- *With `Qᵢ = uᵢ² + bᵢuᵢ + cᵢ` and `u = u₁b₂ + u₂b₁ + 2u₁u₂`,
`u² + bu + c = b₂²Q₁ + b₁²Q₂ + 4(Q₁Q₂ − c₁Q₂ − c₂Q₁)` for `b = b₁b₂`,
`c = c₁b₂² + c₂b₁² − 4c₁c₂`.* -/
theorem identity_page64 {A : Type*} [CommRing A] (b₁ c₁ b₂ c₂ u₁ u₂ : A) :
    (2 * u₁ * u₂ + b₁ * u₂ + b₂ * u₁) ^ 2 + b₁ * b₂ * (2 * u₁ * u₂ + b₁ * u₂ + b₂ * u₁)
        + (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂)
      = b₂ ^ 2 * (u₁ ^ 2 + b₁ * u₁ + c₁) + b₁ ^ 2 * (u₂ ^ 2 + b₂ * u₂ + c₂)
        + 4 * ((u₁ ^ 2 + b₁ * u₁ + c₁) * (u₂ ^ 2 + b₂ * u₂ + c₂)
          - c₁ * (u₂ ^ 2 + b₂ * u₂ + c₂) - c₂ * (u₁ ^ 2 + b₁ * u₁ + c₁)) := by
  sorry

end Challenge.Folder84

end Folder84

section Folder85

/-!
## Folder 85: the fifth power of a `2 × 2` matrix

The trusted statement of `Grothendieck.Folder85.pow_five_eq`.
-/

namespace Challenge.Folder85

/-- *Cayley–Hamilton iterated: `g⁵ = x₅ g + y₅` with `x₅ = t⁴ − 3dt² + d²`.* -/
theorem pow_five_eq {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) :
    g ^ 5 = (g.trace ^ 4 - 3 * g.det * g.trace ^ 2 + g.det ^ 2) • g
      + (-(g.det) * (g.trace ^ 3 - 2 * g.det * g.trace)) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  sorry

end Challenge.Folder85

end Folder85

section Folder88

/-!
## Folder 88, page 14: the hyperbolic case of the trichotomy

The trusted statement of `Grothendieck.Folder88.hyperbolique_iff`.
-/

namespace Challenge.Folder88

/-- *`1/p + 1/q < 1/2` for `p, q ≥ 3` exactly when `p + q ≥ 9` and `(p, q) ≠ (3,6), (6,3)`.* -/
theorem hyperbolique_iff (p q : ℕ) (hp : 3 ≤ p) (hq : 3 ≤ q) :
    2 * (p + q) < p * q ↔ 9 ≤ p + q ∧ (p, q) ≠ (3, 6) ∧ (p, q) ≠ (6, 3) := by
  sorry

end Challenge.Folder88

end Folder88

section Folder90

/-!
## Folder 90, page 9: the components criterion

Finding `90-components-criterion`.

The trusted statement of `Grothendieck.Folder90.iInf_pow_eq_bot_iff`.
-/

namespace Challenge.Folder90

/-- *For `A` reduced and noetherian, `⋂ₙ πⁿA = 0` if and only if every irreducible component
of `Spec A` meets the special fibre `V(π)`.* -/
theorem iInf_pow_eq_bot_iff {A : Type*} [CommRing A] (π : A) [IsNoetherianRing A] [IsReduced A] :
    ⨅ n : ℕ, Ideal.span {π} ^ n = ⊥ ↔ ∀ p ∈ minimalPrimes A, p ⊔ Ideal.span {π} ≠ ⊤ := by
  sorry

end Challenge.Folder90

end Folder90

section Folder91

/-!
## Folder 91, page 19: the cartesian square of `Hom`

Finding `91-hom-unramified-rigidification`.

The trusted statement of `Grothendieck.Folder91HomUnramified.exists_unique_lift_of_surjective`.
-/

namespace Challenge.Folder91

/-- *`Hom(M_u, J)` is the fibre product of `Hom(M_v, J)` and `Hom(M_u, J_η)` over
`Hom(M_v, J_η)` when `M_v → M_u` is onto and `J → J_η` is injective.* -/
theorem exists_unique_lift_of_surjective {A Mu Mv J Jη : Type*} [CommRing A]
    [AddCommGroup Mu] [AddCommGroup Mv] [AddCommGroup J] [AddCommGroup Jη] [Module A Mu]
    [Module A Mv] [Module A J] [Module A Jη] (f : Mv →ₗ[A] Mu) (hf : Function.Surjective f)
    (ι : J →ₗ[A] Jη) (hι : Function.Injective ι) (a : Mv →ₗ[A] J) (b : Mu →ₗ[A] Jη)
    (hab : ι.comp a = b.comp f) :
    ∃! c : Mu →ₗ[A] J, c.comp f = a ∧ ι.comp c = b := by
  sorry

end Challenge.Folder91

end Folder91

section Folder93

/-!
## Folder 93: Jacobson's formula in rank one

The trusted statement of `Grothendieck.Folder93.PCurvature.jacobson`.
-/

namespace Challenge.Folder93

/-- *Statement 2. In characteristic `p`, for a derivation `D` of `A` and `a ∈ A`,
`(D + a)ᵖ = Dᵖ + aᵖ + D^{p−1}(a)` as operators on `A`.* -/
theorem jacobson {A : Type*} [CommRing A] (D : Derivation ℤ A A) (p : ℕ) [hp : Fact p.Prime]
    [CharP A p] (a : A) :
    ((D : Module.End ℤ A) + LinearMap.mulLeft ℤ a) ^ p =
      (D : Module.End ℤ A) ^ p + LinearMap.mulLeft ℤ (a ^ p + D^[p - 1] a) := by
  sorry

end Challenge.Folder93

end Folder93

section Folder94

/-!
## Folder 94, page 7: constant fibre rank over a reduced local ring

Finding `94-rank-constructibility` (Remarque 5 bis).

The trusted statement of `Grothendieck.Folder94.free_of_finrank_eq_of_isReduced`, written with
Mathlib alone and left unproved. `lake comparator` (`comparator.json`) checks that
`Solution.Folder94` proves exactly this statement, through the untrusted imports of this repository,
with no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

open Module IsLocalRing TensorProduct

namespace Challenge.Folder94

/-- *Over a reduced local ring `B`, a finite module `P` whose fibre rank at every minimal prime
equals its rank at the closed point is free.* -/
theorem free_of_finrank_eq_of_isReduced {B P : Type*} [CommRing B] [IsLocalRing B] [IsReduced B]
    [AddCommGroup P] [Module B P] [Module.Finite B P]
    (h : ∀ 𝔮 : PrimeSpectrum B, 𝔮.asIdeal ∈ minimalPrimes B →
      finrank (Localization.AtPrime 𝔮.asIdeal) (Localization.AtPrime 𝔮.asIdeal ⊗[B] P) =
        finrank (ResidueField B) (ResidueField B ⊗[B] P)) :
    Module.Free B P := by
  sorry

end Challenge.Folder94

end Folder94
