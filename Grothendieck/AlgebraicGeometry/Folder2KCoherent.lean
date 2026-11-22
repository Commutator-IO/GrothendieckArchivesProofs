/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupCoherentNonzero
import Grothendieck.Attr

/-!
# Folder 2, page 13: the class of a structure sheaf in the `K`-group of coherent sheaves

Finding `2-trivial-total-chern-class` of `src/content/findings.ts` (pages 9, 11, 13 of folder 2):
for a constant section `i : X → X × P^r` and a divisor `Y ⊂ X` whose class `x' ∈ A¹(X)` is
nonzero but killed by `(r−1)!`, `i_!(𝒪_Y)` is a **nonzero** class of `K(X × P^r)` whose total
Chern class is `1`. The Chern class computation of pages 9 and 13 is proved in
`Grothendieck/AlgebraicGeometry/Folder2.lean`; this file is about the other half, the nonvanishing
of a class in the Grothendieck group of coherent sheaves. It proves the nonvanishing of `[𝒪_Y]` on
an affine `Y`, not of `i_!(𝒪_Y)`.

## Main results

Let `A` be a noetherian ring and `𝔭` a minimal prime of `A`.

* `exists_lengthAtPrimeHom`: `[M] ↦ ℓ_{A_𝔭}(M_𝔭)` is a homomorphism `K'₀(A) →+ ℤ` (the
  multiplicity of `M` at the generic point `𝔭` of `Spec A`; for a domain and `𝔭 = 0` it is the
  generic rank).
* `quotient_cls_ne_zero`: for an ideal `I ⊆ 𝔭`, the class `[A/I]` is nonzero in `K'₀(A)`.
* `coherentKZero_quotient_ne_zero`: the same in `K'₀(Spec A)`, for the class of `𝒪_{V(I)}`
  (pushed forward to `Spec A`). With `A` the coordinate ring of an affine `Y` and `I = 0`,
  `[𝒪_Y] ≠ 0` in `K'₀(Y)`, whether or not `Y` is reduced or irreducible.

## Implementation notes

The vendored AxiomMath/Stacks files supply the group: `KPrime0 R`, the Grothendieck group of
finite `R`-modules (`FinModule R`, classes `FinModule.cls`, universal property
`KPrime0.universalProperty_existence`), `AlgebraicGeometry.CoherentKZero X = K'₀(X)`, and for a
noetherian ring the identification `affineCoherentKZeroEquiv : K'₀(Spec R) ≃+ K'₀(R)`
(Stacks tag 0FDH), which sends the class of `M~` to `[M]`.

`A_𝔭` is noetherian of dimension `0`, hence artinian (Hopkins–Levitzki), so every
finite `A_𝔭`-module has finite length; `A_𝔭 ⊗_A −` is exact (localisation is flat) and length is
additive, which gives the homomorphism. `A_𝔭 ⊗_A A/I ≅ A_𝔭/IA_𝔭` is nonzero since
`IA_𝔭 ⊆ 𝔭A_𝔭`, so the invariant is positive on `[A/I]`.

## Not formalised

The class lives on `X × P^r`, not on `Y`: that `i_!(𝒪_Y) = [𝒪_Y] ⊠ [pt]`
is nonzero in `K(X × P^r)` needs the projective bundle formula `K(X × P^r) = K(X)[ξ]/(ξ^{r+1})`
and `[𝒪_Y] = 1 − [𝒪(−Y)] ≠ 0` in `K(X)`, neither of which Stacks has. The invariant here
cannot replace it: `i_!(𝒪_Y)` is supported in codimension `r + 1`, where every local invariant
vanishes, and torsion classes do vanish affine-locally (`[ℤ/n] = 0` in `K'₀(ℤ)`). Also not
formalised: the total Chern class on `K` (Stacks has none; its algebra is in
`Grothendieck/AlgebraicGeometry/Folder2.lean`) and the restriction `r ≥ 3`.

## References

* A. Grothendieck, folder 2, pp. 9, 11, 13 (finding `2-trivial-total-chern-class`)
* Stacks Project, tag 0FDH
-/

@[expose] public section


namespace Grothendieck.Folder2KCoherent

open Stacks.AlgebraicGeometry.GrothendieckGroupAffine TensorProduct

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Over the localisation `A_𝔭` at a minimal prime of a noetherian ring, `A_𝔭 ⊗_A M` has finite
length for every finite `A`-module `M`. -/
theorem length_localization_ne_top (p : Ideal A) [p.IsPrime] (hp : p ∈ minimalPrimes A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] M) ≠ ⊤ := by
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) := .of_isLocalization p hp _
  have : IsArtinianRing (Localization.AtPrime p) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact Module.length_ne_top

/-- The length of `M_𝔭 = A_𝔭 ⊗_A M` over `A_𝔭`, as an integer. -/
noncomputable def lengthAtPrime (p : Ideal A) [p.IsPrime] (M : FinModule A) : ℤ :=
  ((Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] M.carrier)).toNat : ℤ)

/-- **Length at a minimal prime is additive**: it descends to a homomorphism `K'₀(A) →+ ℤ`. -/
@[montpellier "2, 13"]
theorem exists_lengthAtPrimeHom (p : Ideal A) [p.IsPrime] (hp : p ∈ minimalPrimes A) :
    ∃ φ : KPrime0 A →+ ℤ, ∀ M : FinModule A, φ M.cls = lengthAtPrime p M := by
  refine KPrime0.universalProperty_existence (lengthAtPrime p) ?_ ?_
  · intro N N' e
    unfold lengthAtPrime
    rw [(LinearEquiv.baseChange (R := A) (A := Localization.AtPrime p) (M := N.carrier)
      (N := N'.carrier) e).length_eq]
  · intro N N' N'' f g hf hg hexact
    have hex : Function.Exact f g := LinearMap.exact_iff.mpr hexact.symm
    have hf' : Function.Injective (f.baseChange (Localization.AtPrime p)) := by
      rw [LinearMap.baseChange_eq_lTensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap f hf
    have hg' : Function.Surjective (g.baseChange (Localization.AtPrime p)) := by
      rw [LinearMap.baseChange_eq_lTensor]
      exact LinearMap.lTensor_surjective _ hg
    have hex' : Function.Exact (f.baseChange (Localization.AtPrime p))
        (g.baseChange (Localization.AtPrime p)) := by
      rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
      exact Module.Flat.lTensor_exact _ hex
    have h := Module.length_eq_add_of_exact _ _ hf' hg' hex'
    unfold lengthAtPrime
    rw [h, ENat.toNat_add (length_localization_ne_top p hp _)
      (length_localization_ne_top p hp _)]
    exact Nat.cast_add _ _

/-- `A ⧸ I` as a finite `A`-module. -/
def quotientFinModule (I : Ideal A) : FinModule A := { carrier := A ⧸ I }

/-- The length of `(A/I)_𝔭` is positive when `I ⊆ 𝔭`. -/
theorem lengthAtPrime_quotient_pos (p : Ideal A) [p.IsPrime] (hp : p ∈ minimalPrimes A)
    (I : Ideal A) (hI : I ≤ p) : 0 < lengthAtPrime p (quotientFinModule I) := by
  have hne : I.map (algebraMap A (Localization.AtPrime p)) ≠ ⊤ := by
    intro h
    have h' := Ideal.map_mono (f := algebraMap A (Localization.AtPrime p)) hI
    rw [h, Localization.AtPrime.map_eq_maximalIdeal] at h'
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp h')
  have : Nontrivial (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have : Nontrivial (Localization.AtPrime p ⊗[A] (A ⧸ I)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime p)
      I).injective.nontrivial
  change 0 < ((Module.length (Localization.AtPrime p)
    (Localization.AtPrime p ⊗[A] (A ⧸ I))).toNat : ℤ)
  exact_mod_cast ENat.toNat_pos Module.length_pos.ne' (length_localization_ne_top p hp _)

/-- **`[A/I] ≠ 0` in `K'₀(A)`** when `I` lies in a minimal prime of the noetherian ring `A`. -/
@[montpellier "2, 13"]
theorem quotient_cls_ne_zero (p : Ideal A) [p.IsPrime] (hp : p ∈ minimalPrimes A)
    (I : Ideal A) (hI : I ≤ p) : (quotientFinModule I).cls ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_lengthAtPrimeHom p hp
  intro h
  have h1 := hφ (quotientFinModule I)
  rw [h, map_zero] at h1
  exact (lengthAtPrime_quotient_pos p hp I hI).ne h1

/-- **The class of `𝒪_{V(I)}` in `K'₀(Spec A)` is nonzero** when `I` lies in a minimal prime of
the noetherian ring `A`; it is the class sent to `[A/I]` by Stacks' identification
`K'₀(Spec A) ≃+ K'₀(A)` (tag 0FDH). -/
@[montpellier "2, 13"]
theorem coherentKZero_quotient_ne_zero (p : Ideal A) [p.IsPrime] (hp : p ∈ minimalPrimes A)
    (I : Ideal A) (hI : I ≤ p) :
    (affineCoherentKZeroEquiv A).symm (quotientFinModule I).cls ≠ 0 := by
  intro h
  apply quotient_cls_ne_zero p hp I hI
  have := congrArg (affineCoherentKZeroEquiv A) h
  rwa [AddEquiv.apply_symm_apply, map_zero] at this

end Grothendieck.Folder2KCoherent
