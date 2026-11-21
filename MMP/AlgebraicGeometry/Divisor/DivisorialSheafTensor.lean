-- Copied from AxiomMath/MMP at 1f9ade3 (Apache-2.0, see NOTICE and MMP/LICENSE), and modified in
-- GrothendieckArchivesProofs (2026-11-21): ported to Stacks f56a316, where the sheafification
-- behind `Stacks.SheafOfModules.Tensor.sheafTensor` is sealed. Mathlib's
-- `PresheafOfModules.sheafificationAdjunction` is replaced by
-- `Stacks.SheafOfModules.Tensor.sheafificationAdjunction` (its unit lemma likewise); nothing else
-- changes.
module

public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.EpiGlue

/-!
# The divisorial sheaf of a sum of Cartier divisors

Let `X` be a quasi-compact locally Noetherian normal scheme and `D`, `D'` divisors on `X`.
Multiplication in the sheaf of rational functions `𝒦_X` sends a section `φ` of `𝒪_X(D)` and a
section `ψ` of `𝒪_X(D')` over `U` to the section `φψ` of `𝒪_X(D + D')`, since
`v_E(φψ) = v_E(φ) + v_E(ψ)`. This is bilinear and compatible with restriction, so it induces the
multiplication map `𝒪_X(D) ⊗ 𝒪_X(D') ⟶ 𝒪_X(D + D')`. When `D` and `D'` are Cartier it is an
isomorphism [Har77, II.6.13].

## Main definitions

* `MMP.Mori.Divisor.divisorialMul`: the product `𝒪_X(D)(U) × 𝒪_X(D')(U) → 𝒪_X(D + D')(U)`.
* `MMP.Mori.Divisor.divisorialSheafTensorMul`: the multiplication map
  `𝒪_X(D) ⊗ 𝒪_X(D') ⟶ 𝒪_X(D + D')`.
* `MMP.Mori.Divisor.IsCartier.divisorialSheafTensorIso`: `𝒪_X(D) ⊗ 𝒪_X(D') ≅ 𝒪_X(D + D')` for
  Cartier `D` and `D'`.

## Main results

* `MMP.Mori.Divisor.epi_divisorialSheafTensorMul`: the multiplication map is an epimorphism as
  soon as `D` is Cartier.
* `MMP.Mori.Divisor.IsCartier.isIso_divisorialSheafTensorMul`: it is an isomorphism when `D` and
  `D'` are Cartier.

## Implementation notes

The tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor`, the sheafification of the
objectwise tensor product, which is the one in which the degree of an invertible sheaf on a
proper curve is additive. The multiplication map is obtained from the bilinear map on sections
by the universal properties of the objectwise tensor product and of sheafification.

That it is an isomorphism is not checked on trivializations. Near a point where `ψ` is a local
equation of `D`, a section `s` of `𝒪_X(D + D')` is the product of the section `ψ⁻¹` of `𝒪_X(D)`
and the section `ψ s` of `𝒪_X(D')`, so the map is locally surjective, hence an epimorphism; an
epimorphism between invertible sheaves is an isomorphism.

## References

* [R. Hartshorne, *Algebraic geometry*][Har77], II.6.13
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace MMP.Mori

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

namespace Divisor

variable {D D' : Divisor X}

/-- The product `φψ ∈ 𝒪_X(D + D')(U)` of sections `φ ∈ 𝒪_X(D)(U)` and `ψ ∈ 𝒪_X(D')(U)`,
computed in `𝒦_X(U)`. -/
def divisorialMul (U : X.Opens) (φ : D.divisorialSubmodule U) (ψ : D'.divisorialSubmodule U) :
    (D + D').divisorialSubmodule U :=
  ⟨fun Z => φ.1 Z * ψ.1 Z, fun E hE => ((φ.2 E hE).mul (ψ.2 E hE)).mono (le_of_eq (by
    rw [DivisorWithCoeffs.coeff_add]; ring))⟩

/-- The rational function underlying `divisorialMul U φ ψ` is the pointwise product of those
underlying `φ` and `ψ`. -/
@[simp]
theorem coe_divisorialMul_apply (U : X.Opens) (φ : D.divisorialSubmodule U)
    (ψ : D'.divisorialSubmodule U) (Z) : (divisorialMul U φ ψ).1 Z = φ.1 Z * ψ.1 Z := rfl

variable (D D') in
/-- The multiplication of sections, as a morphism out of the objectwise tensor product of the
underlying presheaves of modules of `𝒪_X(D)` and `𝒪_X(D')`. -/
def divisorialTensorMul : PresheafOfModules.tensorObj (O := X.presheaf) D.divisorialSheaf.val
    D'.divisorialSheaf.val ⟶
    (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
      (D + D').divisorialSheaf :=
  PresheafOfModules.tensorMk (fun W φ ψ => divisorialMul W.unop φ ψ)
    (fun _ _ _ _ => Subtype.ext (funext fun _ => add_mul _ _ _))
    (fun _ _ _ _ => Subtype.ext (funext fun _ => mul_assoc _ _ _))
    (fun _ _ _ _ => Subtype.ext (funext fun _ => mul_add _ _ _))
    (fun _ _ _ _ => Subtype.ext (funext fun _ => mul_left_comm _ _ _))
    (fun _ _ _ _ _ => rfl)

variable (D D') in
/-- The multiplication map `𝒪_X(D) ⊗ 𝒪_X(D') ⟶ 𝒪_X(D + D')`, `φ ⊗ ψ ↦ φψ`. -/
def divisorialSheafTensorMul :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
      X.toRingedSpace.IsSheaf⟩).obj D.divisorialSheaf).obj D'.divisorialSheaf ⟶
      (D + D').divisorialSheaf :=
  ((Stacks.SheafOfModules.Tensor.sheafificationAdjunction
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).homEquiv _ _).symm
    (divisorialTensorMul D D')

/-- The multiplication map sends the image of a pure tensor `φ ⊗ ψ` to the product `φψ`. -/
theorem divisorialSheafTensorMul_unit (W : X.Opensᵒᵖ) (φ : D.divisorialSheaf.val.obj W)
    (ψ : D'.divisorialSheaf.val.obj W) :
    PresheafOfModules.Hom.app (divisorialSheafTensorMul D D').val W
      (PresheafOfModules.Hom.app ((Stacks.SheafOfModules.Tensor.sheafificationAdjunction
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).unit.app
        (PresheafOfModules.tensorObj (O := X.presheaf) D.divisorialSheaf.val
          D'.divisorialSheaf.val)) W (φ ⊗ₜ ψ)) = divisorialMul W.unop φ ψ :=
  PresheafOfModules.hom_congr_apply'
    (Stacks.SheafOfModules.Tensor.sheafificationAdjunction_unit_comp_homEquiv_symm
      (R := ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)
      (M := PresheafOfModules.tensorObj (O := X.presheaf) D.divisorialSheaf.val
        D'.divisorialSheaf.val)
      (N := (D + D').divisorialSheaf) (divisorialTensorMul D D')) W (φ ⊗ₜ ψ)

/-- If `D` has a local equation on a neighbourhood of every point, the multiplication map
`𝒪_X(D) ⊗ 𝒪_X(D') ⟶ 𝒪_X(D + D')` is an epimorphism: near a point where `ψ` is a local equation
of `D`, a section `s` of `𝒪_X(D + D')` is `ψ⁻¹ · (ψ s)` with `ψ⁻¹` a section of `𝒪_X(D)` and
`ψ s` a section of `𝒪_X(D')`. -/
theorem epi_divisorialSheafTensorMul (hD : D.IsCartier) :
    Epi (divisorialSheafTensorMul D D') := by
  apply Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective
  refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr fun V s x hx => ?_
  obtain ⟨U, hxU, ψ, hψ⟩ := hD x
  have hU : ∀ E : PrimeDivisor X, (E.support ∩ (V ⊓ U : X.Opens)).Nonempty →
      (E.support ∩ U).Nonempty := fun E h =>
    h.mono (Set.inter_subset_inter_right _ (inf_le_right : V ⊓ U ≤ U))
  have hV : ∀ E : PrimeDivisor X, (E.support ∩ (V ⊓ U : X.Opens)).Nonempty →
      (E.support ∩ V).Nonempty := fun E h =>
    h.mono (Set.inter_subset_inter_right _ (inf_le_left : V ⊓ U ≤ V))
  let s' : (D + D').divisorialSubmodule V := s
  let a : D.divisorialSubmodule (V ⊓ U) :=
    ⟨fun Z => ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1, fun E h =>
      Or.inr (le_of_eq (by
        rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv, hψ E (hU E h)]))⟩
  let b : D'.divisorialSubmodule (V ⊓ U) :=
    ⟨fun Z => (ψ : RationalFunctions X) Z.1 * s'.1 ⟨Z.1, Z.2.1⟩, fun E h =>
      (PrimeDivisor.OrdGE.mul (Or.inr (E.valuation_component ψ).ge)
        (s'.2 E (hV E h))).mono (le_of_eq (by
          rw [DivisorWithCoeffs.coeff_add, hψ E (hU E h)]; ring))⟩
  refine ⟨V ⊓ U, inf_le_left, ⟨PresheafOfModules.Hom.app
    ((Stacks.SheafOfModules.Tensor.sheafificationAdjunction
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).unit.app
      (PresheafOfModules.tensorObj (O := X.presheaf) D.divisorialSheaf.val
        D'.divisorialSheaf.val)) (op (V ⊓ U))
      ((a : D.divisorialSheaf.val.obj (op (V ⊓ U))) ⊗ₜ
        (b : D'.divisorialSheaf.val.obj (op (V ⊓ U)))), ?_⟩, hx, hxU⟩
  refine (divisorialSheafTensorMul_unit (op (V ⊓ U)) a b).trans (Subtype.ext (funext fun Z => ?_))
  change ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 *
      ((ψ : RationalFunctions X) Z.1 * s'.1 ⟨Z.1, Z.2.1⟩) = s'.1 ⟨Z.1, Z.2.1⟩
  rw [← mul_assoc, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply,
    one_mul]

/-- The tensor product of the divisorial sheaves of two Cartier divisors is invertible. -/
theorem IsCartier.isInvertibleModule_tensorSheaf [CompactSpace X] (hD : D.IsCartier)
    (hD' : D'.IsCartier) :
    Stacks.Ample.IsInvertibleModule X
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj D.divisorialSheaf).obj D'.divisorialSheaf) :=
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := hD'.isInvertibleModule_divisorialSheaf
  Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2
    D.divisorialSheaf D'.divisorialSheaf

/-- For Cartier divisors `D` and `D'` the multiplication map
`𝒪_X(D) ⊗ 𝒪_X(D') ⟶ 𝒪_X(D + D')` is an isomorphism. -/
theorem IsCartier.isIso_divisorialSheafTensorMul [CompactSpace X] (hD : D.IsCartier)
    (hD' : D'.IsCartier) : IsIso (divisorialSheafTensorMul D D') :=
  @Stacks.Chow.GenuineChern.isIso_of_epi_of_isInvertible X _ _ (divisorialSheafTensorMul D D')
    (epi_divisorialSheafTensorMul hD) (hD.isInvertibleModule_tensorSheaf hD')
    (hD.add hD').isInvertibleModule_divisorialSheaf

/-- **Hartshorne II.6.13.** For Cartier divisors `D` and `D'` on a quasi-compact locally
Noetherian normal scheme, `𝒪_X(D) ⊗ 𝒪_X(D') ≅ 𝒪_X(D + D')`, by multiplication of sections in
the sheaf of rational functions. -/
def IsCartier.divisorialSheafTensorIso [CompactSpace X] (hD : D.IsCartier)
    (hD' : D'.IsCartier) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
      X.toRingedSpace.IsSheaf⟩).obj D.divisorialSheaf).obj D'.divisorialSheaf ≅
      (D + D').divisorialSheaf :=
  haveI := hD.isIso_divisorialSheafTensorMul hD'
  asIso (divisorialSheafTensorMul D D')

end Divisor

end MMP.Mori
