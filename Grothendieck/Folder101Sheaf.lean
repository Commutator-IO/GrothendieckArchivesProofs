module

public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExplicit
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SectionsWithSupport
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.DegreeZeroSections
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 101, page 10: the sheaf side, `j_!𝒪_U` and local cohomology of any `𝒪_X`-module

Finding `101-sheaf-duality-dim-one` and its dimension-two companion
`101-sheaf-duality-dim-two-fails`. Pages 10 to 15 of folder 101 test local duality on
`X = Spec A`, `A` local, for `𝒪_X`-modules that need not be quasi-coherent, the test case being
the extension by zero `F = j_!𝒪_U` of the structure sheaf of `U = D(f)`, `f ∈ 𝔪`. The
module-level computations are in `Folder101.lean`, `Folder101Ext.lean`,
`Folder101LocalCohomology.lean` and `Folder101DimTwo.lean`; this file supplies the sheaves
themselves, with local cohomology as the right derived functors of the sections supported at the
closed point `x` (AxiomMath/Stacks, Stacks 0G71: `sectionsWithSupport` and its long exact
sequence).

**What is proved.**
* `jO`: `j_!𝒪_U`, the extension by zero of Stacks 00A4 (5) (`jShriekExplicit`).
* `homEquivΓ`, `homEquivΓ_add`, `homEquivLocalization`: `Ext⁰(X; j_!𝒪_U, 𝒪_X) = Hom(j_!𝒪_U, 𝒪_X)`
  is `Γ(U, 𝒪_X) = A_f`, additively (page 10's `Ext⁰(X; F, 𝒪_X) = A_f`).
* `isZero_stalk_x₀`, `subsingleton_globalSections`: `(j_!𝒪_U)_x = 0` and `Γ(X, j_!𝒪_U) = 0`.
* `preservesEpimorphisms_Γfun`, `isZero_cohomology`: on the spectrum of a local ring `Γ(X, -)` is
  exact (the only open containing `x` is `X`), so `Hⁿ(X, M) = 0` for `n > 0` and every
  `𝒪_X`-module `M`.
* `localCohomology_eq_punctured`: hence `Hⁿ⁺¹_x(M) ≅ Hⁿ(X ∖ {x}, M)` for `n ≥ 1`, and the same
  for `n = 0` when `Γ(X, M) = 0`, by the connecting maps of the long exact sequence.
* `nonempty_iso_cokernel`: `H¹_x(M) ≅ Coker(Γ(X, M) → Γ(X ∖ {x}, M))` for every `𝒪_X`-module
  `M` (and `H⁰_x(M)` is the kernel by definition): page 10's `H⁰_x = Ker u`, `H¹_x = Coker u`.
* `localCohomology_jO`: for `F = j_!𝒪_U`, `H⁰_x(F) = 0`, `H¹_x(F) ≅ Γ(X ∖ {x}, F)` and
  `Hⁿ⁺¹_x(F) ≅ Hⁿ(X ∖ {x}, F)`: the local cohomology of page 10 is the cohomology of `F` on the
  punctured spectrum.
* `isZero_localCohomology_of_two_le`: for `A` a discrete valuation ring, `Hⁱ_x(F) = 0` for
  `i ≥ 2` and **every** `𝒪_X`-module `F`, quasi-coherent or not (page 10's « nothing in higher
  degrees » for the triples `(M₀, M₁, u)`; `Folder101LocalCohomology.lean` had it for
  quasi-coherent sheaves only): `X ∖ {x}` is the generic point, and sections over an open that
  lies in every neighbourhood of one of its points are exact (`surjective_evaluation_of_le`).

**How.** An epimorphism of `𝒪_X`-modules is locally surjective on the underlying abelian sheaves
(Mathlib's `TopCat.Sheaf.isLocallySurjective_iff_epi`); a neighbourhood of the closed point is
`X`, a neighbourhood of the generic point of a discrete valuation ring contains `X ∖ {x}`. Exact
functors have no higher derived functors (`Functor.isZero_rightDerived_of_exact`).

**Not formalised.** The identification of `Hⁿ(X ∖ {x}, -)` (the derived functors of sections
over `X ∖ {x}` on `𝒪_X`-modules) with the cohomology of the open subscheme; the computation of
`H¹(X ∖ {x}, j_!𝒪_U)` in dimension `2`, hence the exact sequence
`0 → A → ∏ 𝒪_{x_i} → H²_x(F) → E(k) → 0` of pages 14–15 and the duality map `φ` with its
injectivity (only « injective ⇒ not surjective » is proved, in `Folder101DimTwo.lean`); the
equivalence between `𝒪_X`-modules on the spectrum of a discrete valuation ring and the page's
triples.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction TopCat.Presheaf

universe u

namespace Grothendieck.Folder101Sheaf

variable (A : Type u) [CommRing A]

/-- `X = Spec A` as a ringed space. -/
noncomputable abbrev X : RingedSpace.{u, u} := (Spec (.of A)).toSheafedSpace

/-- The open `U = D(f)`. -/
def U (f : A) : Opens (X A).carrier := PrimeSpectrum.basicOpen f

/-- `j_! 𝒪_U`. -/
noncomputable abbrev jO (f : A) : SheafOfModules.{u} (structureSheafRing (X A)) :=
  (ExtensionByZeroModules.jShriekExplicit (U A f) (structureSheafRing (X A))).obj
    (SheafOfModules.unit _)

lemma imF_top (f : A) : (imF (U A f)).obj ⊤ = U A f := by
  ext x; simp [imF]

/-- The sections of a presheaf of types on the opens of a space are its values on the whole
space. -/
def sectionsEquivTop {T : TopCat.{u}} (F : (Opens T)ᵒᵖ ⥤ Type u) :
    F.sections ≃ F.obj (op ⊤) where
  toFun s := s.1 (op ⊤)
  invFun v := ⟨fun V => F.map (homOfLE le_top : V.unop ⟶ ⊤).op v, fun {V W} g => by
    change (F.map _ ≫ F.map g) v = _
    rw [← F.map_comp]
    rfl⟩
  left_inv s := by
    ext V
    exact s.2 _
  right_inv v := by
    change F.map (𝟙 _) v = v
    simp

/-- **`Ext⁰(X; j_!𝒪_U, 𝒪_X) = Γ(U, 𝒪_X)`**: maps `j_!𝒪_U ⟶ 𝒪_X` are the sections of
`𝒪_X` over `U`. -/
@[montpellier "101, 10"]
noncomputable def homEquivΓ (f : A) :
    (jO A f ⟶ SheafOfModules.unit (structureSheafRing (X A))) ≃
      Γ(Spec (.of A), PrimeSpectrum.basicOpen f) :=
  ((ExtensionByZeroModules.jShriekExplicitAdjunction _ _).homEquiv _ _).trans <|
    (SheafOfModules.unitHomEquiv _).trans <|
      (sectionsEquivTop (((ExtensionByZeroModules.jStar (U A f) (structureSheafRing (X A))).obj
        (SheafOfModules.unit _)).val.presheaf ⋙ forget _)).trans <|
        (((Spec (.of A)).presheaf.mapIso (eqToIso (imF_top A f).symm).op).commRingCatIsoToRingEquiv
          ).toEquiv

set_option backward.isDefEq.respectTransparency.types false in
/-- `Γ(D(g), 𝒪_{Spec R}) = R_g`, from Mathlib's `IsLocalization.Away` instance. -/
noncomputable def sectionsBasicOpenEquiv (R : CommRingCat.{u}) (g : R) :
    Γ(Spec R, PrimeSpectrum.basicOpen g) ≃+* Localization.Away g :=
  (IsLocalization.algEquiv (Submonoid.powers g) _ _).toRingEquiv

/-- **`Ext⁰(X; j_!𝒪_U, 𝒪_X) = A_f`** (folder 101, page 10): the maps `j_!𝒪_U ⟶ 𝒪_X` are
the elements of the localisation `A_f`, `Γ(D(f), 𝒪_X)` being `A_f`. -/
noncomputable def homEquivLocalization (f : A) :
    (jO A f ⟶ SheafOfModules.unit (structureSheafRing (X A))) ≃ Localization.Away f :=
  (homEquivΓ A f).trans
    (sectionsBasicOpenEquiv (.of A) f).toEquiv

/-- The bijection `homEquivΓ` is additive. -/
theorem homEquivΓ_add (f : A)
    (φ ψ : jO A f ⟶ SheafOfModules.unit (structureSheafRing (X A))) :
    homEquivΓ A f (φ + ψ) = homEquivΓ A f φ + homEquivΓ A f ψ := by
  have key : ∀ g, homEquivΓ A f g =
      ((Spec (.of A)).presheaf.mapIso (eqToIso (imF_top A f).symm).op).commRingCatIsoToRingEquiv
        ((((ExtensionByZeroModules.jShriekExplicitAdjunction _ _).homEquiv _ _ g).val.app
          (op ⊤)) (1 : (ExtensionByZeroModules.resRing (U A f)
            (structureSheafRing (X A))).obj.obj (op ⊤))) := fun _ => rfl
  rw [key, key, key]
  refine (congrArg _ ?_).trans (map_add _ _ _)
  have hadd : (ExtensionByZeroModules.jShriekExplicitAdjunction _ _).homEquiv _ _ (φ + ψ) =
      (ExtensionByZeroModules.jShriekExplicitAdjunction _ _).homEquiv _ _ φ +
        (ExtensionByZeroModules.jShriekExplicitAdjunction _ _).homEquiv _ _ ψ := by
    simp only [Adjunction.homEquiv_unit, Functor.map_add, Preadditive.comp_add]
  rw [hadd]
  rfl

/-- **Sections over an open `W` that lies in every open neighbourhood of one of its points `p`
are exact on epimorphisms**: an epimorphism of `𝒪`-modules is locally surjective, and the only
neighbourhood of `p` inside `W` is `W`. This holds on any ringed space and for every module,
quasi-coherent or not. -/
theorem surjective_evaluation_of_le (W : Opens (X A).carrier) (p : (X A).carrier)
    (hp : p ∈ W) (h : ∀ V : Opens (X A).carrier, p ∈ V → W ≤ V)
    {M N : ModuleSheaves (X A)} (φ : M ⟶ N) [Epi φ] :
    Function.Surjective ((SheafOfModules.evaluation (structureSheafRing (X A)) (op W)).map φ) := by
  have : Epi ((SheafOfModules.toSheaf _).map φ) := inferInstance
  have hls := (TopCat.Sheaf.isLocallySurjective_iff_epi
    ((SheafOfModules.toSheaf _).map φ)).2 this
  intro t
  obtain ⟨V, hV, ⟨s, hs⟩, hx⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).1 hls W t p hp
  obtain rfl : V = W := le_antisymm hV (h V hx)
  refine ⟨s, hs.trans ?_⟩
  change ((SheafOfModules.toSheaf _).obj N).obj.map (homOfLE hV).op t = t
  rw [show homOfLE hV = 𝟙 _ from Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
  rfl

section Local

variable [IsLocalRing A]

/-- The closed point `x` of `Spec A`. -/
abbrev x₀ : (X A).carrier := IsLocalRing.closedPoint A

lemma x₀_notMem {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A) : x₀ A ∉ U A f :=
  fun h => (PrimeSpectrum.mem_basicOpen f _).1 h hf

/-- An open of the spectrum of a local ring containing the closed point is everything. -/
lemma eq_top_of_x₀_mem {W : Opens (X A).carrier} (h : x₀ A ∈ W) : W = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  exact ((PrimeSpectrum.le_iff_specializes y (IsLocalRing.closedPoint A)).1 le_top).mem_open
    W.isOpen h

/-- **The stalk of `j_!𝒪_U` at the closed point vanishes**, `f` being in the maximal ideal. -/
theorem isZero_stalk_x₀ {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A) :
    IsZero (TopCat.Presheaf.stalk (jO A f).val.presheaf (x₀ A)) :=
  ExtensionByZeroModules.isZero_stalk_jShriekExplicit _ _ _ _ (x₀_notMem A hf)

/-- **`Γ(X, j_!𝒪_U) = 0`** on the spectrum of a local ring, `f` being in the maximal ideal: a
global section has zero germ at the closed point, so vanishes on an open containing it, which is
the whole space. -/
theorem subsingleton_globalSections {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A) :
    Subsingleton (ToType ((jO A f).val.presheaf.obj (op ⊤))) := by
  refine ⟨fun s t => ?_⟩
  have hz := isZero_stalk_x₀ A hf
  obtain ⟨W, hW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq (jO A f).val.presheaf (x₀ A)
    (Opens.mem_top _) (Opens.mem_top _) s t (by
      exact (AddCommGrpCat.subsingleton_of_isZero hz).elim _ _)
  obtain rfl := eq_top_of_x₀_mem A hW
  obtain rfl : iU = 𝟙 _ := Subsingleton.elim _ _
  obtain rfl : iV = 𝟙 _ := Subsingleton.elim _ _
  simp only [op_id, CategoryTheory.Functor.map_id] at e
  exact e

/-- The global sections functor `Γ(X, -)` on `𝒪_X`-modules. -/
noncomputable abbrev Γfun : ModuleSheaves (X A) ⥤ ModuleCat.{u}
    ((structureSheafRing (X A)).obj.obj (op ⊤)) :=
  SheafOfModules.evaluation (structureSheafRing (X A)) (op ⊤)

/-- **On the spectrum of a local ring, `Γ(X, -)` sends epimorphisms of `𝒪_X`-modules to
surjections**: the only open containing the closed point is `X`. -/
instance preservesEpimorphisms_Γfun : (Γfun A).PreservesEpimorphisms where
  preserves {_ _} φ _ := (ModuleCat.epi_iff_surjective _).2
    (surjective_evaluation_of_le A ⊤ (x₀ A) (Opens.mem_top _)
      (fun _ hV => (eq_top_of_x₀_mem A hV).ge) φ)

instance preservesFiniteColimits_Γfun : PreservesFiniteColimits (Γfun A) :=
  Stacks.SheafOfModules.LocalCokernel.finiteColimits_of_finiteLimits_epi _

/-- **On the spectrum of a local ring, `Hⁿ(X, M) = 0` for `n > 0` and every `𝒪_X`-module `M`**,
quasi-coherent or not: `Γ(X, -)` is exact. -/
@[montpellier "101, 10"]
theorem isZero_cohomology (M : ModuleSheaves (X A)) {n : ℕ} (hn : 0 < n) :
    IsZero (((Γfun A).rightDerived n).obj M) :=
  Functor.isZero_rightDerived_of_exact _ M n hn

/-- The closed point is closed. -/
lemma isClosed_x₀ : IsClosed ({x₀ A} : Set (X A)) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (IsLocalRing.maximalIdeal.isMaximal A)

open Stacks.Cohomology.SectionsWithSupport in
/-- The local cohomology `H^n_x(M)` at the closed point, the right derived functors of the sections
with support in `{x}`, for every `𝒪_X`-module `M`. -/
noncomputable abbrev Hx (n : ℕ) : ModuleSheaves (X A) ⥤ ModuleCat.{u}
    ((structureSheafRing (X A)).obj.obj (op ⊤)) :=
  (sectionsWithSupport (X A) {x₀ A} (isClosed_x₀ A)).rightDerived n

open Stacks.Cohomology.SectionsWithSupport in
/-- The cohomology `Hⁿ(X ∖ {x}, M)` of the punctured spectrum. -/
noncomputable abbrev HU (n : ℕ) : ModuleSheaves (X A) ⥤ ModuleCat.{u}
    ((structureSheafRing (X A)).obj.obj (op ⊤)) :=
  (sectionsOnComplement (X A) {x₀ A} (isClosed_x₀ A)).rightDerived n

open Stacks.Cohomology.SectionsWithSupport in
/-- **Local cohomology at the closed point is the cohomology of the punctured spectrum, shifted
by one**: on the spectrum of a local ring, for every `𝒪_X`-module `M` and `n ≥ 1`,
`Hⁿ(X ∖ {x}, M) ≅ Hⁿ⁺¹_x(M)`, and `H⁰_x(M) → Γ(X, M)` is injective. -/
theorem localCohomology_eq_punctured :
    (∀ M : ModuleSheaves (X A), Mono ((NatTrans.rightDerived
      (show sectionsWithSupport (X A) {x₀ A} (isClosed_x₀ A) ⟶ _ from
        kernel.ι (restrictionToComplement (X A) {x₀ A} (isClosed_x₀ A))) 0).app M)) ∧
    ∃ δ : ∀ n : ℕ, HU A n ⟶ Hx A (n + 1),
      (∀ M : ModuleSheaves (X A), ∀ n, 1 ≤ n → IsIso ((δ n).app M)) ∧
      ∀ M : ModuleSheaves (X A), IsZero (((Γfun A).rightDerived 0).obj M) →
        IsIso ((δ 0).app M) := by
  obtain ⟨δ, hmono, hex⟩ := longExact_rightDerived_sectionsWithSupport (X A) {x₀ A}
    (isClosed_x₀ A)
  refine ⟨hmono, δ, fun M n hn => ?_, fun M hM => ?_⟩
  · have h2 := (hex n M).exact 1
    have h3 := (hex n M).exact 2
    have hm : Mono ((δ n).app M) := h2.mono_g ((isZero_cohomology A M hn).eq_of_src _ _)
    have he : Epi ((δ n).app M) := h3.epi_f
      ((isZero_cohomology A M (by omega)).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  · have h2 := (hex 0 M).exact 1
    have h3 := (hex 0 M).exact 2
    have hm : Mono ((δ 0).app M) := h2.mono_g (hM.eq_of_src _ _)
    have he : Epi ((δ 0).app M) := h3.epi_f
      ((isZero_cohomology A M (by omega)).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _

/-- `R⁰Γ(X, j_!𝒪_U) = 0`. -/
theorem isZero_rightDerived_zero_jO {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A) :
    IsZero (((Γfun A).rightDerived 0).obj (jO A f)) := by
  have : Subsingleton ((Γfun A).obj (jO A f)) := subsingleton_globalSections A hf
  exact (ModuleCat.isZero_of_subsingleton _).of_iso
    ((Functor.rightDerivedZeroIsoSelf (Γfun A)).app _)

open Stacks.Cohomology.SectionsWithSupport in
/-- **Folder 101, page 10: the local cohomology of `F = j_!𝒪_U`.** On `X = Spec A`, `A` local,
`U = D(f)` with `f ∈ 𝔪`: `H⁰_x(F) = 0`, `H¹_x(F) ≅ Γ(X ∖ {x}, F)` and
`Hⁿ⁺¹_x(F) ≅ Hⁿ(X ∖ {x}, F)` for `n ≥ 1`, through the connecting maps of the long exact
sequence of sections with support. -/
@[montpellier "101, 10"]
theorem localCohomology_jO {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A) :
    IsZero ((Hx A 0).obj (jO A f)) ∧
    ∃ δ : ∀ n : ℕ, HU A n ⟶ Hx A (n + 1), ∀ n, IsIso ((δ n).app (jO A f)) := by
  obtain ⟨hmono, δ, hδ, hδ0⟩ := localCohomology_eq_punctured A
  refine ⟨?_, δ, fun n => ?_⟩
  · have := hmono (jO A f)
    exact (isZero_rightDerived_zero_jO A hf).of_mono
      ((NatTrans.rightDerived (show sectionsWithSupport (X A) {x₀ A} (isClosed_x₀ A) ⟶ _ from
        kernel.ι (restrictionToComplement (X A) {x₀ A} (isClosed_x₀ A))) 0).app (jO A f))
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hδ0 _ (isZero_rightDerived_zero_jO A hf)
    · exact hδ _ n hn

open Stacks.Cohomology.SectionsWithSupport in
instance preservesFiniteLimits_sectionsOnComplement :
    PreservesFiniteLimits (sectionsOnComplement (X A) {x₀ A} (isClosed_x₀ A)) := by
  constructor
  intro J _ _
  have : PreservesLimitsOfShape J (SheafOfModules.evaluation (structureSheafRing (X A))
    (op (openComplement {x₀ A} (isClosed_x₀ A)))) := inferInstance
  have : PreservesLimitsOfShape J (ModuleCat.restrictScalars.{u}
      ((structureSheafRing (X A)).obj.map
        (homOfLE (le_top : openComplement {x₀ A} (isClosed_x₀ A) ≤ ⊤)).op).hom) :=
    ⟨fun {_} => inferInstance⟩
  exact comp_preservesLimitsOfShape _ _

open Stacks.Cohomology.SectionsWithSupport in
/-- **Folder 101, page 10: `H¹_x(M)` is the cokernel of restriction to the punctured spectrum**,
`Γ(X, M) → Γ(X ∖ {x}, M)`, for every `𝒪_X`-module `M` on the spectrum of a local ring
(`H⁰_x(M)` is its kernel by definition). For a discrete valuation ring, `X ∖ {x}` is the generic
point and this is page 10's `H¹_x(F) = Coker u` for the triple `(Γ(X, F), F_η, u)`. -/
@[montpellier "101, 10"]
theorem nonempty_iso_cokernel (M : ModuleSheaves (X A)) :
    Nonempty ((Hx A 1).obj M ≅
      cokernel ((restrictionToComplement (X A) {x₀ A} (isClosed_x₀ A)).app M)) := by
  obtain ⟨δ, -, hex⟩ := longExact_rightDerived_sectionsWithSupport (X A) {x₀ A}
    (isClosed_x₀ A)
  have h2 := (hex 0 M).exact 1
  have hepi : Epi ((δ 0).app M) := ((hex 0 M).exact 2).epi_f
    ((isZero_cohomology A M (by omega)).eq_of_tgt _ _)
  let e₁ := (Functor.rightDerivedZeroIsoSelf (Γfun A)).app M
  let e₂ := (Functor.rightDerivedZeroIsoSelf
    (sectionsOnComplement (X A) {x₀ A} (isClosed_x₀ A))).app M
  have hnat := Functor.toRightDerivedZero_naturality_app
    (restrictionToComplement (X A) {x₀ A} (isClosed_x₀ A)) M
  refine ⟨(IsColimit.coconePointUniqueUpToIso (@ShortComplex.Exact.gIsCokernel _ _ _ _ _ h2 hepi)
    (colimit.isColimit _)) ≪≫
    cokernel.mapIso _ _ e₁ e₂ ?_⟩
  change (NatTrans.rightDerived (restrictionToComplement (X A) {x₀ A} (isClosed_x₀ A)) 0).app M
    ≫ e₂.hom = e₁.hom ≫ _
  rw [← cancel_epi e₁.inv]
  simp only [e₁, e₂, Functor.rightDerivedZeroIsoSelf_inv, Iso.app_inv, Iso.app_hom]
  rw [← Category.assoc, hnat, Category.assoc, Functor.rightDerivedZeroIsoSelf_inv_hom_id_app,
    Category.comp_id, Functor.rightDerivedZeroIsoSelf_inv_hom_id_app_assoc]

end Local

section DVR

variable [IsDomain A] [IsDiscreteValuationRing A]

open Stacks.Cohomology.SectionsWithSupport

/-- The generic point of `Spec A`. -/
abbrev η : (X A).carrier := ⟨⊥, inferInstance⟩

/-- For a discrete valuation ring, the punctured spectrum `X ∖ {x}` is the generic point. -/
lemma eq_η_of_mem {q : (X A).carrier} (hq : q ∈ openComplement {x₀ A} (isClosed_x₀ A)) :
    q = η A := by
  have hne : q.asIdeal ≠ IsLocalRing.maximalIdeal A := fun h =>
    hq (PrimeSpectrum.ext h)
  by_contra hqη
  have hbot : q.asIdeal ≠ ⊥ := fun h => hqη (PrimeSpectrum.ext h)
  exact hne (IsLocalRing.eq_maximalIdeal (q.2.isMaximal hbot))

lemma η_mem : η A ∈ openComplement {x₀ A} (isClosed_x₀ A) := by
  intro h
  have : (⊥ : Ideal A) = IsLocalRing.maximalIdeal A := congrArg PrimeSpectrum.asIdeal h
  exact IsDiscreteValuationRing.not_a_field A this.symm

instance preservesEpimorphisms_sectionsOnComplement :
    (sectionsOnComplement (X A) {x₀ A} (isClosed_x₀ A)).PreservesEpimorphisms where
  preserves {_ _} φ _ := (ModuleCat.epi_iff_surjective _).2
    (surjective_evaluation_of_le A _ (η A) (η_mem A)
      (fun _ hV q hq => by rw [eq_η_of_mem A hq]; exact hV) φ)

instance preservesFiniteColimits_sectionsOnComplement :
    PreservesFiniteColimits (sectionsOnComplement (X A) {x₀ A} (isClosed_x₀ A)) :=
  Stacks.SheafOfModules.LocalCokernel.finiteColimits_of_finiteLimits_epi _

/-- **Folder 101, page 10, for every `𝒪_X`-module: local cohomology lives in degrees `0` and
`1`.** On `X = Spec A`, `A` a discrete valuation ring, `Hⁱ_x(F) = 0` for `i ≥ 2` and every
`𝒪_X`-module `F`, quasi-coherent or not: `Hⁱ_x(F) ≅ Hⁱ⁻¹(X ∖ {x}, F)`, and `X ∖ {x}` is
the generic point, on which sections are exact. -/
@[montpellier "101, 10"]
theorem isZero_localCohomology_of_two_le (M : ModuleSheaves (X A)) {i : ℕ} (hi : 2 ≤ i) :
    IsZero ((Hx A i).obj M) := by
  obtain ⟨-, δ, hδ, -⟩ := localCohomology_eq_punctured A
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have := hδ M n (by omega)
  exact (Functor.isZero_rightDerived_of_exact _ M n (by omega)).of_iso
    (asIso ((δ n).app M)).symm

end DVR

end Grothendieck.Folder101Sheaf
