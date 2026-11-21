module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentIffFinitePresentation
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

@[expose] public section

/-!
# Buffalo, algebraic geometry, part 07 (a): coherent `𝒪_X`-modules on a scheme

`Part07a.lean` has the entries `22510` (definition of a coherent module) and `22572` (Serre:
coherent modules are stable under finite sums, kernels, cokernels, images and extensions) only in
module form, over a ring. Here they are stated for sheaves of modules on a scheme `X`, that is for
Mathlib's `X.Modules`.

**What is proved.**
* `def_22510_scheme`: an `𝒪_X`-module `M` is coherent (Stacks tag 01BV, EGA 0 5.3.7) if and only
  if it is of finite type and, for every open `U` and every finite free module `𝒪_U^I`, the
  kernel of every morphism `𝒪_U^I → M|_U` is of finite type.
* `thm_22572_scheme`: the coherent `𝒪_X`-modules form a weak Serre subcategory of `X.Modules`
  (Stacks 01BY): they contain `0`, are closed under isomorphisms, finite direct sums, kernels,
  cokernels, images and extensions.
* `structureSheaf_isCoherent_22510` and `isCoherent_iff_of_isLocallyNoetherian_22510`: on a
  locally noetherian scheme `𝒪_X` is coherent, and a module is coherent if and only if it is
  quasi-coherent of finite type, if and only if it is of finite presentation (Stacks 01XZ);
  `isCoherent_iff_isFinitePresentation_22510`: whenever `𝒪_X` is coherent, coherent means of
  finite presentation (Stacks 01BZ).

**How.** Mathlib defines `X.Modules` as `SheafOfModules X.ringCatSheaf`, where
`X.ringCatSheaf` is a sheaf of rings on the site of opens of `X`; this is exactly the ringed
space on which the vendored AxiomMath/Stacks files
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/{Coherent, CoherentWeakSerre, CoherenceClosure,
CoherentIffFinitePresentation}.lean` and `StacksFrontier/AlgebraicGeometry/CoherenceCriteria/
Basic.lean` (Apache-2.0, see `lean/Stacks/NOTICE.md`) state coherence
(`Stacks.SheafOfModules.IsCoherent`). The glue is the instantiation `R := X.ringCatSheaf`; the
abelian structure of `X.Modules` is that of `SheafOfModules X.ringCatSheaf`, so kernels,
cokernels and images below are those of `X.Modules`. The image is the kernel of the cokernel.

**Not formalised.** The restriction `M|_U` is the restriction `M.over U` to the slice site of the
opens of `X` contained in `U`, not Mathlib's `M.restrict U.ι` on the open subscheme `U`; the two
are identified by `Scheme.Modules.overFunctorEquiv` and `Scheme.Modules.overEquiv`, but the
transport of finite type and of free modules along that equivalence is not written here.
-/

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace Buffalo.AG.Part07

variable {X : Scheme.{u}}

/-- Oqhr-Gt66es-22510 (6:15:10) [def] (on a scheme) An `𝒪_X`-module `M` is coherent if it is of
finite type and, for every open `U` and every finite `I`, the kernel of every morphism
`𝒪_U^I → M|_U` is of finite type (Stacks tag 01BV, EGA 0 5.3.7). -/
theorem def_22510_scheme (M : X.Modules) :
    Stacks.SheafOfModules.IsCoherent M ↔ M.IsFiniteType ∧
      ∀ (U : X.Opens) (I : Type u) [Finite I]
        (φ : (SheafOfModules.free I : SheafOfModules.{u} (X.ringCatSheaf.over U)) ⟶ M.over U),
        (kernel φ).IsFiniteType :=
  ⟨fun h => ⟨h.isFiniteType, fun U I hI φ => h.kernel_isFiniteType U I hI φ⟩,
    fun h => ⟨h.1, fun U I _ φ => h.2 U I φ⟩⟩

/-- Oqhr-Gt66es-22572 (6:16:12) [thm] (Serre, on a scheme) The coherent `𝒪_X`-modules form a weak
Serre subcategory of `X.Modules`: they are stable under finite direct sums, kernels, cokernels,
images and extensions (Stacks tag 01BY). -/
theorem thm_22572_scheme :
    (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).IsWeakSerreClass ∧
    (∀ {J : Type u} [Finite J] (F : J → X.Modules),
      (∀ j, Stacks.SheafOfModules.IsCoherent (F j)) →
        Stacks.SheafOfModules.IsCoherent (∐ F)) ∧
    (∀ {M N : X.Modules} (φ : M ⟶ N), Stacks.SheafOfModules.IsCoherent M →
      Stacks.SheafOfModules.IsCoherent N →
      Stacks.SheafOfModules.IsCoherent (kernel φ) ∧
      Stacks.SheafOfModules.IsCoherent (cokernel φ) ∧
      Stacks.SheafOfModules.IsCoherent (Abelian.image φ)) ∧
    (∀ S : ShortComplex X.Modules, S.ShortExact → Stacks.SheafOfModules.IsCoherent S.X₁ →
      Stacks.SheafOfModules.IsCoherent S.X₃ → Stacks.SheafOfModules.IsCoherent S.X₂) := by
  refine ⟨inferInstance, fun F hF => Stacks.SheafOfModules.isCoherent_sigma F hF,
    fun φ hM hN => ?_,
    fun _ hS h₁ h₃ => Stacks.SheafOfModules.isCoherent_X₂_of_shortExact hS h₁ h₃⟩
  have hc : Stacks.SheafOfModules.IsCoherent (cokernel φ) :=
    (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).prop_cokernel φ hM hN
  exact ⟨(Stacks.SheafOfModules.coherentModules X.ringCatSheaf).prop_kernel φ hM hN, hc,
    (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).prop_kernel (cokernel.π φ) hN hc⟩

/-- Oqhr-Gt66es-22510 (6:15:10) [def] (complement, Stacks tag 01BZ) When `𝒪_X` is coherent, an
`𝒪_X`-module is coherent if and only if it is of finite presentation. -/
theorem isCoherent_iff_isFinitePresentation_22510 (M : X.Modules)
    [Stacks.SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf)] :
    Stacks.SheafOfModules.IsCoherent M ↔ M.IsFinitePresentation :=
  Stacks.SheafOfModules.isCoherent_iff_isFinitePresentation X.ringCatSheaf M

/-- Oqhr-Gt66es-22510 (6:15:10) [def] (complement, Stacks tag 01XZ) On a locally noetherian scheme
the structure sheaf `𝒪_X` is coherent. -/
theorem structureSheaf_isCoherent_22510 [IsLocallyNoetherian X] :
    Stacks.SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent'_of_isCoherent
    (Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X)

/-- Oqhr-Gt66es-22510 (6:15:10) [def] (complement, Stacks tag 01XZ) On a locally noetherian scheme
an `𝒪_X`-module is coherent if and only if it is quasi-coherent of finite type, if and only if it
is of finite presentation. -/
theorem isCoherent_iff_of_isLocallyNoetherian_22510 [IsLocallyNoetherian X] (F : X.Modules) :
    (Stacks.SheafOfModules.IsCoherent F ↔ F.IsQuasicoherent ∧ F.IsFiniteType) ∧
    (Stacks.SheafOfModules.IsCoherent F ↔ F.IsFinitePresentation) := by
  have h := Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X F
  have e : Stacks.SheafOfModules.IsCoherent F ↔ _ :=
    ⟨Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isCoherent',
      Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent'_of_isCoherent⟩
  exact ⟨e.trans (h.out 1 2), e.trans (h.out 1 3)⟩

/-- Oqhr-Gt66es-22510 (6:15:10) (on the open subscheme) Finite type restricts to an open
subscheme: if `M` is of finite type, so is `M|_U = M.restrict U.ι` on the scheme `U` (Stacks 01B6,
through `Scheme.Modules.restrictFunctorIsoPullback`). -/
theorem isFiniteType_restrict_22510 (M : X.Modules) [M.IsFiniteType] (U : X.Opens) :
    (M.restrict U.ι).IsFiniteType :=
  Stacks.SheafOfModules.isFiniteType_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M)

/-- Oqhr-Gt66es-22510 (6:15:10) (on the open subscheme) On a locally noetherian scheme, a coherent
module restricts to a coherent module on every open subscheme `U`, for `M|_U = M.restrict U.ι`
on the scheme `U`. -/
theorem isCoherent_restrict_22510 [IsLocallyNoetherian X] (M : X.Modules)
    (hM : Stacks.SheafOfModules.IsCoherent M) (U : X.Opens) :
    Stacks.SheafOfModules.IsCoherent (M.restrict U.ι) := by
  obtain ⟨hq, hf⟩ := (isCoherent_iff_of_isLocallyNoetherian_22510 M).1.1 hM
  have : (M.restrict U.ι).IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.restrictFunctor U.ι).obj M).IsQuasicoherent
  have : (M.restrict U.ι).IsFiniteType := isFiniteType_restrict_22510 M U
  exact (isCoherent_iff_of_isLocallyNoetherian_22510 (X := U) (M.restrict U.ι)).1.2
    ⟨inferInstance, inferInstance⟩

end Buffalo.AG.Part07
