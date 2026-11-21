module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.Basic
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.SerreFiniteness
public import StacksFrontier.AlgebraicGeometry.Properties.RelativeAmpleExternalTensorProduct
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.ProjIso
public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.Proper
public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.ChartSections

/-!
# Relatively ample invertible sheaves

Let `f : X ⟶ Y` be a morphism of schemes. An invertible sheaf `L` on `X` is *`f`-ample* if every
point of `Y` has an affine open neighbourhood `V` such that the restriction of `L` to `f⁻¹(V)` is
ample. For an open `U ⊆ Y`, `L` is *ample over `U`* if `L|_{f⁻¹(U)}` is ample relative to the
restriction `f|_{f⁻¹(U)} : f⁻¹(U) ⟶ U`.

A Cartier divisor `D` is `f`-ample when its invertible sheaf `𝒪_X(D)` is.

## Main definitions

* `MMP.Mori.IsRelativelyAmple`: `L` is `f`-ample.
* `MMP.Mori.IsAmpleOver`: `L` is ample over an open `U` of the base.

## Main results

* `MMP.Mori.isRelativelyAmple_iff`, `MMP.Mori.isAmpleOver_iff`: the defining conditions.
* `MMP.Mori.IsRelativelyAmple.of_stacks`: ampleness relative to `f` in the sense of Stacks
  Tag 01VH (ampleness over every affine open of the base) implies `f`-ampleness.

## Implementation notes

The definition is stated for an invertible sheaf rather than for a Cartier divisor, so that
`f`-ampleness of a Cartier divisor `D` is this predicate applied to `𝒪_X(D)`.
Ampleness is `Stacks.Ample.IsAmple` (Stacks Tag 01PS) and invertibility is
`Stacks.Ample.IsInvertibleModule`, the spellings `Stacks.RelativeAmple.IsRelativelyAmple` uses.
The restriction of `L` to an open subscheme `W` is the module pull-back along the open immersion
`W.ι`, which is invertible by Stacks Tag 0B8L.

The definition is the local form: some affine neighbourhood of each point. Stacks Tag 01VH asks
for every affine open of the base together with quasi-compactness of `f`; that form implies this
one (`MMP.Mori.IsRelativelyAmple.of_stacks`). The converse is Stacks Tag 01VJ.

The Stacks form is preserved by the operations used downstream, which are taken from the library
directly: external tensor products over the base (Stacks Tag 0DNK,
`Stacks.AmpleExternalTensor.isRelativelyAmple_externalTensor`), tensor products along a
pull-back square (`Stacks.AmpleExternalTensor.isRelativelyAmple_tensorModules_of_isPullback`),
and pull-back along an affine morphism
(`Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom`).
The relative Proj of the direct-image algebra `⊕ₙ f_* L^{⊗n}` and the canonical morphism
`Stacks.RelativeAmple.relativeAmpleProjHom` to it, which recovers `X` for proper `f`
(Stacks Tag 0C6J), are imported here as well, together with the absolute counterparts for the
section ring `⊕ₙ Γ(X, L^{⊗n})`: it is of finite type over a Noetherian ring `R` when `L` is
ample and `X` is proper over `Spec R`
(Stacks Tag 0B5T, `Stacks.AlgebraicGeometry.ProperAmpleCohomology.ringHomFiniteType_sectionRing`),
the isomorphism of `X` with its `Proj` for proper `X`
(Stacks Tag 0EKI, `Stacks.SectionRingProjIso.isIso_projHomOfIsAmple_of_isProper`), and the
description of that morphism on the standard charts (Stacks Tag 01PZ,
`Stacks.SectionRingProjQuasicoherent.awayToSection_comp_projHomOfIsAmple_app`).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Proposition 1.41,
  Theorem 1.42]
* [R. Hartshorne, *Algebraic geometry*, II.7]
* [EGA II, 4.6]
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace MMP.Mori

/-- An invertible sheaf `L` on `X` is *ample relative to* `f : X ⟶ Y` (`f`-ample) if every point
of `Y` has an affine open neighbourhood `V` such that the restriction of `L` to `f⁻¹(V)` is
ample. -/
@[mmp "def_km1b_relatively_ample"]
def IsRelativelyAmple {X Y : Scheme.{u}} (f : X ⟶ Y) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] : Prop :=
  ∀ y : Y, ∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V ∧
    Stacks.Ample.IsAmple (f ⁻¹ᵁ V).toScheme
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L)

/-- An invertible sheaf `L` on `X` is *ample over* an open `U` of `Y` if its restriction to
`f⁻¹(U)` is ample relative to the restriction `f ∣_ U : f⁻¹(U) ⟶ U` of `f`. -/
@[mmp "def_km1b_relatively_ample"]
def IsAmpleOver {X Y : Scheme.{u}} (f : X ⟶ Y) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (U : Y.Opens) : Prop :=
  IsRelativelyAmple (f ∣_ U) ((modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj L)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- The defining condition of `f`-ampleness. -/
theorem isRelativelyAmple_iff :
    IsRelativelyAmple f L ↔ ∀ y : Y, ∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V ∧
      Stacks.Ample.IsAmple (f ⁻¹ᵁ V).toScheme
        ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) := Iff.rfl

/-- The defining condition of ampleness over an open of the base. -/
theorem isAmpleOver_iff (U : Y.Opens) :
    IsAmpleOver f L U ↔
      IsRelativelyAmple (f ∣_ U) ((modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj L) :=
  Iff.rfl

/-- Ampleness relative to `f` in the sense of Stacks Tag 01VH (`f` quasi-compact and `L` ample
over the preimage of every affine open) implies `f`-ampleness. -/
theorem IsRelativelyAmple.of_stacks (h : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    IsRelativelyAmple f L := by
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  exact ⟨V, hV, hyV, h.isAmple_preimage f L V hV⟩

end MMP.Mori
