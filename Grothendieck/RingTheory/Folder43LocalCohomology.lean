/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import StacksFrontier.RingTheory.CohenMacaulay.Witnesses
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.BelowDepth
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.MaximalIdeal
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
import Grothendieck.Attr

/-!
# Folder 43, pages 70–74: the local cohomology of `𝔾_a` on a regular local ring

Finding `43-local-cohomology-concentration` (issue Commutator-IO/grothendieck-project#247). For
a regular local ring `A` of dimension `d` containing an algebraically closed field `k` and a
commutative algebraic group `G` over `k`, pages 70–73 show that the local cohomology
`H^i_a(Spec A, G)` at the closed point `a` vanishes for `i ≠ d`. The argument dévisses `G`: the
abelian quotient gives a flasque sheaf, `𝔾_m` drops out because `A` is factorial, and the
unipotent part is dévissé to `𝔾_a`, for which the page uses that `H^i_𝔪(A)` vanishes for
`i ≠ d` (page 72, « `H^i(Spec A − a, 𝔾_a) = H^{i+1}_𝔪(A)` vanishes outside `i = d − 1` »).

This file proves that last input, the case `G = 𝔾_a`, for every regular local ring: no field
`k` and no hypothesis on the residue field are needed.

## Main results

* `isZero_localCohomology_of_ne`: for `A` regular local of Krull dimension `d`, the local
  cohomology `H^i_𝔪(A)` vanishes for every integer `i ≠ d`, in the model of local cohomology
  of [Stacks, Tag 0A6Q] (`Stacks.LocalCohomology.localCohomologyModule`);
* `isZero_localCohomologyWithSupportIn_of_ne`: the same in the model of the right derived
  functor of sections with support in `V(𝔪)` (the two agree, [Stacks, Tag 0955]).

## Implementation notes

`A` is Cohen–Macaulay (`IsRegularLocalRing.isCohenMacaulayLocalRing`, EGA 0 17.1.3), so its
depth along `𝔪` is `d`; local cohomology vanishes below the depth ([Stacks, Tag 0AVZ],
`Stacks.LocalCohomology.isZero_localCohomology_of_lt_depth`) and above the dimension
(`Stacks.LocalCohomology.isZero_localCohomologyModule_of_zeroLocus_eq_maximalIdeal`, from
Krull's height theorem). The first is stated for the derived sections with support, the second
for the coreflection model; `localCohomologyWithSupportInIsoLocalCohomologyModule` passes from
one to the other over a Noetherian ring.

`H^i_𝔪(A)` is the local cohomology of the module `A`. The page's `H^i_a(Spec A, 𝔾_a)` is the
Zariski cohomology with support in `{a}` of the sheaf `𝒪_X`; the two agree for quasi-coherent
sheaves, a comparison the libraries do not have in this generality
(`Stacks.LocalCohomologyTilde.rightDerivedCohomologyWithSupportTildeIso` assumes that `M ↦ M̃`
sends injective modules to injective sheaves), so the statement is given for the module.

## Not formalised

The other groups `G`: the reduction to `𝔾_a`, `𝔾_m` and abelian varieties needs the structure
of commutative algebraic groups (Chevalley, the unipotent part and its composition series),
which neither library has; the vanishing of `H^i(Spec A − a, 𝔾_m)` (factoriality and the
Gersten resolution); the formulas `H^1_a = G(K)/G(A)` for `d = 1` and
`H^d_a(G) = H^{d−1}(Spec A − a, U)` for `d ≥ 2`; the non-vanishing of `H^d_𝔪(A)`; the exactness
of `G ↦ H^d_a(G)` and the local Jacobian of page 74.

## References

* A. Grothendieck, folder 43, pp. 70–74 (finding `43-local-cohomology-concentration`)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Grothendieck.Folder43

variable (A : Type u) [CommRing A] [IsRegularLocalRing A] {d : ℕ}

/-- **Page 72, `H^i_𝔪(A) = 0` for `i ≠ d`**, the case `G = 𝔾_a` of the concentration of
pages 70–73: for a regular local ring `A` of Krull dimension `d`, the local cohomology of `A`
at the closed point vanishes in every degree `i ≠ d` (coreflection model of Stacks 0A6Q). No
field is needed. -/
@[montpellier "43, 70–73"]
theorem isZero_localCohomology_of_ne (hd : ringKrullDim A = d) (i : ℤ) (hi : i ≠ d) :
    IsZero (localCohomologyModule A (maximalIdeal A) (IsNoetherian.noetherian _)
      (ModuleCat.of A A) i) := by
  rcases lt_or_gt_of_ne hi with hi | hi
  · refine (isZero_localCohomology_of_lt_depth.{u, u} (maximalIdeal A) (ModuleCat.of A A)
      (by simpa using (maximalIdeal.isMaximal A).ne_top) d ?_ i hi).of_iso
      (localCohomologyWithSupportInIsoLocalCohomologyModule A _ _ _ i).symm
    exact_mod_cast (((isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay A).1
      (IsRegularLocalRing.isCohenMacaulayLocalRing A)).trans hd).ge
  · exact isZero_localCohomologyModule_of_zeroLocus_eq_maximalIdeal A _ _ rfl hd.le _ i hi

/-- `isZero_localCohomology_of_ne` for the local cohomology computed as the right derived
functor of the sections with support in `V(𝔪)`. -/
@[montpellier "43, 70–73"]
theorem isZero_localCohomologyWithSupportIn_of_ne (hd : ringKrullDim A = d) (i : ℤ)
    (hi : i ≠ d) :
    IsZero (localCohomologyWithSupportIn.{u, u} A
      (PrimeSpectrum.zeroLocus (maximalIdeal A : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) i) :=
  (isZero_localCohomology_of_ne A hd i hi).of_iso
    (localCohomologyWithSupportInIsoLocalCohomologyModule A _ (IsNoetherian.noetherian _) _ i)

end Grothendieck.Folder43
