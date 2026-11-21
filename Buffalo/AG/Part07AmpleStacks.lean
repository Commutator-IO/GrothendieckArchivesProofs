import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basis
import StacksFrontier.AlgebraicGeometry.AmplePositivePower.Basic
import StacksFrontier.AlgebraicGeometry.AmplePullbackDatum.Basic
import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
import StacksFrontier.AlgebraicGeometry.QuasiProjective.BaseChange
import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase
import StacksFrontier.AlgebraicGeometry.RelativeAmple.VeryAmple
import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
import StacksFrontier.AlgebraicGeometry.RelativelyAmple.Separated

/-!
# Buffalo, algebraic geometry, part 07: ℙ(E), ample and very ample invertible sheaves

The index entries of the topics « Projective and ample morphisms », « Quasi-projective and proper
morphisms » and « Ample sheaves » (and their echoes in parts 01, 04, 05, 08, 09), stated with the
definitions of the AxiomMath/Stacks project (pinned in `lakefile.toml`, Apache-2.0):

* an invertible `𝒪_X`-module is `L : X.Modules` with `Stacks.Ample.IsInvertibleModule X L`;
* `L` is ample (`Stacks.Ample.IsAmple X L`, Stacks 01PS, EGA II 4.5.3) when `X` is quasi-compact
  and every point lies in an affine `X_s`, `s ∈ Γ(X, L^{⊗ n})`, `n ≥ 1`;
* `L` is ample relative to `f : X ⟶ S` (`Stacks.RelativeAmple.IsRelativelyAmple f L`, Stacks
  01VH, EGA II 4.6.1) when `f` is quasi-compact and `L` is ample over `f⁻¹(V)` for every affine
  open `V ⊆ S`;
* `L` is very ample relative to `f` (`Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L`, Stacks
  01VM, EGA II 4.4.2) when there are a quasi-coherent `E` on `S` and an `S`-immersion
  `i : X ⟶ ℙ(E) = Proj_S(Sym E)` with `L ≅ i^* 𝒪_{ℙ(E)}(1)`;
* `f` is quasi-projective (`AlgebraicGeometry.IsQuasiProjective f`, Stacks 01VW, EGA II 5.3.1)
  when it is of finite type and some invertible sheaf on `X` is ample relative to `f`. This is
  Grothendieck's definition 27285.

Grothendieck's « coherent » scheme is a quasi-compact quasi-separated one.

**What is proved.**
* `def_27285`: the definition of a quasi-projective morphism (Stacks 01VW).
* `prop_27544`: quasi-projective morphisms are stable under base change (Stacks 0B3G); the
  projective half is not stated.
* `prop_32075`: a morphism carrying a relatively ample invertible sheaf is separated (Stacks 01VI,
  EGA II 4.6.3).
* `prop_25928`: a morphism carrying a relatively very ample invertible sheaf is separated (Stacks
  01VQ); the choice of `E` of finite type is not formalised.
* `prop_32333`: for `f` quasi-compact, a relatively very ample sheaf is relatively ample (Stacks
  01VN, the case `n = 1`); `prop_31756`: over an affine base, if `L^{⊗ n}` (`n ≥ 1`) is very
  ample relative to `f`, then `L` is ample, absolutely and relative to `f` (Stacks 01VN, 01VK,
  01PT). The converses (`f` of finite type) are not formalised.
* `prop_26840`: for `n ≥ 1`, `L` is ample if and only if `L^{⊗ n}` is (Stacks 01PT, EGA II 4.5.6);
  stability under base change and tensor product is not formalised.
* `prop_27098`: over an affine base, `𝒪_X` is ample relative to `f` if and only if `X` is
  quasi-affine (Stacks 01VK, 01QE); `prop_33470_ample`: `X` is quasi-affine if and only if `𝒪_X`
  is ample (Stacks 01QE, the clause of 33470 that was missing). The quasi-compact non-affine base
  and the proper ⇒ finite clause are not formalised.
* `prop_31422`: the `X_s`, `s ∈ Γ(X, L^{⊗ n})`, `n ≥ 1`, form a base of the topology if and only
  if the affine ones do (Stacks 01PX; the converse is immediate).
* `def_32012`: for `f` quasi-compact, `L` is ample relative to `f` if and only if `S` is covered
  by affine opens over which `L` is ample, so ampleness over one affine covering gives it over
  every affine open (Stacks 01VJ, EGA II 4.6.4); `def_32012_affine`: over an affine base,
  relative ampleness is ampleness (Stacks 01VK, EGA II 4.6.6).
* `prop_32398`: absolute case of 32398 (`Z` affine, ample on `Y`): if `L` is ample relative to
  `f : X ⟶ Y` and `M` is ample on `Y`, then `L ⊗ f^* M^{⊗ a}` is ample for `a` large (Stacks
  0892 (1)); the relative and the very ample versions are not formalised.
* Part 09, entry 19516 (inverse image along quasi-affine morphisms): `Part09AmpleStacks.lean`.

**Not formalised.** (status suggested for the Buffalo index in brackets)
* Part 07: 25093 [def, ℙ(E) of a finite type module: AxiomMath/Stacks has `relativeProj` of
  `Sym E` but not the naive projective morphism], 25350 [base change of ℙ(E): not formalised],
  25477, 25603, 33188 [counterexamples: not constructed], 25734 [universal property of ℙ(E):
  not stated here], 25800 [def: Stacks 01VM, stated above as the predicate used, not restated],
  26255, 27481 [immersions into ℙ(E) of finite type: not formalised], 26447 [base change of very
  ample sheaves: Stacks 0B3F exists but its import closure is about 2,500 further modules],
  26511, 32732 [Segre: not formalised], 26648 [Stacks 01VU, closure too large], 27035, 27219
  [ample cone: not formalised], 31560 [Stacks 01Q3 clauses (5)-(8): closure of about 470 further
  modules, left out], 31946 [def: Stacks 01PS, the predicate used], 32204 [not formalised], 32997
  [ℙ(E ⊗ I): not formalised], 33600 [not formalised], 28486 [Chow: not formalised].
* Part 07, already partial and not changed here: 25222, 28411, 28613, 30771, 30835, 30898.
* Parts 01, 04, 05: 17536, 24233, 28043, 28112, 29283 [ℙ(M) as a functor of invertible quotients:
  not formalised]; 32636, 32959, 33086 unchanged.
* Parts 08, 09: 13514, 14220, 15139, 15264, 18219, 18281, 18420, 18808, 18872, 19653, 24670, 24799,
  20037 [relative ampleness and descent data: not formalised].
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Buffalo.AG.Part07

/-- Oqhr-Gt66es-27285 (7:34:45) [def] `f : X → Y` is quasi-projective if it is of finite type and
there is an invertible sheaf on `X` ample relative to `Y` (Stacks tag 01VW, EGA II 5.3.1). -/
theorem def_27285 {X S : Scheme.{u}} (f : X ⟶ S) :
    IsQuasiProjective f ↔ ((LocallyOfFiniteType f ∧ QuasiCompact f) ∧
      ∃ L : X.Modules, ∃ hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
          X.ringCatSheaf.2 L,
        letI : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
        Stacks.RelativeAmple.IsRelativelyAmple f L) :=
  isQuasiProjective_iff

/-- Oqhr-Gt66es-27544 (7:39:04) [prop] (quasi-projective half) Quasi-projective morphisms are
stable under base change (Stacks tag 0B3G). -/
theorem prop_27544 {X S X' S' : Scheme.{u}} {p : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S}
    {g : S' ⟶ S} (hsq : IsPullback p f' f g) (hf : IsQuasiProjective f) :
    IsQuasiProjective f' :=
  IsQuasiProjective.of_isPullback hsq hf

/-- Oqhr-Gt66es-32075 (8:54:35) [prop] If there is an invertible sheaf ample relative to `Y`,
then `X` is separated over `Y` (Stacks tag 01VI, EGA II 4.6.3). -/
theorem prop_32075 {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) : IsSeparated f :=
  AlgebraicGeometry.Scheme.Modules.IsRelativelyAmple.isSeparated hL

/-- Oqhr-Gt66es-25928 (7:12:08) [prop] (first half) If `X` has a sheaf very ample relative to
`Y`, then `X` is separated over `Y` (Stacks tag 01VQ, EGA II 4.4.2). -/
theorem prop_25928 {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L) : IsSeparated f := by
  obtain ⟨E, hE, i, hi, rfl, -⟩ := hL
  have := hE
  have hsep := Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase _
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E))
  infer_instance

/-- Oqhr-Gt66es-32333 (8:58:53) [prop] (the case `n = 1`) For `f` quasi-compact, an invertible
sheaf very ample relative to `Y` is ample relative to `Y` (Stacks tag 01VN, EGA II 4.6.2). -/
theorem prop_32333 {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hf : QuasiCompact f)
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple f L hf hL

/-- Oqhr-Gt66es-31756 (8:49:16) [prop] (first half) If `X` is quasi-compact over an affine
`Y = Spec A` and `L^{⊗ n}` is very ample relative to `Y` for some `n > 0`, then `L` is ample,
absolutely and relative to `Y` (Stacks tags 01VN, 01VK, 01PT). -/
theorem prop_31756 {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hf : QuasiCompact f) (n : ℕ) (hn : 1 ≤ n)
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f
      (Stacks.Ample.tensorPowModule X L (n : ℤ))) :
    Stacks.Ample.IsAmple X L ∧ Stacks.RelativeAmple.IsRelativelyAmple f L := by
  have h1 := Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple f _ hf hL
  rw [Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple] at h1
  have h2 : Stacks.Ample.IsAmple X L :=
    (Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule L n hn).2 h1
  exact ⟨h2, (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).2 h2⟩

/-- Oqhr-Gt66es-26840 (7:27:20) [prop] (last clause) For `n > 0`, `L` is ample if and only if
`L^{⊗ n}` is (Stacks tag 01PT, EGA II 4.5.6 (i)). -/
theorem prop_26840 {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (n : ℕ) (hn : 1 ≤ n) :
    Stacks.Ample.IsAmple X L ↔
      Stacks.Ample.IsAmple X (Stacks.Ample.tensorPowModule X L (n : ℤ)) :=
  Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule L n hn

/-- Oqhr-Gt66es-27098 (7:31:38) [prop] (first half, `Y` affine) `𝒪_X` is ample relative to `Y`
if and only if `X` is quasi-affine (Stacks tags 01VK, 01QE). -/
theorem prop_27098 {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) :
    Stacks.RelativeAmple.IsRelativelyAmple f (Stacks.Ample.unitModule X) ↔ X.IsQuasiAffine :=
  (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f _).trans
    (Stacks.Ample.isQuasiAffine_iff_isAmple X).symm

/-- Oqhr-Gt66es-33470 (9:17:50) [prop] (the clause « `𝒪_X` is ample ») `X` is quasi-affine if and
only if `𝒪_X` is ample (Stacks tag 01QE, EGA II 5.1.2). -/
theorem prop_33470_ample (X : Scheme.{u}) :
    X.IsQuasiAffine ↔ Stacks.Ample.IsAmple X (Stacks.Ample.unitModule X) :=
  Stacks.Ample.isQuasiAffine_iff_isAmple X

/-- Oqhr-Gt66es-31422 (8:43:42) [prop] For `L` invertible, the `X_s`, `s ∈ Γ(X, L^{⊗ n})`,
`n > 0`, form a base of the topology if and only if those that are affine do (Stacks tag 01PX;
no coherence hypothesis is needed). -/
theorem prop_31422 (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    Opens.IsBasis
      {U : X.Opens | ∃ n : ℕ, 1 ≤ n ∧
        ∃ s : (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
          U = Stacks.SheafOfModules.nonvanishingOpen
            (X := X.toLocallyRingedSpace.toRingedSpace)
            (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s} ↔
    Opens.IsBasis
      {U : X.Opens | (∃ n : ℕ, 1 ≤ n ∧
        ∃ s : (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
          U = Stacks.SheafOfModules.nonvanishingOpen
            (X := X.toLocallyRingedSpace.toRingedSpace)
            (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) ∧
          IsAffineOpen U} := by
  refine ⟨AlgebraicGeometry.Scheme.Modules.isBasis_affine_nonvanishingOpens X L, fun h => ?_⟩
  rw [Opens.isBasis_iff_nbhd] at h ⊢
  intro U x hx
  obtain ⟨U', hU', hxU', hle⟩ := h hx
  exact ⟨U', hU'.1, hxU', hle⟩

/-- Oqhr-Gt66es-32012 (8:53:32) [def] For `f` quasi-compact, `L` is ample relative to `Y` (over
every affine open of `Y`) if and only if `Y` is covered by affine opens `Y_i` with `L` ample on
`f⁻¹(Y_i)` (Stacks tag 01VJ, EGA II 4.6.4). -/
theorem def_32012 {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hf : QuasiCompact f) :
    Stacks.RelativeAmple.IsRelativelyAmple f L ↔
      ∀ x : S, ∃ V : S.Opens, IsAffineOpen V ∧ x ∈ V ∧
      Stacks.Ample.IsAmple (f ⁻¹ᵁ V).toScheme
        (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V).ι L) :=
  Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover f L hf

/-- Oqhr-Gt66es-32012 (8:53:32) [def] (complement) Over an affine base, ampleness relative to
`Y` is ampleness (Stacks tag 01VK, EGA II 4.6.6). -/
theorem def_32012_affine {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    Stacks.RelativeAmple.IsRelativelyAmple f L ↔ Stacks.Ample.IsAmple X L :=
  Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L

/-- Oqhr-Gt66es-32398 (8:59:58) [prop] (ample case, `Z` affine and absolute ampleness on `Y`) If
`L` is ample relative to `f : X → Y` and `M` is ample on `Y`, then
`L ⊗ f^* M^{⊗ a}` (`Stacks.AmplePullbackPart1.tensorPullbackPowModule f L M a`) is ample for all
`a ≥ n₀` (Stacks tag 0892 (1)). -/
theorem prop_32398 {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) (M : S.Modules)
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule S M]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (hM : Stacks.Ample.IsAmple S M) :
    ∃ n₀ : ℕ, ∀ a : ℕ, n₀ ≤ a →
      Stacks.Ample.IsAmple X (Stacks.AmplePullbackPart1.tensorPullbackPowModule f L M a) :=
  Stacks.AmplePullbackDatum.exists_threshold_isAmple f L M hL hM

end Buffalo.AG.Part07
