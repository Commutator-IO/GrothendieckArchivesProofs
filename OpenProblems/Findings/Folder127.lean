/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib
public import StacksFrontier.RingTheory.GeometricallyNormal.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
import Grothendieck.Attr

/-!
# Folder 127: flatness of a schematic closure, stated as propositions

Three open rows of the edition's list of findings (`src/content/findings.ts`) for folder 127
(*critère valuatif de platitude d'une adhérence schématique*, and Hironaka's flatness over a
reduced base): `127-closure-flatness-artinian-or-trait`, `127-non-flat-descent-artinian-epimorphism`
and `127-hironaka-reduced-base-openness`. Nothing here is proved; a `def … : Prop` asserts
nothing. The second is proved elsewhere (below).

## Main definitions

* `ClosureFlatnessArtinianOrTrait` (`127-closure-flatness-artinian-or-trait`): the valuative
  criterion, affine case.
* `NonFlatDescentArtinian` (`127-non-flat-descent-artinian-epimorphism`): descent along a finite
  epimorphism over an artinian base, affine case. The folder gives no proof; it is proved in Lean
  as `Grothendieck.Folder127.nonFlatDescentArtinian`
  (`Grothendieck/AlgebraicGeometry/Folder127.lean`).
* `HironakaReducedBase` (`127-hironaka-reduced-base-openness`): stated for schemes, as the row
  gives it.

## Implementation notes

The two first rows concern a coherent sheaf `F` on `X`, a coherent quotient `G_U` of `F|_U` on a
retrocompact open `U`, flat over `Y`, and the image `G = Im(F → i_*G_U)`. They are stated here in
the affine case only: `Y = Spec A`, `X = Spec B`, `U = D(g)` a principal open, `F` the finite
`B`-module `M`, `G_U` a `B_g`-module `N` (a `B`-module on which `g` acts invertibly) with a map
`φ : M → N` that becomes surjective after inverting `g`. Then `i_*G_U` is `N`, `G` is the image of
`φ`, and after a base change `A → A'` the same data are `A' ⊗_A M → A' ⊗_A N`. « `G` flat over
`Y` with `U` universally `G`-dense relative to `Y` » (EGA IV 11.10.2) becomes: the image of `φ` is
`A`-flat and its inclusion into `N` stays injective after every base change `A → A'`
(`IsFlatClosureSolution`); the second clause is the universal injectivity of `G → i_*G_U`
relative to `Y` of the second row. These are special cases of the rows, not the rows.

## Not formalised

* The two first rows for a general `X → Y` and a retrocompact `U`: Mathlib has sheaves of modules
  on a scheme and their pushforward, but not coherent sheaves with their image sheaf, flatness of
  a sheaf of modules over a base, or universal schematic density relative to a base; the affine
  case keeps the commutative algebra the rows turn on.

## References

* A. Grothendieck, folder 127 (findings `127-closure-flatness-artinian-or-trait`,
  `127-non-flat-descent-artinian-epimorphism`, `127-hironaka-reduced-base-openness`)
* [EGA IV] 11.10.2
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TensorProduct

universe u

namespace OpenProblems.Findings.Folder127

/-- The formal fibres of a local ring `R` are geometrically normal: for every prime `P` of `R`, the
fibre `R̂ ⊗_R κ(P)` of the completion `R̂ = lim R/mⁿ` is a geometrically normal `κ(P)`-algebra
(`Algebra.IsGeometricallyNormal`, Stacks 0380). -/
def HasGeomNormalFormalFibres (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ P : PrimeSpectrum R, Algebra.IsGeometricallyNormal P.asIdeal.ResidueField
    (P.asIdeal.ResidueField ⊗[R] AdicCompletion (IsLocalRing.maximalIdeal R) R)

/-- A linear map `ψ : P → P'` of `R`-modules is universally injective relative to `R`: it stays
injective after every base change `R → R'`. -/
def IsUnivInjectiveRel (R : Type u) [CommRing R] {P P' : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P'] (ψ : P →ₗ[R] P') : Prop :=
  ∀ (R' : Type u) [CommRing R'] [Algebra R R'], Function.Injective (ψ.baseChange R')

/-- The image `G` of `ψ : P → P'` solves the problem of the folder over `R`: it is flat over `R`,
and its inclusion into `P'` is universally injective relative to `R`. With `P = M`, `P' = N`, this
says that `G = Im(F → i_*G_U)` is flat over `Y` and that `U` is universally `G`-dense relative to
`Y`. -/
def IsFlatClosureSolution (R : Type u) [CommRing R] {P P' : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P'] (ψ : P →ₗ[R] P') : Prop :=
  Module.Flat R (LinearMap.range ψ) ∧ IsUnivInjectiveRel R (LinearMap.range ψ).subtype

/-- The standing data of the two affine statements: `B` noetherian, `M` a finite `B`-module (the
coherent `F`), `g` invertible on `N` (so that `N` is a `B_g`-module, the `G_U` on `U = D(g)`),
`φ` surjective after inverting `g` (`G_U` is a quotient of `F|_U`), and `N` flat over `A` (`G_U`
flat over `Y`). -/
def IsAffineSetting (A B M N : Type u) [CommRing A] [CommRing B] [AddCommGroup M]
    [Module B M] [AddCommGroup N] [Module B N] [Module A N] (φ : M →ₗ[B] N) (g : B) : Prop :=
  IsNoetherianRing B ∧ Module.Finite B M ∧ IsUnit (algebraMap B (Module.End B N) g) ∧
    (∀ n : N, ∃ (m : M) (k : ℕ), g ^ k • n = φ m) ∧ Module.Flat A N

/-- `127-closure-flatness-artinian-or-trait` (folder 127, pp. 2–4, 15, 19), in the affine case.
For `X → Y` locally noetherian, `F` coherent on `X` and a coherent quotient `G_U` of `F|_U` on a
retrocompact open `U`, flat over `Y`: if the local rings of `X` at the points of `X − U` have
geometrically normal formal fibres, then `G = Im(F → i_*G_U)` is flat over `Y` with `U`
universally `G`-dense relative to `Y` if and only if this holds after every base change `Y' → Y`
with `Y'` artinian or a trait. The page's « Vrai théorème » (p. 15), stated without proof.

Status: candidate. The density form of condition (a) is the page's; the proof that it is
equivalent to the page's specialisation form, and the chaining of p. 19 with Lemma 1.3, are the
reading's. « tout » and « artinien » on p. 15 are uncertain readings, and the row asks that
« artinien » be checked on the facsimile first. To compare with EGA IV 11.8 and 11.10 and
Raynaud–Gruson I §§ 4–5.

Choices: the affine case described in the module docstring (`X = Spec B`, `Y = Spec A`,
`U = D(g)`), with `A` and `B` noetherian; the points of `X − U` are the primes containing `g`; a
trait is the spectrum of a discrete valuation ring. Not formalised: non-affine `X`, a
retrocompact `U` that is not principal. -/
@[montpellier "127, 2–4, 15, 19"]
def ClosureFlatnessArtinianOrTrait : Prop :=
  ∀ (A B M N : Type u) [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower A B M] [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] (φ : M →ₗ[B] N) (g : B), IsNoetherianRing A →
    IsAffineSetting A B M N φ g →
    (∀ (P : Ideal B) [P.IsPrime], g ∈ P → HasGeomNormalFormalFibres (Localization.AtPrime P)) →
    (IsFlatClosureSolution A (φ.restrictScalars A) ↔
      ∀ (A' : Type u) [CommRing A'] [Algebra A A'],
        (IsArtinianRing A' ∨ ∃ _ : IsDomain A', IsDiscreteValuationRing A') →
          IsFlatClosureSolution A' ((φ.restrictScalars A).baseChange A'))

/-- `127-non-flat-descent-artinian-epimorphism` (folder 127, pp. 2–3, Lemma 1.3), in the affine
case and for a finite epimorphism. Over an artinian base `Y`, the problem of a flat quotient `G`
of `F` extending `G_U`, with `G → i_*G_U` universally injective relative to `Y`, descends along an
epimorphism of schemes `Y' → Y`, flat or not, provided `Y' → Y` is finite: if it has a solution
after base change to `Y'`, it has one over `Y`. The solution, when it exists, is the image of `F`
in `i_*G_U`, hence unique, which is why the statement is about that image.

Status: proved, as `Grothendieck.Folder127.nonFlatDescentArtinian`
(`Grothendieck/AlgebraicGeometry/Folder127.lean`). The lemma is stated in the folder and not proved
(checked on the facsimile, #127). The proof uses neither the finiteness of `A → A'` nor the
flatness of the base-changed solution, and uses the epimorphism only through the injectivity of
`A → A'` (`Grothendieck.Folder127.nonFlatDescent_of_injective`). Stated as read.

Choices: the affine case of the module docstring; `Y' = Spec A'` with `A → A'` finite and
`Spec A' → Spec A` an epimorphism in the category of schemes; the standing hypotheses
`IsAffineSetting` (`B` noetherian, `M` finite, `N` flat over `A`) are those of the section, not
repeated by the lemma. Not formalised: the other branch of the page's alternative (« `f` and the
solution of finite presentation », a pencil note), which needs the base-changed solution as a
module over `A' ⊗_A B`; non-affine `X`. -/
@[montpellier "127, 2–3"]
def NonFlatDescentArtinian : Prop :=
  ∀ (A B M N : Type u) [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower A B M] [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] (φ : M →ₗ[B] N) (g : B), IsArtinianRing A →
    IsAffineSetting A B M N φ g →
    ∀ (A' : Type u) [CommRing A'] [Algebra A A'], Module.Finite A A' →
      Epi (Spec.map (CommRingCat.ofHom (algebraMap A A'))) →
      IsFlatClosureSolution A' ((φ.restrictScalars A).baseChange A') →
      IsFlatClosureSolution A (φ.restrictScalars A)

variable {X Y : Scheme.{u}}

/-- `f` is universally open at `x`: after every base change `Y' → Y`, the base-changed morphism
is open at every point `x'` over `x` (it maps every neighbourhood of `x'` onto a neighbourhood of
its image). -/
def UnivOpenAt (f : X ⟶ Y) (x : X) : Prop :=
  ∀ (Y' : Scheme.{u}) (g : Y' ⟶ Y) (x' : (pullback f g : Scheme.{u})),
    (pullback.fst f g).base x' = x →
      ∀ W ∈ 𝓝 x', (pullback.snd f g).base '' W ∈ 𝓝 ((pullback.snd f g).base x')

/-- The fibres of `f` are equidimensional of the same dimension near `x`: there are a
neighbourhood `V` of `x` and an `n` such that, for every `v ∈ V`, every irreducible component of
the fibre `f⁻¹(f(v))` through `v` has dimension `n`. The fibre is read as a subspace of `X`. -/
def FibresEquidimNear (f : X ⟶ Y) (x : X) : Prop :=
  ∃ V ∈ 𝓝 x, ∃ n : ℕ, ∀ v ∈ V, ∀ Z ∈ irreducibleComponents ↥(f.base ⁻¹' {f.base v}),
    (⟨v, rfl⟩ : ↥(f.base ⁻¹' {f.base v})) ∈ Z → topologicalKrullDim Z = n

/-- The fibre `X_y = X ×_Y Spec κ(y)` of `f` at `y`. -/
noncomputable abbrev schemeFibre (f : X ⟶ Y) (y : Y) : Scheme.{u} :=
  pullback f (Y.fromSpecResidueField y)

/-- The fibre `X_y` is reduced at the maximal generisations of `x`: at every point `z` of `X_y`
that is the generic point of an irreducible component of `X_y` and whose image in `X` is a
generisation of `x`, the local ring of `X_y` is reduced. -/
def FibreReducedAtMaxGeneralisations (f : X ⟶ Y) (x : X) : Prop :=
  ∀ z : schemeFibre f (f.base x), (pullback.fst f _).base z ⤳ x →
    closure {z} ∈ irreducibleComponents ↥(schemeFibre f (f.base x)) →
      _root_.IsReduced ((schemeFibre f (f.base x)).presheaf.stalk z)

/-- `(X_y)_red` is geometrically normal over `κ(y)`. The reduction is characterised rather than
constructed: it is any reduced scheme `Z` with a surjective closed immersion into `X_y` (all such
are isomorphic). Geometric normality is `AlgebraicGeometry.IsGeometricallyNormal` of the Stacks
library (Stacks 038M). -/
def FibreReductionGeomNormal (f : X ⟶ Y) (y : Y) : Prop :=
  ∀ (Z : Scheme.{u}) (i : Z ⟶ schemeFibre f y) [IsClosedImmersion i] [Surjective i]
    [IsReduced Z], IsGeometricallyNormal (k := Y.residueField y)
      (i ≫ pullback.snd f (Y.fromSpecResidueField y))

/-- `127-hironaka-reduced-base-openness` (folder 127, pp. 7, 9, 10, 12; Th. 1.8 as restated on
p. 10). Let `f : X → Y` be of finite type, `Y` noetherian, `y = f(x)` with `O_{Y,y}` reduced with
geometrically normal formal fibres. Suppose `f` universally open at `x`, the fibres
equidimensional of the same dimension near `x`, `X_y` reduced at the maximal generisations of `x`
and `(X_y)_red` geometrically normal. Then `x` has an open neighbourhood `U` such that
`U_red → Y` is flat with geometrically normal fibres.

Status: candidate. In print: Hironaka over a regular base (1958), Kollár over a normal excellent
base (1995; Families of varieties of general type, Th. 10.72), EGA IV 15.2.3 and 15.3.1 over a
reduced base under geometrically reduced fibres and with flatness only. The folder's form over a
reduced base with geometrically normal formal fibres was not found. The proof on p. 12 is a
sketch resting on uncertain readings and on the unproved Cor. 1.6–1.7.

Choices: the conclusion follows p. 10, the conclusion on p. 7 being struck; « `(X_y)_red`
geometrically normal » is taken for the whole fibre, as the row writes it (a hypothesis only
near `x` would give a stronger statement); `U_red` is any reduced scheme with a surjective closed
immersion into `U`; « of finite type » is locally of finite type and quasi-compact. -/
@[montpellier "127, 7, 9, 10, 12"]
def HironakaReducedBase : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] [IsNoetherian Y]
    (x : X), _root_.IsReduced (Y.presheaf.stalk (f.base x)) →
    HasGeomNormalFormalFibres (Y.presheaf.stalk (f.base x)) →
    UnivOpenAt f x → FibresEquidimNear f x → FibreReducedAtMaxGeneralisations f x →
    FibreReductionGeomNormal f (f.base x) →
    ∃ U : X.Opens, x ∈ U ∧ ∃ (Z : Scheme.{u}) (i : Z ⟶ U) (_ : IsClosedImmersion i)
      (_ : Surjective i) (_ : IsReduced Z), Flat (i ≫ U.ι ≫ f) ∧
        ∀ y : Y, IsGeometricallyNormal (k := Y.residueField y)
          (pullback.snd (i ≫ U.ι ≫ f) (Y.fromSpecResidueField y))

end OpenProblems.Findings.Folder127
