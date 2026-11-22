module

public import StacksFrontier.RingTheory.Flat.LocalCriteria.FibreCriteria
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Coherent.Flat
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictStalkDepth
public import Mathlib.AlgebraicGeometry.Noetherian
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 49, page 3: a coherent sheaf that embeds fibrewise into flat stalks is flat

Finding `49-flatness-lemma-pushforward`. The Lemme of page 3: for `φ : X → Y` of finite type over
a locally noetherian `S`, `F` quasi-coherent on `X` and flat over `S`, `G` coherent on `Y`, and a
map `G → φ_* F` whose restriction to the fibre over `s` is injective at the points above `y`,
`G` is flat over `S` at `y`.

The statement is local at `y`. Write `R = 𝒪_{S,s}` (noetherian local), `A = 𝒪_{Y,y}` (noetherian
local, `R → A` local), `N = G_y` (a finite `A`-module), and for each point `x` of `X` above `y`
let `M x = F_x` (flat over `R`) and `u x : G_y → (φ_* F)_y → F_x` (`R`-linear). The fibre over `s`
is reduction modulo the maximal ideal `𝔪` of `R`, and « injective on the fibre at the points above
`y` » is read as: an element of `G_y` whose images in all the `F_x / 𝔪 F_x` vanish lies in
`𝔪 G_y`. That is, `G_y ⊗ k(s) → ∏ₓ F_x ⊗ k(s)` is injective.

**What is proved.**
* `flat_of_fibre_injective_pi`: under these hypotheses, `N` is flat over `R`, and the map
  `N → ∏ₓ M x` is injective. No finiteness of `φ` at the points above `y` is needed: the target
  `∏ₓ F_x` is not finite over `A`, but the local criterion only asks that the source be finite.
* `flat_of_fibre_injective`: the case of one flat target, for instance `(φ_* F)_y` itself when it
  is flat over `R`.

**How.** A product of flat modules over a noetherian ring is flat (Chase's theorem, Stacks 05CZ
`IsCoherentRing.tfae_flat_pi`, a noetherian ring being coherent, 05CY). The local flatness
criterion in the form of Stacks 00ME
(`Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing`,
EGA III 4.6.7.1) asks only that the target be flat over `R` and the source finite over `A`: it
gives that `N → ∏ₓ M x` is injective with flat cokernel. A submodule of a flat module with flat
quotient is flat (Stacks 00HM, `flat_of_flat_of_flat_quotient`).

**For schemes.** `flat_of_fibre_injective_scheme` builds the input from a morphism of schemes:
for `p : Y → S` and `φ : X → Y`, `F` an `𝒪_X`-module, `G` an `𝒪_Y`-module and `α : G → φ_* F`,
the stalk `G_y` is a module over `𝒪_{Y,y}` (AxiomMath/Stacks' `instModuleStalk`), and for each
`x` above `y` the map `G_y → (φ_* F)_y → F_x` (`mapAbove`) is the stalk of `α` followed by the
germ map of the direct image (Stacks' `pushforwardStalkHom`), semilinear over
`φ^♯_x : 𝒪_{Y,y} → 𝒪_{X,x}` (`mapAbove_smul`). `R = 𝒪_{S,p(y)}` acts through `p^♯_y`, a local
homomorphism of noetherian local rings when `S` and `Y` are locally noetherian.

**Not formalised.** Finiteness of `G_y` over `𝒪_{Y,y}` is a hypothesis of the scheme form (it
holds for `G` coherent). Flatness of `F` over `S` at `x` is read as flatness of `F_x` over
`𝒪_{S,p(y)}`. The page's own reading of clause c), with injectivity into `(φ_{s*} F_s)_y` rather than
into the product of the stalks above `y`, is weaker when `φ` is not proper, and is not covered.
-/

universe u v

open IsLocalRing

namespace Grothendieck.Folder49Flatness

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra R A]
  [IsLocalHom (algebraMap R A)]
  {N : Type*} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
  [Module.Finite A N]

include A

/-- **Folder 49, p. 3, local form.** `R → A` a local homomorphism of noetherian local rings, `N`
a finite `A`-module, `M x` flat `R`-modules and `u x : N → M x` `R`-linear maps such that an
element of `N` whose images all lie in `𝔪 M x` lies in `𝔪 N`. Then `N` is flat over `R`, and
`N → ∏ₓ M x` is injective. -/
@[montpellier "49, 3"]
theorem flat_of_fibre_injective_pi {ι : Type u} {M : ι → Type u} [∀ x, AddCommGroup (M x)]
    [∀ x, Module R (M x)] (hM : ∀ x, Module.Flat R (M x)) (u : ∀ x, N →ₗ[R] M x)
    (hu : ∀ n : N, (∀ x, u x n ∈ maximalIdeal R • (⊤ : Submodule R (M x))) →
      n ∈ maximalIdeal R • (⊤ : Submodule R N)) :
    Module.Flat R N ∧ Function.Injective (LinearMap.pi u) := by
  -- Chase: a product of flat modules over a noetherian ring is flat.
  have hchase : IsCoherentRing R ↔ ∀ (B : Type u) (Q : B → Type u) [∀ α, AddCommGroup (Q α)]
      [∀ α, Module R (Q α)], (∀ α, Module.Flat R (Q α)) → Module.Flat R (∀ α, Q α) :=
    (IsCoherentRing.tfae_flat_pi R).out 1 2
  have hpi : Module.Flat R (∀ x, M x) :=
    hchase.mp (isCoherentRing_of_isNoetherianRing R) ι M hM
  -- The fibre map `N/𝔪N → (∏ M x)/𝔪(∏ M x)` is injective.
  have hfib : Function.Injective (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R N))
      (maximalIdeal R • (⊤ : Submodule R (∀ x, M x))) (LinearMap.pi u)
      (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) (LinearMap.pi u))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    refine hu n fun x => ?_
    exact Submodule.smul_top_le_comap_smul_top (maximalIdeal R) (LinearMap.proj x) hq
  -- Stacks 00ME: injective with flat cokernel.
  have := hpi
  obtain ⟨hinj, hQ⟩ :=
    Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
      (S := A) (LinearMap.pi u) hfib
  -- Stacks 00HM: a submodule of a flat module with flat quotient is flat.
  have := hQ
  refine ⟨?_, hinj⟩
  exact flat_of_flat_of_flat_quotient (LinearMap.pi u) (LinearMap.range (LinearMap.pi u)).mkQ hinj
    (LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)) (Submodule.mkQ_surjective _)

/-- **Folder 49, p. 3, one target.** The same with a single flat `R`-module `M`: if
`u : N → M` is injective modulo `𝔪`, then `N` is flat over `R` and `u` is injective. -/
@[montpellier "49, 3"]
theorem flat_of_fibre_injective {M : Type u} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (u : N →ₗ[R] M)
    (hu : ∀ n : N, u n ∈ maximalIdeal R • (⊤ : Submodule R M) →
      n ∈ maximalIdeal R • (⊤ : Submodule R N)) :
    Module.Flat R N ∧ Function.Injective u := by
  obtain ⟨hN, hinj⟩ := flat_of_fibre_injective_pi A (ι := PUnit.{u + 1}) (M := fun _ => M)
    (fun _ => inferInstance) (fun _ => u) (fun n hn => hu n (hn PUnit.unit))
  refine ⟨hN, fun a b hab => hinj ?_⟩
  funext x
  simp only [LinearMap.pi_apply]
  exact hab

end Grothendieck.Folder49Flatness

open AlgebraicGeometry CategoryTheory

namespace Grothendieck.Folder49Flatness

open Scheme.Modules
variable {X Y : Scheme.{u}} (φ : X ⟶ Y) (F : X.Modules) (G : Y.Modules)
  (α : G ⟶ (pushforward φ).obj F)

/-- `G_{φ(x)} → (φ_* F)_{φ(x)} → F_x`. -/
noncomputable def fibreMap (x : X) : G.presheaf.stalk (φ.base x) →+ F.presheaf.stalk x :=
  (stalkMapOfHom α (φ.base x) ≫ pushforwardStalkHom φ F x).hom

theorem fibreMap_smul (x : X) (r : Y.presheaf.stalk (φ.base x)) (n : G.presheaf.stalk (φ.base x)) :
    fibreMap φ F G α x (r • n) = (φ.stalkMap x).hom r • fibreMap φ F G α x n := by
  simp only [fibreMap, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [stalkMapOfHom_smul, pushforwardStalkHom_smul]

/-- The points of `X` above `y`. -/
abbrev Above (y : Y) : Type u := {x : X // φ.base x = y}

/-- `𝒪_{Y,y} → 𝒪_{X,x}` for `x` above `y`. -/
noncomputable def ringAbove {y : Y} (x : Above φ y) : Y.presheaf.stalk y →+* X.presheaf.stalk x.1 := by
  obtain ⟨x, rfl⟩ := x
  exact (φ.stalkMap x).hom

/-- `G_y → (φ_* F)_y → F_x` for `x` above `y`. -/
noncomputable def mapAbove (F : X.Modules) (G : Y.Modules) (α : G ⟶ (pushforward φ).obj F)
    {y : Y} (x : Above φ y) : G.presheaf.stalk y →+ F.presheaf.stalk x.1 := by
  obtain ⟨x, rfl⟩ := x
  exact fibreMap φ F G α x

theorem mapAbove_smul {y : Y} (x : Above φ y) (r : Y.presheaf.stalk y) (n : G.presheaf.stalk y) :
    mapAbove φ F G α x (r • n) = ringAbove φ x r • mapAbove φ F G α x n := by
  obtain ⟨x, rfl⟩ := x
  exact fibreMap_smul φ F G α x r n

variable {S : Scheme.{u}} (p : Y ⟶ S)

/-- **Folder 49, p. 3, for schemes.** Let `p : Y → S` with `S` and `Y` locally noetherian,
`φ : X → Y`, `F` an `𝒪_X`-module, `G` an `𝒪_Y`-module with `G_y` finite over `𝒪_{Y,y}`, and
`α : G → φ_* F`. Put `R = 𝒪_{S,p(y)}`, acting on `G_y` through `p^♯_y` and on `F_x` (`x` above
`y`) through `φ^♯_x ∘ p^♯_y`. If every `F_x` is flat over `R` and an element of `G_y` whose images
in all the `F_x` lie in `𝔪_R F_x` lies in `𝔪_R G_y`, then `G_y` is flat over `R` and
`G_y → ∏ₓ F_x` is injective. -/
@[montpellier "49, 3"]
theorem flat_of_fibre_injective_scheme [AlgebraicGeometry.IsLocallyNoetherian S]
    [AlgebraicGeometry.IsLocallyNoetherian Y] (y : Y)
    [Module.Finite (Y.presheaf.stalk y) (G.presheaf.stalk y)] :
    letI : Module (S.presheaf.stalk (p.base y)) (G.presheaf.stalk y) :=
      Module.compHom _ (p.stalkMap y).hom
    letI : ∀ x : Above φ y, Module (S.presheaf.stalk (p.base y)) (F.presheaf.stalk x.1) :=
      fun x => Module.compHom _ ((ringAbove φ x).comp (p.stalkMap y).hom)
    (∀ x : Above φ y, Module.Flat (S.presheaf.stalk (p.base y)) (F.presheaf.stalk x.1)) →
    (∀ n : G.presheaf.stalk y, (∀ x : Above φ y, mapAbove φ F G α x n ∈
        maximalIdeal (S.presheaf.stalk (p.base y)) •
          (⊤ : Submodule (S.presheaf.stalk (p.base y)) (F.presheaf.stalk x.1))) →
      n ∈ maximalIdeal (S.presheaf.stalk (p.base y)) •
        (⊤ : Submodule (S.presheaf.stalk (p.base y)) (G.presheaf.stalk y))) →
    Module.Flat (S.presheaf.stalk (p.base y)) (G.presheaf.stalk y) ∧
      Function.Injective (fun n : G.presheaf.stalk y => fun x : Above φ y => mapAbove φ F G α x n) := by
  intro hM hu
  let : Module (S.presheaf.stalk (p.base y)) (G.presheaf.stalk y) :=
    Module.compHom _ (p.stalkMap y).hom
  let : ∀ x : Above φ y, Module (S.presheaf.stalk (p.base y)) (F.presheaf.stalk x.1) :=
    fun x => Module.compHom _ ((ringAbove φ x).comp (p.stalkMap y).hom)
  let : Algebra (S.presheaf.stalk (p.base y)) (Y.presheaf.stalk y) := (p.stalkMap y).hom.toAlgebra
  have : IsScalarTower (S.presheaf.stalk (p.base y)) (Y.presheaf.stalk y) (G.presheaf.stalk y) :=
    ⟨fun r a n => by
      change ((p.stalkMap y).hom r * a) • n = (p.stalkMap y).hom r • (a • n)
      rw [mul_smul]⟩
  have : IsLocalHom (algebraMap (S.presheaf.stalk (p.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (p.stalkMap y).hom)
  let u : ∀ x : Above φ y, G.presheaf.stalk y →ₗ[S.presheaf.stalk (p.base y)] F.presheaf.stalk x.1 :=
    fun x => { mapAbove φ F G α x with
      map_smul' := fun r n => by
        change mapAbove φ F G α x ((p.stalkMap y).hom r • n) = _
        rw [mapAbove_smul]
        rfl }
  obtain ⟨h1, h2⟩ := flat_of_fibre_injective_pi (Y.presheaf.stalk y) hM u hu
  exact ⟨h1, h2⟩
end Grothendieck.Folder49Flatness
