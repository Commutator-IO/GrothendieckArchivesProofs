import StacksFrontier.RingTheory.Flat.LocalCriteria.FibreCriteria
import StacksFrontier.RingTheory.Flat.ShortExact
import StacksFrontier.RingTheory.Coherent.Flat

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

**Not formalised.** The passage from sheaves to stalks: the stalk `G_y`, the maps
`G_y → (φ_* F)_y → F_x`, and the identification of `𝒪_{S,s} → 𝒪_{Y,y}` as a local homomorphism
of noetherian local rings are taken as the input of the statement, not built from a morphism of
schemes. The page's own reading of clause c), with injectivity into `(φ_{s*} F_s)_y` rather than
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
