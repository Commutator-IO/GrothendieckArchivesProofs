import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.LinearCombination

/-!
# Folder 91, pages 15–24: `Hom_S(X, Y; φ) → Hom_S(Z, Y)` is unramified

Finding `91-hom-unramified-rigidification` of `src/content/findings.ts`. For `φ : Z → X`
between proper flat `S`-schemes and `Y` separated of finite type, page 15 cuts out the open
subfunctor `Hom_S(X, Y; φ)` of the `u` at which composition with `φ` is unramified
(`M_v → M_u` surjective, EGA III 7.7.6), and page 16 states that
`φ^♯ : Hom_S(X, Y; φ) → Hom_S(Z, Y)`, `u ↦ u φ`, is representable by unramified morphisms.

What is formalised. The functor `Mor_S(X, Y)` as an algebraic space (Stacks 0D1C, 0DPN) has an
import closure of some 18,000 modules, so it is not imported; we prove the infinitesimal and
module-theoretic content of the pages on the affine (algebraic) core.

* `eq_of_comp_eq_of_rigid` (formal unramifiedness of `φ^♯`, the rigidity form of page 21):
  `u, u' : B → C'` are `R`-algebra maps (points of `Hom(X, Y)` with values in a first-order
  thickening `C' → C'/I`, `I² = 0`) that agree modulo `I` and have the same composite with
  `ψ = φ^♯ : C' → D'`. If every `u`-derivation `B → I` killed by `ψ` is zero (the injectivity of
  `Hom(u₀^* Ω¹, 𝒪_{X₀} ⊗ J) → Hom(v₀^* Ω¹, 𝒪_{Z₀} ⊗ J)`, i.e. `M_v → M_u` surjective), then
  `u = u'`: liftings along `φ^♯` are unique.
* `exists_unique_lift_of_surjective` (the cartesian square of page 19): for `f : M_v → M_u`
  surjective and `ι : J → J_η` injective (`J` torsion-free over a domain, the reading's
  addition), a compatible pair `(a : Hom(M_v, J), b : Hom(M_u, J_η))` comes from a unique
  `c : Hom(M_u, J)`.
* `obstruction_vanishes_of_admitted` (condition 7°, pages 19–20): the two steps the page
  « admet » are taken as the hypotheses `hadmis₁` (`η''` is the image of `ξ''`) and `hadmis₂`
  (`η' = ξ'''`); they are not proved, as on the page. Under them the obstruction `ξ''` to
  extending `u₀` vanishes.
-/

namespace Grothendieck.Folder91HomUnramified

/-- Formal unramifiedness of composition with `φ` under the rigidity hypothesis of page 21:
two first-order deformations of `u` with the same composite with `φ` coincide. -/
theorem eq_of_comp_eq_of_rigid {R B C' D' : Type*} [CommRing R] [CommRing B] [CommRing C']
    [CommRing D'] [Algebra R B] [Algebra R C'] [Algebra R D'] (I : Ideal C') (hI : I * I = ⊥)
    (ψ : C' →ₐ[R] D') (u u' : B →ₐ[R] C') (hmod : ∀ b, u b - u' b ∈ I)
    (hcomp : ψ.comp u = ψ.comp u')
    (hrigid : ∀ δ : B →ₗ[R] C', (∀ b, δ b ∈ I) →
      (∀ x y, δ (x * y) = u x * δ y + u y * δ x) → (∀ b, ψ (δ b) = 0) → δ = 0) :
    u = u' := by
  have hsq : ∀ x y, (u x - u' x) * (u y - u' y) = 0 := fun x y => by
    have h := Ideal.mul_mem_mul (hmod x) (hmod y)
    rw [hI] at h
    exact (Submodule.mem_bot _).1 h
  have h := hrigid (u.toLinearMap - u'.toLinearMap) hmod
    (fun x y => by
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, map_mul]
      linear_combination -(hsq x y))
    (fun b => by
      have := congrArg (fun g => g b) hcomp
      simp only [AlgHom.comp_apply] at this
      simp [this])
  ext b
  exact sub_eq_zero.1 (congrArg (fun g => g b) h)

/-- The cartesian square of page 19: `Hom(M_u, J)` is the fibre product of `Hom(M_v, J)` and
`Hom(M_u, J_η)` over `Hom(M_v, J_η)` when `M_v → M_u` is onto and `J → J_η` is injective. -/
theorem exists_unique_lift_of_surjective {A Mu Mv J Jη : Type*} [CommRing A]
    [AddCommGroup Mu] [AddCommGroup Mv] [AddCommGroup J] [AddCommGroup Jη] [Module A Mu]
    [Module A Mv] [Module A J] [Module A Jη] (f : Mv →ₗ[A] Mu) (hf : Function.Surjective f)
    (ι : J →ₗ[A] Jη) (hι : Function.Injective ι) (a : Mv →ₗ[A] J) (b : Mu →ₗ[A] Jη)
    (hab : ι.comp a = b.comp f) :
    ∃! c : Mu →ₗ[A] J, c.comp f = a ∧ ι.comp c = b := by
  have hker : LinearMap.ker f ≤ LinearMap.ker a := fun x hx => by
    have := congrArg (fun g => g x) hab
    simp only [LinearMap.comp_apply, LinearMap.mem_ker.1 hx, map_zero] at this
    exact LinearMap.mem_ker.2 (hι (by rw [this, map_zero]))
  let c := ((LinearMap.ker f).liftQ a hker).comp
    (f.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hc : c.comp f = a := by
    ext x
    have : (f.quotKerEquivOfSurjective hf).symm (f x) = Submodule.Quotient.mk x :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    simp [c, this]
  refine ⟨c, ⟨hc, ?_⟩, fun c' ⟨h1, _⟩ => ?_⟩
  · ext y
    obtain ⟨x, rfl⟩ := hf y
    have := congrArg (fun g => g x) hab
    simp only [LinearMap.comp_apply] at this ⊢
    rw [← this, ← LinearMap.comp_apply c f, hc]
  · ext y
    obtain ⟨x, rfl⟩ := hf y
    rw [← LinearMap.comp_apply c' f, ← LinearMap.comp_apply c f, h1, hc]

/-- Condition 7° of the representability criterion (pages 19–20), with the two « admis » steps
as hypotheses. `δ : Hom(N, J)/Im → Ext¹(M_{u₀}, J)` carries `ξ'''` to `ξ''`, `ρ` carries `ξ''`
to the obstruction `η''` of `v₀`, which vanishes since `v` exists; `η'` is the class given by
the generic extensions, zero by hypothesis. The conclusion: the obstruction to extending `u₀`
vanishes. -/
theorem obstruction_vanishes_of_admitted {Q E F : Type*} [AddCommGroup Q] [AddCommGroup E]
    [AddCommGroup F] (δ : Q →+ E) (ρ : E →+ F) (ξ''' η' : Q) (ξ'' : E) (η'' : F)
    (hξ : ξ'' = δ ξ''') (hη'' : η'' = 0) (hη' : η' = 0)
    (hadmis₁ : η'' = ρ ξ'') (hadmis₂ : η' = ξ''') : ξ'' = 0 ∧ ρ ξ'' = 0 := by
  subst hξ hadmis₂ hη'
  exact ⟨map_zero δ, hadmis₁ ▸ hη''⟩

end Grothendieck.Folder91HomUnramified
