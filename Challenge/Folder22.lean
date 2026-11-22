module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

/-!
# Folder 22: Lemme 3.3 and the obstruction of pages 22 and 24

Finding `22-power-series-discrete-obstruction` (pages 22, 24).

The trusted statements of `Grothendieck.Folder22.lemme3_3` and
`Grothendieck.Folder22.no_derivation`, written with Mathlib alone and left unproved.
`lake comparator` (`comparator.json`) checks that `Solution.Folder22` proves exactly these
statements, through the untrusted imports of this repository, with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

open PowerSeries TensorProduct

namespace Challenge.Folder22

/-- *Lemme 3.3. For `M` finitely presented, `M ⊗_A ∏ P_i → ∏ (M ⊗_A P_i)` is an isomorphism.* -/
theorem lemme3_3 {A : Type*} [CommRing A] {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] :
    Function.Bijective (TensorProduct.piRightHom A A M P) := by
  sorry

/-- *Pages 22, 24. Let `M` be a free `k`-module with basis `b`, and `a₀, a₁, …` in `k`. There
is no derivation `D : k⟦t⟧ → k⟦t⟧ ⊗_k M` with `D(aₙ) = 1 ⊗ b(iₙ)` for infinitely many
distinct indices `iₙ`.* -/
theorem no_derivation {k : Type*} [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]
    {R : Type*} [CommRing R] [Algebra R k] [Nontrivial k] {ι : Type*} (b : Module.Basis ι k M)
    (e : ℕ → ι) (he : Function.Injective e) (a : ℕ → k) (D : Derivation R k⟦X⟧ (k⟦X⟧ ⊗[k] M))
    (hD : ∀ n, D (C (a n)) = 1 ⊗ₜ b (e n)) : False := by
  sorry

end Challenge.Folder22
