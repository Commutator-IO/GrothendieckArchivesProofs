import Mordell.AbelianVariety.Ample.Sum
import Mordell.AlgebraicGeometry.VeryAmple.Twist
import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic

/-!
# Buffalo, algebraic geometry, part 07: tensor products and twists of ample sheaves

Two clauses of the « Ample sheaves » topic of the Buffalo index (part 07) that were left open:
the stability of ampleness under tensor product (entry 26840), and the twist `L^{⊗ n} ⊗ M`
(entry 27219). The ample predicates are those of AxiomMath/Stacks (Apache-2.0):
`Stacks.Ample.IsAmple` and `AlgebraicGeometry.Scheme.Modules.IsAmple` (Stacks 01PS, EGA II 4.5.3),
which agree by `Stacks.AmpleBridge.isAmple_iff_isAmple`. Very ampleness over a field is
`Faltings.IsVeryAmple` (an embedding `φ : X ⟶ ℙⁿ_k` with `L ≅ φ^* 𝒪(1)`), from the files of
AxiomMath/Mordell copied under `Mordell/` (see `NOTICE`).

**What is proved.**
* `prop_26840_tensor`, `prop_26840_tensor_stacks`: the tensor product of two ample invertible
  sheaves on a scheme is ample (Stacks 0890), in both spellings of 01PS. This is the clause
  « ample sheaves are stable under tensor product » of 26840.
* `prop_27219_veryAmple`: on a projective variety `X` over a field `k`, if `L` is very ample and
  `M` is any invertible sheaf, then `M ⊗ L^{⊗ a}` is very ample for all `a` large enough
  (Hartshorne II.5.17, II Ex. 7.5; Mordell `Faltings.eventually_isVeryAmple_tensorModules_tensorPowModule`,
  through the Segre embedding). This is 27219 for a very ample `L` over a field.

**Not formalised.** 27219 for an ample `L` over a quasi-compact base `Y`, and its corollary that
the ample cone spans `Pic(X) ⊗ ℚ`. The convex cone of 27035. Stability of ampleness under base
change (the other clause of 26840). The Segre embedding `ℙ(E) × ℙ(F) → ℙ(E ⊗ F)` over a base
(26511, 32732): Mordell has it only for `ℙʳ_S × ℙᵐ_S` with the twisting sheaves, not for `ℙ(E)`.
-/

universe u

-- The option Mordell's files are elaborated with (instance search on tensor powers).
set_option maxSynthPendingDepth 3

open AlgebraicGeometry CategoryTheory

namespace Buffalo.AG.Part07

/-- **Buffalo 26840, tensor clause** (Stacks 0890). On a scheme, the tensor product of two ample
invertible sheaves is ample. -/
theorem prop_26840_tensor (X : Scheme.{u}) (L M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X M]
    (hL : Scheme.Modules.IsAmple X L) (hM : Scheme.Modules.IsAmple X M) :
    Scheme.Modules.IsAmple X (Scheme.Modules.tensorProductModule X L M) :=
  Scheme.Modules.isAmple_tensor_of_power_sections_cover X L M hL fun x =>
    let ⟨n, hn, s, hs, _⟩ := hM.2 x; ⟨n, hn, s, hs⟩

/-- **Buffalo 26840, tensor clause**, for the predicate `Stacks.Ample.IsAmple` of Stacks 01PS. -/
theorem prop_26840_tensor_stacks (X : Scheme.{u}) (L M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X M]
    (hL : Stacks.Ample.IsAmple X L) (hM : Stacks.Ample.IsAmple X M) :
    Stacks.Ample.IsAmple X (Scheme.Modules.tensorProductModule X L M) := by
  refine (Stacks.AmpleBridge.isAmple_iff_isAmple X _).2 ?_
  exact prop_26840_tensor X L M ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).1 hL)
    ((Stacks.AmpleBridge.isAmple_iff_isAmple X M).1 hM)

/-- **Buffalo 27219, very ample case over a field.** On a projective variety `X` over `k`, if `L`
is very ample and `M` is any invertible sheaf, then `M ⊗ L^{⊗ a}` is very ample for all
sufficiently large integers `a`. -/
theorem prop_27219_veryAmple {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Faltings.IsVeryAmple f L) (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] :
    ∀ᶠ a : ℤ in Filter.atTop,
      Faltings.IsVeryAmple f (Stacks.RelativeVeryAmple.tensorModules X M
        (Stacks.Ample.tensorPowModule X L a)) :=
  Faltings.eventually_isVeryAmple_tensorModules_tensorPowModule f L hL M

end Buffalo.AG.Part07
