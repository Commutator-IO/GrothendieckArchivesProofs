module

public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
import Grothendieck.Attr

@[expose] public section

/-!
# Buffalo, algebraic geometry, part 06: complete regular local rings are power series rings

`Part06.lean` left the entry `Oqhr-Gt66es-8313` (2:18:33: a complete local algebra `𝒪` over a
field `k`, with residue field `k`, is regular if and only if `𝒪 ≃ k[[t_1, …, t_n]]` as a
`k`-algebra; if `A` is regular, so is `A[[t]]`) unformalised, Mathlib having neither Cohen's
structure theorem nor the regularity of `A[[t]]`. It is proved here from AxiomMath/Stacks
(Apache-2.0).

**What is proved.**
* `prop_8313`: let `k` be a field and `𝒪` a noetherian local `k`-algebra, complete for its
  maximal ideal `𝔪`, such that `k → 𝒪 → 𝒪/𝔪` is bijective (residue field `k`). Then `𝒪` is
  regular (Mathlib's `IsRegularLocalRing`) if and only if `𝒪 ≃ₐ[k] k[[t_1, …, t_n]]` for some `n`
  (the proof takes `n = dim_k 𝔪/𝔪²`).
* `prop_8313_powerSeries`: if `A` is a regular local ring, so is `A[[t]]`.

**How.** Regular ⇒ power series is Stacks 0C0S, part (2)
(`IsRegularLocalRing.nonempty_ringEquiv_and_algEquiv_mvPowerSeries`,
`StacksFrontier/RingTheory/CompleteLocalRing/Regular.lean`), the argument of the lecture: lift a
basis of `𝔪/𝔪²` to `f_1, …, f_n ∈ 𝔪`; the continuous `k`-algebra map `k[[t]] → 𝒪`, `t_i ↦ f_i`, is
surjective by completeness (Stacks 0315) and injective because a kernel would make `dim 𝒪 < n`.
The converse is the regularity of `k[[t_1, …, t_n]]` (`isRegularLocalRing_mvPowerSeries`), carried
along the isomorphism. The regularity of `A[[t]]` is `PowerSeries.isRegularLocalRing`
(`StacksFrontier/RingTheory/RegularLocalRing/Criteria.lean`): adjoining `t` adds one to the minimal
number of generators of the maximal ideal and at least one to the Krull dimension.

**Not formalised.** Completeness is that of `𝒪` for its `𝔪`-adic topology
(`IsAdicComplete (maximalIdeal 𝒪) 𝒪`) and "local algebra" is read as noetherian, as the entry's
regularity requires. The general Cohen structure theorem, which the entry does not state (a
complete local ring without a given coefficient field is a quotient of a power series ring over a
field or a Cohen ring, Stacks 032A, and a complete regular local ring containing a field is a power
series ring over its residue field, Stacks 0C0S (1)), is not restated here.
-/

open IsLocalRing

universe u v

namespace Buffalo.AG.Part06

/-- Oqhr-Gt66es-8313 (2:18:33) [prop] A complete local algebra `𝒪` over a field `k`, with residue
field `k`, is regular if and only if `𝒪 ≃ k[[t_1, …, t_n]]` as a `k`-algebra. Stacks 0C0S. -/
@[buffalo "Oqhr-Gt66es-8313"]
theorem prop_8313 (k : Type u) [Field k] (O : Type v) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra k O]
    (hk : Function.Bijective ((residue O).comp (algebraMap k O))) :
    IsRegularLocalRing O ↔ ∃ n : ℕ, Nonempty (O ≃ₐ[k] MvPowerSeries (Fin n) k) := by
  constructor
  · intro hO
    exact ⟨_, (IsRegularLocalRing.nonempty_ringEquiv_and_algEquiv_mvPowerSeries.{v, 0, u} O
      (Module.finrank (ResidueField O) (CotangentSpace O)) rfl).2 k hk⟩
  · rintro ⟨n, ⟨e⟩⟩
    have : IsRegularLocalRing (MvPowerSeries (Fin n) k) := isRegularLocalRing_mvPowerSeries k n
    exact IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv

/-- Oqhr-Gt66es-8313 (2:18:33) [prop], second half: if `A` is a regular local ring, so is the
power series ring `A[[t]]`. -/
@[buffalo "Oqhr-Gt66es-8313"]
theorem prop_8313_powerSeries (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsRegularLocalRing (PowerSeries A) :=
  PowerSeries.isRegularLocalRing A

end Buffalo.AG.Part06
