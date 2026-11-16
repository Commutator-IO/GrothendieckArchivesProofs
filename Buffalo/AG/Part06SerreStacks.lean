import StacksFrontier.RingTheory.RegularRing.GlobalDimension

/-!
# Buffalo, algebraic geometry, part 06: Serre's characterisation of regular local rings

`Part06.lean` left the entry `Oqhr-Gt66es-8121` (2:15:21, Serre: a noetherian local ring is
regular if and only if its global dimension is finite; the localization of a regular local ring at
a prime is therefore regular) unformalised, Mathlib having no notion of global dimension. It is
proved here from AxiomMath/Stacks (Apache-2.0).

**What is proved.** `thm_8121`: for a noetherian local ring `R`,
* `R` is regular (Mathlib's `IsRegularLocalRing`) if and only if its global dimension is finite;
* if `R` is regular, its global dimension equals its Krull dimension `dim R`;
* if `R` is regular, then `R_𝔭` is a regular local ring for every prime `𝔭` of `R`.

**How.** The global dimension is the supremum `⨆ M : ModuleCat.{u} R, projectiveDimension M` of
the projective dimensions of all `R`-modules, in `WithBot ℕ∞`, and "finite" is `≠ ⊤`, as in
Stacks 00O6 and 00OC. The first two items are items (2), (3), (4) of Stacks 00OC
(`isRegularLocalRing_tfae`, `StacksFrontier/RingTheory/RegularLocalRing/GlobalDimension.lean`);
the third is Stacks 0AFS (`IsLocalRing.isRegularRing_tfae`,
`StacksFrontier/RingTheory/RegularRing/GlobalDimension.lean`), whose proof is the one of the
lecture: global dimension does not grow under localization (Stacks 00O8), so `R_𝔭` has finite
global dimension, hence is regular by Serre's criterion.

**Not formalised.** The global dimension is that of modules in the universe of `R` (by Stacks
065T this is no restriction, the cyclic modules `R ⧸ I` already bounding it); the further equality
of the global dimension with `dim_κ 𝔪/𝔪²` and the equivalence with `pd_R κ < ∞`, which Stacks
00OC also gives, are not part of the entry and are not restated here.
-/

open CategoryTheory

universe u

namespace Buffalo.AG.Part06

/-- Oqhr-Gt66es-8121 (2:15:21) [thm] (Serre) A noetherian local ring `R` is regular if and only if
its global dimension `sup_M pd_R M` is finite, and then the global dimension is `dim R`; the
localization of a regular local ring at a prime is therefore regular. Stacks 00OC and 0AFS. -/
theorem thm_8121 {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    (IsRegularLocalRing R ↔ (⨆ M : ModuleCat.{u} R, projectiveDimension M) ≠ ⊤) ∧
    (IsRegularLocalRing R → (⨆ M : ModuleCat.{u} R, projectiveDimension M) = ringKrullDim R) ∧
    (IsRegularLocalRing R →
      ∀ (p : Ideal R) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p)) := by
  have h := isRegularLocalRing_tfae (R := R)
  refine ⟨h.out 3 2, (h.out 3 4).mp, ?_⟩
  intro hR p hp
  have : IsRegularRing R := ((IsLocalRing.isRegularRing_tfae (R := R)).out 1 3).mp hR
  exact IsRegularRing.isRegularLocalRing_localization p

end Buffalo.AG.Part06
