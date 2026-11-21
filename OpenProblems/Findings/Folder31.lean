module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TorsionVanishingBound
public import Mathlib.Algebra.Order.Ring.IsFormallyReal

@[expose] public section

/-!
# Folder 31, page 22: a lower bound for the cohomological dimension of a local domain, stated

Finding `31-local-ring-cd-lower-bound`. *For a noetherian local domain `A` with fraction field `K`
and residue field `k`, `cd_r(K) ≥ cd_r(k) + dim A` for every prime `r`, with exactly two possible
exceptions: `r` is the characteristic of `K`, or `r = 2` and some point of `Spec A` has an
orderable residue field `k(x)` with `cd₂ k(x)(√−1)` finite — the second exception disappearing
when `A` is regular, and refining to « `k` itself real » when `A` is catenary and universally
japanese.*

Nothing here is proved; a `def … : Prop` asserts nothing.

**The `r`-cohomological dimension.** `cd_r(F)` of a field is the least `d` such that
`H^p_ét(Spec F, 𝓖) = 0` for every abelian sheaf `𝓖` killed by `r` and every `p > d`
(`cdPrime`, from Stacks' `AlgebraicGeometry.Scheme.IsTorsionVanishingBound` with `n = r`, the
form of Travaux de Gabber XVIII-A used by Stacks 0DC6). Values are in `WithBot ℕ∞`, as is
`ringKrullDim`, so `cd_r(k) + dim A` is computed there.

**The exceptions.** The second exception: some `x ∈ Spec A` has a formally real (orderable)
residue field `κ(x)`, and `cd₂ κ(x)(√−1) < ∞`, where `κ(x)(√−1)` is `κ(x)[X] ⧸ (X² + 1)`, a field
because `−1` is not a square in an orderable field.

## Stated

* `CdLowerBound`: the inequality off the two exceptions.
* `CdLowerBoundRegular`: for regular `A`, the inequality whenever `r ≠ char K`.

**Not stated.** The refinement for catenary universally japanese `A` (« `k` itself real »).
-/

open CategoryTheory AlgebraicGeometry IsLocalRing Polynomial

universe u

namespace OpenProblems.Findings.Folder31

/-- The `r`-cohomological dimension `cd_r(F)` of a field `F`: the infimum of the bounds `d` with
`H^p_ét(Spec F, 𝓖) = 0` for every abelian sheaf `𝓖` killed by `r` and every `p > d`. It is
defined for any commutative ring, through `Spec F`. -/
noncomputable def cdPrime (F : Type u) [CommRing F] (r : ℕ) : WithBot ℕ∞ :=
  sInf {d : WithBot ℕ∞ | Scheme.IsTorsionVanishingBound (Spec (.of F)) r d}

/-- `F(√−1)`: the quotient `F[X] ⧸ (X² + 1)`, a field when `−1` is not a square in `F`. -/
abbrev adjoinSqrtNegOne (F : Type u) [Field F] : Type u :=
  AdjoinRoot (X ^ 2 + 1 : F[X])

/-- The second exception of page 22: some point `x` of `Spec A` has an orderable residue field
`κ(x)` with `cd₂ κ(x)(√−1)` finite. -/
def RealException (A : Type u) [CommRing A] : Prop :=
  ∃ x : PrimeSpectrum A, IsFormallyReal x.asIdeal.ResidueField ∧
    cdPrime (adjoinSqrtNegOne x.asIdeal.ResidueField) 2 < ⊤

/-- **Folder 31, page 22.** For a noetherian local domain `A` with fraction field `K` and residue
field `k`, and a prime `r`: unless `r` is the characteristic of `K`, or `r = 2` and the real
exception holds, `cd_r(K) ≥ cd_r(k) + dim A`. -/
def CdLowerBound : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (r : ℕ),
    r.Prime → r ≠ ringChar (FractionRing A) → ¬ (r = 2 ∧ RealException A) →
      cdPrime (ResidueField A) r + ringKrullDim A ≤ cdPrime (FractionRing A) r

/-- **Folder 31, page 22, the regular case.** For a regular local ring `A` the second exception
disappears: `cd_r(K) ≥ cd_r(k) + dim A` for every prime `r` other than the characteristic of `K`. -/
def CdLowerBoundRegular : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRegularLocalRing A] (r : ℕ),
    r.Prime → r ≠ ringChar (FractionRing A) →
      cdPrime (ResidueField A) r + ringKrullDim A ≤ cdPrime (FractionRing A) r

end OpenProblems.Findings.Folder31
