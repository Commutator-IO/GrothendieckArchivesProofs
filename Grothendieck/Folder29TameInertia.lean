/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Grothendieck.Folder29
public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.AbhyankarLemma

@[expose] public section

/-!
# Folder 29, page 120: tame inertia through Abhyankar's lemma

Finding `29-inertia-matrix-determinant` of `src/content/findings.ts` (« Comportement fonctoriel
des groupes d'inertie », number 4, page 120 of `transcripts/29/29.modern.tex`). For a morphism
`f : X̄ → Ȳ` of strictly local regular schemes with normal crossings divisors `D̄ = Σ_{c ∈ C} D̄_c`
and `Ē = Σ_{c' ∈ C'} Ē_{c'}`, `f*(Ē_{c'}) = Σ_c n_{c,c'} D̄_c`, the map on tame inertia
`∏_{ℓ ≠ p} ℤ_ℓ(1)^C → ∏_{ℓ ≠ p} ℤ_ℓ(1)^{C'}` is the matrix `N = (n_{c,c'})`, and `N` is an
isomorphism iff `card C = card C'` and `det N = ± p^k`.

`Grothendieck/Folder29.lean` proved the criterion over each `ℤ_ℓ` (`Folder29.criterion`). This
file adds, from AxiomMath/Stacks (Apache-2.0), the local algebraic core of the Kummer computation
through Abhyankar's lemma, and the criterion on the finite quotients through which the tame
inertia acts on Kummer covers.

## Main results

* `finiteInertiaMap N e`: the map `(ℤ/e)^C → (ℤ/e)^{C'}` of `N`, on the quotient
  `μ_e^C ≅ (ℤ/e)^C` of (3.1) (`k(x̄)` separably closed, `p ∤ e`), the Galois group of the Kummer
  cover obtained by extracting `e`-th roots of the equations of the branches.
* `criterion_mod`: `N` is bijective modulo every `e ≥ 1` prime to `p` iff `card C = card C'` and
  `det N = ± p^k` (`p` prime, or `p = 1` in characteristic zero), the columns being matched with
  the rows by a bijection. With `card_eq_of_bijective_mod`, `bijective_mod_iff_isUnit_det`,
  `bijective_mod_submatrix_iff`, `isUnit_of_eq_pow`.
* `finiteInertiaMap_single_eq_zero_iff`: for one branch on each side, `N = (n)` kills `μ_e` iff
  `e ∣ n`.
* `abhyankar` (Stacks 0BRM, `formallySmooth_localizations_of_ramificationIndex_dvd`): for a tame
  extension of discrete valuation rings `A → B` of ramification index `e` and a finite extension
  `K₁` of the fraction field of `A` such that, at every maximal ideal of the normalisation `A₁`
  of `A` in `K₁`, the multiplicity `n = e(𝔭 / A)` kills `μ_e` in the sense above, every local
  factor of the normalisation of `B` in `L ⊗_K K₁` is formally smooth over `A₁`. This is the
  one-branch local core of the page: a tame cover of the generic point of a branch, of inertia
  `μ_e`, becomes unramified after the pull-back along a branch of multiplicity `n` as soon as the
  map `(n) : μ_e → μ_e` on inertia is zero (only this direction is proved; the converse, that a
  ramified cover stays ramified when `e ∤ n`, is not).

## Not formalised

Mathlib and Stacks have no tame fundamental group or inertia group of a
scheme, no strictly local regular scheme with a normal crossings divisor, and no Kummer
computation for several branches. So the canonical identification (3.1) of the tame inertia at
`x̄` with a quotient of `∏_{ℓ ≠ p} ℤ_ℓ(1)^C` (SGA 1 XIII 5.3), the statement that the map on
inertia is `N` (here only its one-branch, one-step algebraic shadow, through 0BRM), and the
consequence that the inertia subgroups of `H` at `y` are exactly the conjugates of the images of
those of `G` at `x` are not proved. Stacks 0EYG (Abhyankar's lemma for normal crossings divisors
on regular schemes, several branches) would be the route to the several-branch local core; its
import closure (4,384 modules) was not used.

## References

* A. Grothendieck, folder 29, page 120 (reading `transcripts/29/29.modern.tex`; finding
  `29-inertia-matrix-determinant`)
* [SGA 1] XIII 5.3
* Stacks Project, tags 0BRM, 0EYG
-/

open Matrix

namespace Grothendieck.Folder29TameInertia

variable {C C' : Type*} [Fintype C] [Fintype C']

/-- The map `(ℤ/e)^C → (ℤ/e)^{C'}` of an integer matrix with rows indexed by `C'` and columns by
`C`: the map `N` of page 120 on the quotient `μ_e^C ≅ (ℤ/e)^C` of the tame inertia (3.1). -/
def finiteInertiaMap (N : Matrix C' C ℤ) (e : ℕ) : (C → ZMod e) → (C' → ZMod e) :=
  (N.map (Int.cast : ℤ → ZMod e)).mulVec

/-- A matrix bijective modulo one prime `ℓ` is square. -/
theorem card_eq_of_bijective_mod (N : Matrix C' C ℤ) (ℓ : ℕ) [Fact ℓ.Prime]
    (h : Function.Bijective (finiteInertiaMap N ℓ)) : Fintype.card C = Fintype.card C' := by
  simpa using (LinearEquiv.ofBijective (N.map (Int.cast : ℤ → ZMod ℓ)).mulVecLin h).finrank_eq

/-- A square integer matrix is bijective modulo `e` iff its determinant is a unit modulo `e`. -/
theorem bijective_mod_iff_isUnit_det [DecidableEq C'] (M : Matrix C' C' ℤ) (e : ℕ) :
    Function.Bijective (finiteInertiaMap M e) ↔ IsUnit (M.det : ZMod e) := by
  rw [Int.cast_det, ← isUnit_iff_isUnit_det]
  exact ⟨fun h => mulVec_surjective_iff_isUnit.1 h.2,
    fun h => ⟨mulVec_injective_of_isUnit h, mulVec_surjective_iff_isUnit.2 h⟩⟩

/-- Reindexing the columns by a bijection does not change bijectivity modulo `e`. -/
theorem bijective_mod_submatrix_iff (N : Matrix C' C ℤ) (σ : C' ≃ C) (e : ℕ) :
    Function.Bijective (finiteInertiaMap (N.submatrix id σ) e) ↔
      Function.Bijective (finiteInertiaMap N e) := by
  have : finiteInertiaMap (N.submatrix id σ) e = finiteInertiaMap N e ∘ (· ∘ σ.symm) := by
    ext v
    simp [finiteInertiaMap, ← submatrix_map, submatrix_mulVec_equiv]
  rw [this, Function.Bijective.of_comp_iff]
  exact (σ.arrowCongr (Equiv.refl (ZMod e))).bijective

/-- `± p^k` is a unit modulo every `e` prime to `p`. -/
theorem isUnit_of_eq_pow {p e k : ℕ} (he : e.Coprime p) {d : ℤ}
    (hd : d = p ^ k ∨ d = -(p ^ k : ℤ)) : IsUnit (d : ZMod e) := by
  have hp : IsUnit ((p : ℕ) : ZMod e) := (ZMod.isUnit_iff_coprime p e).2 he.symm
  rcases hd with rfl | rfl <;> simpa using hp.pow k

/-- **The criterion of page 120 on the finite quotients `μ_e^C` of the tame inertia.** The
integer matrix `N` is bijective `(ℤ/e)^C → (ℤ/e)^{C'}` for every `e ≥ 1` prime to `p` iff
`card C = card C'` and, the columns being matched with the rows by some bijection,
`det N = ± p^k`. -/
theorem criterion_mod [DecidableEq C'] {p : ℕ} (hp : p = 1 ∨ p.Prime) (N : Matrix C' C ℤ) :
    (∀ e : ℕ, e ≠ 0 → e.Coprime p → Function.Bijective (finiteInertiaMap N e)) ↔
      Fintype.card C = Fintype.card C' ∧ ∃ σ : C' ≃ C, ∃ k : ℕ,
        (N.submatrix id σ).det = p ^ k ∨ (N.submatrix id σ).det = -(p ^ k : ℤ) := by
  have hcop : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ℓ.Coprime p := fun ℓ hℓ hℓp => by
    rcases hp with rfl | hp
    · exact Nat.coprime_one_right ℓ
    · exact (Nat.coprime_primes hℓ hp).2 hℓp
  constructor
  · intro h
    obtain ⟨ℓ, hℓp, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
    have := Fact.mk hℓ
    have hc := card_eq_of_bijective_mod N ℓ (h ℓ hℓ.ne_zero (hcop ℓ hℓ (by omega)))
    refine ⟨hc, Fintype.equivOfCardEq hc.symm, (Folder29.forall_not_dvd_iff hp _).1 ?_⟩
    intro q hq hqp hdvd
    have := Fact.mk hq
    have hu := (bijective_mod_iff_isUnit_det _ q).1
      ((bijective_mod_submatrix_iff N (Fintype.equivOfCardEq hc.symm) q).2
        (h q hq.ne_zero (hcop q hq hqp)))
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 hdvd] at hu
    exact not_isUnit_zero hu
  · rintro ⟨_, σ, hσ⟩ e _ he
    exact (bijective_mod_submatrix_iff N σ e).1
      ((bijective_mod_iff_isUnit_det _ e).2 (isUnit_of_eq_pow he hσ.choose_spec))

/-- **One branch.** For `C = C' = {*}` the matrix is the multiplicity `n` of the pull-back of the
branch, and it kills the quotient `μ_e ≅ ℤ/e` of the tame inertia iff `e ∣ n`: this is the
hypothesis of Abhyankar's lemma (`abhyankar` below). -/
theorem finiteInertiaMap_single_eq_zero_iff (n e : ℕ) :
    (∀ v, finiteInertiaMap (Matrix.of fun (_ : Unit) (_ : Unit) => (n : ℤ)) e v = 0) ↔ e ∣ n := by
  have key : ∀ v : Unit → ZMod e,
      finiteInertiaMap (Matrix.of fun (_ : Unit) (_ : Unit) => (n : ℤ)) e v = (n : ZMod e) • v := by
    intro v
    ext u
    simp [finiteInertiaMap, mulVec, dotProduct]
  simp_rw [key]
  refine ⟨fun h => (ZMod.natCast_eq_zero_iff n e).1 (by simpa using congrFun (h 1) ()),
    fun h v => by rw [(ZMod.natCast_eq_zero_iff n e).2 h, zero_smul]⟩


/-! ### Abhyankar's lemma (Stacks 0BRM): the one-branch local core -/

section Abhyankar

universe u v w x y

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
-- The statement carries the nested localization and tensor-product algebra structures of 0BRM.
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Abhyankar's lemma, in the language of page 120 (one branch).** Let `A → B` be an extension
of discrete valuation rings, tamely ramified of index `e` (residue characteristic `0`, or prime to
`e` with separable residue extension), and `K₁ / K` a finite extension. Suppose that at every
maximal ideal `𝔭` of the normalisation `A₁` of `A` in `K₁` the multiplicity `n = e(𝔭 / A)` of the
pull-back of the branch kills the quotient `μ_e ≅ ℤ/e` of the tame inertia (the one-branch matrix
`(n)` of `finiteInertiaMap` is zero modulo `e`, that is `e ∣ n`). Then the reduced ring
`L ⊗_K K₁` is a finite product of fields `E i`, and at every maximal ideal of the normalisation
of `B` in each `E i` the local ring is formally smooth (for the adic topology) over the local ring
of `A₁` below it: the tame ramification disappears. Stacks 0BRM. -/
theorem abhyankar
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (K₁ : Type y)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsDiscreteValuationRing.IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (htame : ringChar (IsLocalRing.ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (IsLocalRing.ResidueField A))
          (IsDiscreteValuationRing.ramificationIndex A B) ∧
        Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B))
    (hkill : ∀ p : Ideal (integralClosure A K₁), p.IsMaximal →
      ∀ v, finiteInertiaMap (Matrix.of fun (_ : Unit) (_ : Unit) => ((p.ramificationIdx A : ℕ) : ℤ))
        (IsDiscreteValuationRing.ramificationIndex A B) v = 0) :
    ∃ (n : ℕ) (E : Fin n → Type (max u v w x y))
      (_ : ∀ i, Field (E i))
      (_ : ∀ i, Algebra K (E i))
      (_ : ∀ i, Algebra L (E i))
      (_ : ∀ i, Algebra K₁ (E i))
      (_ : ∀ i, Algebra B (E i))
      (_ : ∀ i, IsScalarTower K L (E i))
      (_ : ∀ i, IsScalarTower K K₁ (E i))
      (_ : ∀ i, Module.Finite L (E i))
      (decomp : ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[K] ∀ i, E i),
      0 < n ∧
      (∀ i (z : L),
        decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) z)) i =
          algebraMap L (E i) z) ∧
      (∀ i (z : K₁),
        decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) z)) i =
          algebraMap K₁ (E i) z) ∧
      (∀ i (z : B), algebraMap B (E i) z =
        algebraMap L (E i) (algebraMap B L z)) ∧
      ∀ i, let A₁ := integralClosure A K₁
        let B₁ := integralClosure B (E i)
        ∃ f : A₁ →+* B₁,
          (∀ z : A₁, ((f z : B₁) : E i) =
            algebraMap K₁ (E i) ((z : A₁) : K₁)) ∧
          (∀ z : A, f (algebraMap A A₁ z) =
            algebraMap B B₁ (algebraMap A B z)) ∧
          ∀ p : Ideal A₁, p.IsMaximal →
            ∀ q : Ideal B₁, q.IsMaximal → q.comap f = p →
              ∃ (_ : q.IsPrime) (_ : p.IsPrime),
                (∃ _ : IsDomain (Localization p.primeCompl),
                  IsDiscreteValuationRing (Localization p.primeCompl)) ∧
                (∃ _ : IsDomain (Localization q.primeCompl),
                  IsDiscreteValuationRing (Localization q.primeCompl)) ∧
                ∃ φ : Localization p.primeCompl →+* Localization q.primeCompl,
                  Function.Injective φ ∧ IsLocalHom φ ∧
                    (∀ z : A₁, φ (algebraMap A₁ _ z) =
                      algebraMap B₁ _ (f z)) ∧
                    RingHom.FormallySmoothNAdic φ
                      (IsLocalRing.maximalIdeal (Localization q.primeCompl)) := by
  obtain ⟨n, E, hE, hKE, hLE, hK₁E, hBE, hKLE, hKK₁E, hfin, decomp, hn, hleft, hright, hB, hloc⟩ :=
    IsDiscreteValuationRing.formallySmooth_localizations_of_ramificationIndex_dvd
      A B K L K₁ htame
  refine ⟨n, E, hE, hKE, hLE, hK₁E, hBE, hKLE, hKK₁E, hfin, decomp, hn, hleft, hright, hB,
    fun i => ?_⟩
  obtain ⟨f, hf, hfA, hp⟩ := hloc i
  exact ⟨f, hf, hfA, fun p hpm =>
    hp p hpm ((finiteInertiaMap_single_eq_zero_iff _ _).1 (hkill p hpm))⟩

end Abhyankar

end Grothendieck.Folder29TameInertia
