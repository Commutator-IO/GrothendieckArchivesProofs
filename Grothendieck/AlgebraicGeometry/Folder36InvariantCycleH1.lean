/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Group.Prod
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.Abel
import Grothendieck.Attr

/-!
# Folder 36, pages 60–70: the defect of the invariant cycle theorem for `H¹`, the diagram chase

Finding `36-h1-invariant-cycle-defect`. For `X` projective and regular over a strictly henselian
trait, `O_S ≅ f_*O_X`, `X₀ = Σ dᵢ Dᵢ`, `Γ = Δ/ℤ·X₀ ⊂ Pic X` and `w : Γ → NS(X₀)`, the typescript
of pp. 60–63 states, for `n` prime to `p`, the exact sequence
`0 → ₙΓ → H¹(X, μₙ) → H¹(X_η̄, μₙ)^I → Ker wₙ → 0`. The manuscript of pp. 64–68 proves it when
`X_η` has a 0-cycle of degree `1`:

* Kummer theory identifies `H¹(X, μₙ)` with `ₙPic X` and `H¹(X_η̄, μₙ)^I` with `ₙPic X_η`, so
  that `uₙ` becomes `ₙv : ₙPic X → ₙPic X_η` (p. 64);
* `0 → Γ → Pic X → Pic X_η → 0` is exact (`X` regular), hence by the snake lemma for
  multiplication by `n`, `Coker uₙ ≅ Ker(iₙ : Γₙ → (Pic X)ₙ)` (p. 64);
* `Ker iₙ ⊂ Ker jₙ` for `j : Γ → Pic X₀`, with equality by the lemma « `Pic(X)ₙ ↪ Pic(X₀)ₙ` (du
  moins si `S` complet) »; `Pic⁰(X₀)` is `n`-divisible, so `Pic(X₀)ₙ ↪ NS(X₀)ₙ`, and
  `Coker uₙ ≅ Ker kₙ`, `k : Γ → NS(X₀)` (p. 66);
* with `Γ` torsion-free and `0 → Γ → NS(X₀) → δ → 0` exact, `Ker kₙ ≅ Coker ₙλ = ₙδ/ₙδ′`
  (p. 66), and the six-term sequence of `0 → δ′ → δ → δ″ → 0` (p. 68);
* `Γ` is torsion-free because `d = pgcd(dᵢ)` divides the degree `Σ dᵢ (Z·Dᵢ)` of every closed
  point of `X_η`, hence the gcd `d′ = 1` of the degrees (p. 68);
* page 70 drops the 0-cycle: `Γ` may have torsion `T`; with a splitting `Γ ≅ Γ′ ⊕ T`,
  `Ker(Γₙ → NS(X₀)ₙ) ≃ Tₙ + Ker(Γ′ₙ → NS(X₀)ₙ)`.

**The geometry is not formalised.** Schemes, `Pic`, `NS`, étale cohomology, Kummer theory, the
exact sequence `0 → Γ → Pic X → Pic X_η → 0`, the lemma `Pic(X)ₙ ↪ Pic(X₀)ₙ`, the divisibility
of `Pic⁰(X₀)`, the 0-cycle and the intersection numbers are **hypotheses**. What is proved is the
homological algebra the pages write, for abelian groups, with `ₙA = {x | n • x = 0}` (`tors`) and
`Aₙ = A/nA` (`Mod`).

## Main definitions

* `tors n A`, `Mod n A`, `torsMap n f`, `modMap n f`: `ₙA`, `A/nA` and the induced maps.
* `ShortExact i v`: `0 → G → P → Q → 0` exact.
* `delta h n : ₙQ →+ G/nG`: the connecting homomorphism of the snake lemma.

## Main results

* `torsMap_injective`, `exact_torsMap`, `exact_torsMap_delta`, `exact_delta_modMap`,
  `exact_modMap`, `modMap_surjective`: the six-term exact sequence
  `0 → ₙG → ₙP → ₙQ → G/n → P/n → Q/n → 0` (pp. 64, 68).
* `ker_modMap_comp`, `modMap_injective_of_divisible`: `Ker iₙ = Ker jₙ` when `Pic(X)ₙ ↪ Pic(X₀)ₙ`,
  and `Pic(X₀)ₙ ↪ NS(X₀)ₙ` when the kernel `Pic⁰(X₀)` is `n`-divisible (p. 66).
* `exact_sequence_six` (pp. 64–66, the sequence (6) of p. 61): from the Kummer identifications,
  `0 → ₙΓ → H → H′ → Ker kₙ → 0` is exact, `H`, `H′` standing for `H¹(X, μₙ)`,
  `H¹(X_η̄, μₙ)^I`.
* `kerModMapEquiv`, `torsMap_injective_of_torsionFree` (p. 66): for `0 → Γ → N → C → 0` exact,
  `Ker kₙ ≃ ₙC ⧸ ₙN`, and `ₙN → ₙC` is injective when `Γ` has no `n`-torsion.
* `gcd_dvd_sum_mul`, `gcd_eq_one_of_sum_mul_eq_one` (p. 68): `pgcd(dᵢ)` divides every
  `Σ dᵢ mᵢ`, hence is `1` if one such sum is `1`.
* `mk_mem_ker_modMap_prod` (p. 70): for `k : T × Γ′ → N` zero on `T`, `(t, g)` is in
  `Ker kₙ` iff `g` is in `Ker (k|Γ′)ₙ`.

## Not formalised

* Everything geometric listed above, and assertions a), b), d) of the typescript (`Ker w` torsion
  is referred to Raynaud on p. 68).
* The passage to the limit over `n = ℓ^ν`, `T_ℓ` and `R ⊗ ℤ_ℓ`; Corollaries 9, 10, 15; the case
  `p ∣ n`; on p. 70, the `p`-torsion of `Br(K)` and the identification of `R` with `Tors Γ`.

## References

* A. Grothendieck, folder 36, pp. 60–70 (finding `36-h1-invariant-cycle-defect`)
-/

@[expose] public section

namespace Grothendieck.Folder36

open Function

section Defs

variable (n : ℕ) (A : Type*) [AddCommGroup A]

/-- The `n`-torsion `ₙA = {x | n • x = 0}`. -/
def tors : AddSubgroup A where
  carrier := {x | n • x = 0}
  zero_mem' := smul_zero n
  add_mem' {x y} hx hy := by simp_all [smul_add]
  neg_mem' {x} hx := by simp_all [smul_neg]

/-- The subgroup `nA`. -/
def mult : AddSubgroup A where
  carrier := {x | ∃ y, n • y = x}
  zero_mem' := ⟨0, smul_zero n⟩
  add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, smul_add n x y⟩
  neg_mem' := by rintro _ ⟨x, rfl⟩; exact ⟨-x, smul_neg n x⟩

/-- `Aₙ = A/nA`. -/
abbrev Mod := A ⧸ mult n A

variable {n A}

@[simp]
theorem mem_tors {x : A} : x ∈ tors n A ↔ n • x = 0 := Iff.rfl

@[simp]
theorem mem_mult {x : A} : x ∈ mult n A ↔ ∃ y, n • y = x := Iff.rfl

end Defs

variable {n : ℕ} {G P Q : Type*} [AddCommGroup G] [AddCommGroup P] [AddCommGroup Q]

variable (n) in
/-- The map `ₙG → ₙP` induced by `f : G → P`. -/
def torsMap (f : G →+ P) : tors n G →+ tors n P :=
  (f.comp (tors n G).subtype).codRestrict (tors n P) fun x => by
    simp [← map_nsmul, (mem_tors.1 x.2 : n • (x : G) = 0)]

@[simp]
theorem coe_torsMap (f : G →+ P) (x : tors n G) : (torsMap n f x : P) = f x := rfl

variable (n) in
/-- The map `G/nG → P/nP` induced by `f : G → P`. -/
def modMap (f : G →+ P) : Mod n G →+ Mod n P :=
  QuotientAddGroup.map _ _ f (by rintro _ ⟨y, rfl⟩; exact ⟨f y, (map_nsmul f n y).symm⟩)

@[simp]
theorem modMap_mk (f : G →+ P) (x : G) :
    modMap n f (x : Mod n G) = (f x : Mod n P) := rfl

theorem modMap_comp (f : G →+ P) (g : P →+ Q) :
    modMap n (g.comp f) = (modMap n g).comp (modMap n f) :=
  QuotientAddGroup.addMonoidHom_ext _ rfl

theorem mk_eq_zero {x : G} : (x : Mod n G) = 0 ↔ ∃ y, n • y = x :=
  QuotientAddGroup.eq_zero_iff x

/-- A short exact sequence `0 → G → P → Q → 0` of abelian groups. -/
structure ShortExact (i : G →+ P) (v : P →+ Q) : Prop where
  injective : Injective i
  exact : Exact i v
  surjective : Surjective v

variable {i : G →+ P} {v : P →+ Q}

namespace ShortExact

variable (h : ShortExact i v)
include h

theorem exists_lift (q : tors n Q) : ∃ γ : G, ∃ p : P, v p = q ∧ i γ = n • p := by
  obtain ⟨p, hp⟩ := h.surjective q
  obtain ⟨γ, hγ⟩ := (h.exact (n • p)).1 (by simp [hp, mem_tors.1 q.2])
  exact ⟨γ, p, hp, hγ⟩

/-- The connecting map `ₙQ → G/nG` as a function: lift `q` to `p`, write `n • p = i γ`. -/
noncomputable def deltaFun (n : ℕ) (q : tors n Q) : Mod n G :=
  (Classical.choose (h.exists_lift q) : G)

/-- The connecting map does not depend on the lifts. -/
theorem deltaFun_eq (q : tors n Q) {p : P} {γ : G} (hp : v p = q) (hγ : i γ = n • p) :
    h.deltaFun n q = (γ : Mod n G) := by
  obtain ⟨p₀, hp₀, hγ₀⟩ := Classical.choose_spec (h.exists_lift q)
  obtain ⟨g, hg⟩ := (h.exact (p - p₀)).1 (by simp [hp, hp₀])
  refine QuotientAddGroup.eq.2 (mem_mult.2 ⟨g, h.injective ?_⟩)
  simp only [map_add, map_neg, map_nsmul, hg, hγ, hγ₀, smul_sub]
  abel

/-- The connecting homomorphism `δ : ₙQ → G/nG` of the snake lemma for multiplication by `n`. -/
noncomputable def delta (n : ℕ) : tors n Q →+ Mod n G where
  toFun := h.deltaFun n
  map_zero' := h.deltaFun_eq 0 (p := 0) (γ := 0) (by simp) (by simp)
  map_add' q₁ q₂ := by
    obtain ⟨γ₁, p₁, hp₁, hγ₁⟩ := h.exists_lift q₁
    obtain ⟨γ₂, p₂, hp₂, hγ₂⟩ := h.exists_lift q₂
    rw [h.deltaFun_eq q₁ hp₁ hγ₁, h.deltaFun_eq q₂ hp₂ hγ₂,
      h.deltaFun_eq (q₁ + q₂) (p := p₁ + p₂) (γ := γ₁ + γ₂) (by simp [hp₁, hp₂])
        (by simp [hγ₁, hγ₂, smul_add])]
    rfl

theorem delta_eq (q : tors n Q) {p : P} {γ : G} (hp : v p = q) (hγ : i γ = n • p) :
    h.delta n q = (γ : Mod n G) :=
  h.deltaFun_eq q hp hγ

/-- `36-h1-invariant-cycle-defect` (folder 36, pp. 64, 68): `0 → ₙG → ₙP`. -/
@[montpellier "36, 64, 68"]
theorem torsMap_injective : Injective (torsMap n i) := fun _ _ hxy =>
  Subtype.ext (h.injective (congrArg Subtype.val hxy))

/-- `36-h1-invariant-cycle-defect` (folder 36, pp. 64, 68): `ₙG → ₙP → ₙQ` is exact. -/
@[montpellier "36, 64, 68"]
theorem exact_torsMap : Exact (torsMap n i) (torsMap n v) := by
  intro y
  constructor
  · intro hy
    obtain ⟨γ, hγ⟩ := (h.exact y).1 (congrArg Subtype.val hy)
    refine ⟨⟨γ, h.injective ?_⟩, Subtype.ext hγ⟩
    simp [hγ, mem_tors.1 y.2]
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((h.exact _).2 ⟨x, rfl⟩)

/-- `36-h1-invariant-cycle-defect` (folder 36, pp. 64, 68): `ₙP → ₙQ → G/nG` is exact. -/
@[montpellier "36, 64, 68"]
theorem exact_torsMap_delta : Exact (torsMap n v) (h.delta n) := by
  intro q
  constructor
  · intro hq
    obtain ⟨γ, p, hp, hγ⟩ := h.exists_lift q
    obtain ⟨g, hg⟩ := mk_eq_zero.1 ((h.delta_eq q hp hγ).symm.trans hq)
    refine ⟨⟨p - i g, ?_⟩, Subtype.ext ?_⟩
    · simp [smul_sub, ← map_nsmul, hg, hγ]
    · simp [hp, (h.exact _).2 ⟨g, rfl⟩]
  · rintro ⟨p, rfl⟩
    exact (h.delta_eq _ (p := p) (γ := 0) rfl (by simp [mem_tors.1 p.2])).trans
      (QuotientAddGroup.mk_zero _)

/-- `36-h1-invariant-cycle-defect` (folder 36, pp. 64, 68): `ₙQ → G/nG → P/nP` is exact. -/
@[montpellier "36, 64, 68"]
theorem exact_delta_modMap : Exact (h.delta n) (modMap n i) := by
  intro x
  induction x using QuotientAddGroup.induction_on with | H γ => ?_
  rw [modMap_mk, mk_eq_zero]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨⟨v p, by simp [← map_nsmul, hp, (h.exact _).2 ⟨γ, rfl⟩]⟩,
      h.delta_eq _ rfl hp.symm⟩
  · rintro ⟨q, hq⟩
    obtain ⟨γ₀, p₀, hp₀, hγ₀⟩ := h.exists_lift q
    obtain ⟨g, hg⟩ := QuotientAddGroup.eq.1 ((h.delta_eq q hp₀ hγ₀).symm.trans hq)
    refine ⟨p₀ + i g, ?_⟩
    rw [smul_add, ← hγ₀, ← map_nsmul, ← map_add, hg, add_neg_cancel_left]

/-- `36-h1-invariant-cycle-defect` (folder 36, pp. 64, 68): `G/nG → P/nP → Q/nQ` is exact. -/
@[montpellier "36, 64, 68"]
theorem exact_modMap : Exact (modMap n i) (modMap n v) := by
  intro x
  induction x using QuotientAddGroup.induction_on with | H p => ?_
  rw [modMap_mk, mk_eq_zero]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨p', rfl⟩ := h.surjective q
    obtain ⟨γ, hγ⟩ := (h.exact (p - n • p')).1 (by simp [hq])
    refine ⟨(γ : Mod n G), QuotientAddGroup.eq.2 ⟨p', ?_⟩⟩
    simp [hγ]
  · rintro ⟨y, hy⟩
    induction y using QuotientAddGroup.induction_on with | H γ => ?_
    obtain ⟨p', hp'⟩ := QuotientAddGroup.eq.1 hy
    refine ⟨v p', ?_⟩
    rw [← map_nsmul, hp', map_add, map_neg, (h.exact _).2 ⟨γ, rfl⟩, neg_zero, zero_add]

/-- `36-h1-invariant-cycle-defect` (folder 36, pp. 64, 68): `P/nP → Q/nQ → 0`. -/
@[montpellier "36, 64, 68"]
theorem modMap_surjective : Surjective (modMap n v) := by
  intro x
  induction x using QuotientAddGroup.induction_on with | H q => ?_
  obtain ⟨p, rfl⟩ := h.surjective q
  exact ⟨p, rfl⟩

theorem range_delta : (h.delta n).range = (modMap n i).ker :=
  AddSubgroup.ext fun x => (h.exact_delta_modMap x).symm

theorem ker_delta : (h.delta n).ker = (torsMap n v).range :=
  AddSubgroup.ext h.exact_torsMap_delta

end ShortExact

variable {P₀ N : Type*} [AddCommGroup P₀] [AddCommGroup N]

/-- `36-h1-invariant-cycle-defect` (folder 36, p. 66): `Ker iₙ ⊂ Ker jₙ` for `j = r ∘ i`, with
equality when `rₙ` is injective (the lemma `Pic(X)ₙ ↪ Pic(X₀)ₙ`). -/
@[montpellier "36, 66"]
theorem ker_modMap_comp (r : P →+ P₀) (hr : Injective (modMap n r)) :
    (modMap n (r.comp i)).ker = (modMap n i).ker := by
  rw [modMap_comp]
  exact AddMonoidHom.ker_comp_of_injective _ _ hr

/-- `36-h1-invariant-cycle-defect` (folder 36, p. 66): `Pic(X₀)ₙ ↪ NS(X₀)ₙ`, for
`s : Pic(X₀) → NS(X₀)` surjective with `n`-divisible kernel `Pic⁰(X₀)`. -/
@[montpellier "36, 66"]
theorem modMap_injective_of_divisible (s : P₀ →+ N) (hs : Surjective s)
    (hdiv : ∀ x, s x = 0 → ∃ y, s y = 0 ∧ n • y = x) : Injective (modMap n s) := by
  rw [injective_iff_map_eq_zero]
  intro x
  induction x using QuotientAddGroup.induction_on with | H x => ?_
  rw [modMap_mk, mk_eq_zero, mk_eq_zero]
  rintro ⟨z, hz⟩
  obtain ⟨w, rfl⟩ := hs z
  obtain ⟨y, -, hy⟩ := hdiv (x - n • w) (by simp [hz])
  exact ⟨w + y, by rw [smul_add, hy, add_sub_cancel]⟩

/-- `36-h1-invariant-cycle-defect` (folder 36, pp. 64–66; the sequence (6) of p. 61): with
`0 → Γ → Pic X → Pic X_η → 0` exact (`h`), the Kummer identifications `α : H ≃ ₙPic X`,
`α′ : H′ ≃ ₙPic X_η` carrying `u` to `ₙv` (`H`, `H′` for `H¹(X, μₙ)`, `H¹(X_η̄, μₙ)^I`), the lemma
`Pic(X)ₙ ↪ Pic(X₀)ₙ` (`hr`) and `Pic(X₀) → NS(X₀)` surjective with `n`-divisible kernel, the
sequence `0 → ₙΓ → H → H′ → Ker kₙ → 0` is exact, `k : Γ → NS(X₀)` the composite. -/
@[montpellier "36, 61, 64, 66"]
theorem exact_sequence_six (h : ShortExact i v) {H H' : Type*} [AddCommGroup H]
    [AddCommGroup H'] (u : H →+ H') (α : H ≃+ tors n P) (α' : H' ≃+ tors n Q)
    (hu : ∀ x, α' (u x) = torsMap n v (α x)) (r : P →+ P₀) (hr : Injective (modMap n r))
    (s : P₀ →+ N) (hs : Surjective s) (hdiv : ∀ x, s x = 0 → ∃ y, s y = 0 ∧ n • y = x) :
    Injective (α.symm.toAddMonoidHom.comp (torsMap n i)) ∧
      Exact (α.symm.toAddMonoidHom.comp (torsMap n i)) u ∧
      Exact u ((h.delta n).comp α'.toAddMonoidHom) ∧
      ((h.delta n).comp α'.toAddMonoidHom).range = (modMap n (s.comp (r.comp i))).ker := by
  refine ⟨α.symm.injective.comp h.torsMap_injective, fun y => ?_, fun y => ?_, ?_⟩
  · have := h.exact_torsMap (α y)
    rw [← hu, AddEquiv.map_eq_zero_iff] at this
    rw [this]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, by simp [hx]⟩, fun ⟨x, hx⟩ => ⟨x, by simp [← hx]⟩⟩
  · change h.delta n (α' y) = 0 ↔ y ∈ Set.range u
    rw [h.exact_torsMap_delta (α' y)]
    exact ⟨fun ⟨x, hx⟩ => ⟨α.symm x, α'.injective (by rw [hu, AddEquiv.apply_symm_apply, hx])⟩,
      fun ⟨x, hx⟩ => ⟨α x, by rw [← hu, hx]⟩⟩
  · rw [AddMonoidHom.range_comp, AddMonoidHom.range_eq_top.2 α'.surjective, AddSubgroup.map_top,
      h.range_delta, modMap_comp, AddMonoidHom.ker_comp_of_injective _ _
        (modMap_injective_of_divisible s hs hdiv), ker_modMap_comp r hr]

/-- `36-h1-invariant-cycle-defect` (folder 36, p. 66): for `0 → Γ → NS(X₀) → δ → 0` exact,
`Ker kₙ ≅ Coker(ₙλ : ₙNS(X₀) → ₙδ)`. -/
@[montpellier "36, 66"]
noncomputable def kerModMapEquiv (h : ShortExact i v) :
    (modMap n i).ker ≃+ tors n Q ⧸ (torsMap n v).range :=
  (AddEquiv.addSubgroupCongr h.range_delta.symm).trans
    ((QuotientAddGroup.quotientKerEquivRange (h.delta n)).symm.trans
      (QuotientAddGroup.quotientAddEquivOfEq h.ker_delta))

/-- `36-h1-invariant-cycle-defect` (folder 36, p. 66): if `Γ` has no `n`-torsion, `ₙNS(X₀) → ₙδ`
is injective, so `Ker kₙ ≅ ₙδ/ₙNS(X₀)`. -/
@[montpellier "36, 66"]
theorem torsMap_injective_of_torsionFree (h : ShortExact i v)
    (hG : ∀ g : G, n • g = 0 → g = 0) : Injective (torsMap n v) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := (h.exact_torsMap y).1 hy
  rw [show x = 0 from Subtype.ext (hG x (mem_tors.1 x.2)), map_zero]

/-- `36-h1-invariant-cycle-defect` (folder 36, p. 68): `d = pgcd(dᵢ)` divides the degree
`Σ dᵢ (Z·Dᵢ)` of a closed point of `X_η`. -/
@[montpellier "36, 68"]
theorem gcd_dvd_sum_mul {J : Type*} (s : Finset J) (d m : J → ℕ) :
    s.gcd d ∣ ∑ j ∈ s, d j * m j :=
  Finset.dvd_sum fun _ hj => Dvd.dvd.mul_right (Finset.gcd_dvd hj) _

/-- `36-h1-invariant-cycle-defect` (folder 36, p. 68): if some such degree is `1` (a 0-cycle of
degree `1`, `d′ = 1`), then `d = 1`. -/
@[montpellier "36, 68"]
theorem gcd_eq_one_of_sum_mul_eq_one {J : Type*} (s : Finset J) (d m : J → ℕ)
    (h : ∑ j ∈ s, d j * m j = 1) : s.gcd d = 1 :=
  Nat.dvd_one.1 (h ▸ gcd_dvd_sum_mul s d m)

/-- `36-h1-invariant-cycle-defect` (folder 36, p. 70): with a splitting `Γ ≅ T × Γ′` and
`k : Γ → NS(X₀)` zero on `T`, `(t, g)` lies in `Ker kₙ` iff `g` lies in `Ker (k|Γ′)ₙ`:
`Ker(Γₙ → NS(X₀)ₙ) ≃ Tₙ + Ker(Γ′ₙ → NS(X₀)ₙ)`. -/
@[montpellier "36, 70"]
theorem mk_mem_ker_modMap_prod {T Γ' : Type*} [AddCommGroup T] [AddCommGroup Γ']
    (k : T × Γ' →+ N) (hk : ∀ t, k (t, 0) = 0) (t : T) (g : Γ') :
    ((t, g) : Mod n (T × Γ')) ∈ (modMap n k).ker ↔
      (g : Mod n Γ') ∈ (modMap n (k.comp (AddMonoidHom.inr T Γ'))).ker := by
  have : k (t, g) = k (0, g) := by
    rw [show ((t, g) : T × Γ') = (t, 0) + (0, g) by simp, map_add, hk, zero_add]
  simp [this]

end Grothendieck.Folder36
