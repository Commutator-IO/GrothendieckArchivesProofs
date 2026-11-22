/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheory

/-!
# Folder 16, page 49: `A⁰(X)`, `A′⁰(X)`, `A″⁰(X)` in a classical Weil cohomology theory

The reading (« Les variantes faibles, qui ne le sont pas ») introduces, for a smooth projective
`X` of dimension `n`, polarised by `ξ`, with a smooth hyperplane section `φ : Y → X`,
* `A′(X)`: for `2i ≤ n − 1`, a class of `H^{2i}(X)` whose restriction to `Y` is algebraic is
  algebraic;
* `A″(X)`: for `2i ≥ n − 1`, every algebraic class of `H^{2i+2}(X)` is `φ_*` of an algebraic
  class of `H^{2i}(Y)`;
* `A′⁰`, `A″⁰`: their restrictions to the critical dimension, `2i = n − 1` (`n` odd) and
  `2i = n − 2` (`n` even);
and claims that `A⁰(X)` — the Lefschetz-type statement on algebraic classes in the critical
dimension, `L : Z^i → Z^{i+1}` (`n = 2i + 1`) or `L² : Z^i → Z^{i+2}` (`n = 2i + 2`) onto — follows
from `A′⁰(X) + A″⁰(X)`, « comme on le voit en décomposant l'opérateur de la dimension critique à
travers la section hyperplane » (`L = φ_*φ^*`). This is the step of the finding
`16-weak-variants-imply-strong` that the edition did not find in the literature.

Everything is stated inside a classical Weil cohomology theory `T` (Stacks 0FGV,
`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory`), with algebraic classes the `F`-span of
the image of the cycle class map. Hard and weak Lefschetz, the identity `L = φ_*φ^*` (which needs
`γ(Y) = ξ`) and the projection formula are not axioms there; they enter as explicit hypotheses.

**What is proved.**
* `algebraicClasses`, `lefschetzOp` (cup product with `ξ = γ(h)`, `h ∈ CH¹(X)`), and
  `sectionPushforward` (the Gysin map `H^{2r}(Y) → H^{2r+2}(X)` of the Poincaré-duality
  pushforward, for `dim X = dim Y + 1`); `pullback_mem`, `lefschetzOp_mem`,
  `sectionPushforward_mem`: `φ^*`, `L` and `φ_*` carry algebraic classes to algebraic classes
  (from the axioms `cycleClass_gysin`, `cycleClass_mul`, `cycleClass_pushforward`).
* The page's conditions: `AZero`, `APrime`, `APrimeZero`, `ADoublePrime`, `ADoublePrimeZero`, and
  the inclusions `aPrimeZero_of_aPrime`, `aDoublePrimeZero_odd_of_aDoublePrime`.
* The « trivial » direction: under `L = φ_*φ^*` and hard Lefschetz (injectivity of `L`, resp.
  `L²`, in the critical degree), `A⁰(X) ⇒ A′⁰(X)` (`aPrimeZero_of_aZero`) and, for `n` odd,
  `A⁰(X) ⇒ A″⁰(X)` (`aDoublePrimeZero_odd_of_aZero`).
* `n` odd: `aZero_odd_iff`: under hard Lefschetz, `L = φ_*φ^*` and the hypothesis that the
  algebraic classes of the middle degree of `Y` split along `H^{2i}(Y) = Im φ^* ⊕ Ker φ_*`,
  `A⁰ ⇔ A′⁰ + A″⁰` in degree `i`. `odd_step_fails_without_splitting`: the splitting cannot be
  dropped — a model over `ℚ` with `L = φ_*φ^*` bijective, `φ^*` injective, `φ_*` onto, satisfying
  `A′⁰` and `A″⁰` and not `A⁰`; so the factorisation alone does not give the step.
* `n` even: `lefschetz_surj_of_aPrimeZero_even`: `A′⁰ + A″⁰` and weak Lefschetz give only the
  first half, `L : Z^i(X) → Z^{i+1}(X)` onto; `aZero_even_of`: `A′⁰(X)`, the next case of `A″(X)`
  (degree `2i + 2`, inside the range of `A″`) and `A⁰(Y)` give `A⁰(X)`, through
  `L² = L φ_* φ^* = φ_* L_Y φ^*`.
* `aZero_of`: the two together, `A′⁰(X) + A″(X) + A⁰(Y) ⇒ A⁰(X)` (with the splitting for `n`
  odd).

**How.** The statements reduce to linear algebra of three or five vector spaces with subspaces of
algebraic classes (`odd_step`, `odd_converse`, `even_step`, `even_first_half`,
`even_converse`); the Weil theory supplies the spaces, the maps and their compatibility with
algebraic classes, the degree identifications being `ExternallyGraded.degreeCast`.

**Not formalised.** Hyperplane sections, `γ(Y) = ξ`, the projection formula, and weak and hard
Lefschetz are hypotheses, not theorems of the theory. The full `A(X)` (all `L^{n−2i}`), hence
`A(X) ⇒ A′(X)` and `C(Y) ⇒ A″(X)` outside the critical dimension, and `C(X)` itself (the
algebraicity of `Λ` as a correspondence), with the equivalence
`C(X) ⇔ C(Y) + A′⁰(X×X) + A″⁰(X×X)` and its descent along hyperplane sections (Kleiman 1968,
Theorem 2.13, for the form with `A⁰`). Whether the splitting of `Z^i(Y)` holds in an actual Weil
cohomology: the model of `odd_step_fails_without_splitting` is linear algebra, not a variety. For
`n` even the reading's `A″⁰` (at `2i = n − 2`) lies outside the range `2i ≥ n − 1` of `A″`, so
`A″ ⇒ A″⁰` is only stated for `n` odd.
-/

@[expose] public section


open CategoryTheory AlgebraicGeometry Stacks.WeilCohomology

universe u v w t

namespace Grothendieck.Folder16Problem5

/-! ## Linear algebra of the critical dimension -/

section Abstract

variable {K : Type*} [Field K] {V W U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W] [AddCommGroup U] [Module K U]

/-- `n` odd, the step `A′⁰ + A″⁰ ⇒ A⁰` through `L = q ∘ p` (`p = φ^*`, `q = φ_*`), granted that the
algebraic classes `Z_W` of the middle space split along `Im p` and `Ker q`. -/
theorem odd_step {p : V →ₗ[K] W} {q : W →ₗ[K] U} {L : V →ₗ[K] U} (hL : ∀ x, L x = q (p x))
    {ZV : Submodule K V} {ZW : Submodule K W} {ZU : Submodule K U}
    (hA' : ∀ x, p x ∈ ZW → x ∈ ZV) (hA'' : ∀ z ∈ ZU, ∃ y ∈ ZW, q y = z)
    (hsplit : ZW ≤ (ZW ⊓ LinearMap.range p) ⊔ (ZW ⊓ LinearMap.ker q)) :
    ∀ z ∈ ZU, ∃ x ∈ ZV, L x = z := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hA'' z hz
  obtain ⟨a, ha, e, he, rfl⟩ := Submodule.mem_sup.1 (hsplit hy)
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 (Submodule.mem_inf.1 ha).2
  refine ⟨x, hA' x (Submodule.mem_inf.1 ha).1, ?_⟩
  rw [hL, map_add, LinearMap.mem_ker.1 (Submodule.mem_inf.1 he).2, add_zero]

/-- `n` odd, the converse `A⁰ ⇒ A′⁰ + A″⁰`, for `L = q ∘ p` injective. -/
theorem odd_converse {p : V →ₗ[K] W} {q : W →ₗ[K] U} {L : V →ₗ[K] U} (hL : ∀ x, L x = q (p x))
    {ZV : Submodule K V} {ZW : Submodule K W} {ZU : Submodule K U}
    (hp : ∀ x ∈ ZV, p x ∈ ZW) (hq : ∀ y ∈ ZW, q y ∈ ZU) (hinj : Function.Injective L)
    (hA : ∀ z ∈ ZU, ∃ x ∈ ZV, L x = z) :
    (∀ x, p x ∈ ZW → x ∈ ZV) ∧ (∀ z ∈ ZU, ∃ y ∈ ZW, q y = z) := by
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · obtain ⟨x', hx', he⟩ := hA (L x) (by rw [hL]; exact hq _ hx)
    rwa [hinj he] at hx'
  · obtain ⟨x, hx, rfl⟩ := hA z hz
    exact ⟨p x, hp x hx, (hL x).symm⟩

/-- Without the splitting, `n` odd: `L = q ∘ p` bijective, `p` injective, `q` onto, `A′⁰` and `A″⁰`
hold, the maps respect algebraic classes, and `A⁰` fails. Here `V = U = ℚ`, `W = ℚ²`,
`p = (1, 0)`, `q = pr₁`, `Z_V = 0`, `Z_W = ℚ·(1, 1)`, `Z_U = ℚ`. -/
theorem odd_step_fails_without_splitting :
    ∃ (p : ℚ →ₗ[ℚ] ℚ × ℚ) (q : ℚ × ℚ →ₗ[ℚ] ℚ) (ZV : Submodule ℚ ℚ)
      (ZW : Submodule ℚ (ℚ × ℚ)) (ZU : Submodule ℚ ℚ),
      Function.Bijective (q.comp p) ∧ Function.Injective p ∧ Function.Surjective q ∧
      (∀ x ∈ ZV, p x ∈ ZW) ∧ (∀ y ∈ ZW, q y ∈ ZU) ∧
      (∀ x, p x ∈ ZW → x ∈ ZV) ∧ (∀ z ∈ ZU, ∃ y ∈ ZW, q y = z) ∧
      ¬ ∀ z ∈ ZU, ∃ x ∈ ZV, q (p x) = z := by
  refine ⟨LinearMap.inl ℚ ℚ ℚ, LinearMap.fst ℚ ℚ ℚ, ⊥, Submodule.span ℚ {((1 : ℚ), (1 : ℚ))}, ⊤,
    ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    simpa using h
  · intro z
    exact ⟨z, by simp⟩
  · exact LinearMap.inl_injective
  · intro z
    exact ⟨(z, 0), by simp⟩
  · intro x hx
    rw [Submodule.mem_bot] at hx
    subst hx
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro _ _
    exact Submodule.mem_top
  · intro x hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
    have h2 : c = 0 := by simpa using congrArg Prod.snd hc
    have h1 : c = x := by simpa using congrArg Prod.fst hc
    rw [Submodule.mem_bot, ← h1, h2]
  · intro z _
    exact ⟨(z, z), Submodule.mem_span_singleton.2 ⟨z, by simp⟩, by simp⟩
  · intro h
    obtain ⟨x, hx, hx1⟩ := h 1 Submodule.mem_top
    rw [Submodule.mem_bot] at hx
    subst hx
    simp at hx1

variable {W₁ U₁ U₂ : Type*} [AddCommGroup W₁] [Module K W₁] [AddCommGroup U₁] [Module K U₁]
  [AddCommGroup U₂] [Module K U₂]

/-- `n` even, first half: `A′⁰ + A″⁰` (at `2i = n − 2`) and `p` onto give `L₁ = q₀ ∘ p` onto the
algebraic classes. -/
theorem even_first_half {p : V →ₗ[K] W} {q₀ : W →ₗ[K] U₁} {L₁ : V →ₗ[K] U₁}
    (hL : ∀ x, L₁ x = q₀ (p x)) (hp : Function.Surjective p)
    {ZV : Submodule K V} {ZW : Submodule K W} {ZU₁ : Submodule K U₁}
    (hA' : ∀ x, p x ∈ ZW → x ∈ ZV) (hA'' : ∀ z ∈ ZU₁, ∃ y ∈ ZW, q₀ y = z) :
    ∀ z ∈ ZU₁, ∃ x ∈ ZV, L₁ x = z := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hA'' z hz
  obtain ⟨x, rfl⟩ := hp y
  exact ⟨x, hA' x hy, hL x⟩

/-- `n` even: `L₂ ∘ L₁ = L₂ ∘ q₀ ∘ p = q₁ ∘ L_Y ∘ p`, so `A′⁰`, `A″` one degree up (`q₁`) and the
Lefschetz condition `A⁰` on the section (`L_Y`) give `A⁰`. -/
theorem even_step {p : V →ₗ[K] W} {q₀ : W →ₗ[K] U₁} {q₁ : W₁ →ₗ[K] U₂} {L₁ : V →ₗ[K] U₁}
    {L₂ : U₁ →ₗ[K] U₂} {LY : W →ₗ[K] W₁} (hL : ∀ x, L₁ x = q₀ (p x))
    (hproj : ∀ w, L₂ (q₀ w) = q₁ (LY w)) (hp : Function.Surjective p)
    {ZV : Submodule K V} {ZW : Submodule K W} {ZW₁ : Submodule K W₁} {ZU₂ : Submodule K U₂}
    (hA' : ∀ x, p x ∈ ZW → x ∈ ZV) (hA'' : ∀ z ∈ ZU₂, ∃ y ∈ ZW₁, q₁ y = z)
    (hAY : ∀ y ∈ ZW₁, ∃ w ∈ ZW, LY w = y) :
    ∀ z ∈ ZU₂, ∃ x ∈ ZV, L₂ (L₁ x) = z := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hA'' z hz
  obtain ⟨w, hw, rfl⟩ := hAY y hy
  obtain ⟨x, rfl⟩ := hp w
  exact ⟨x, hA' x hw, by rw [hL, hproj]⟩

/-- `n` even, the converse `A⁰ ⇒ A′⁰`, for `L₂ ∘ L₁` injective. -/
theorem even_converse {p : V →ₗ[K] W} {q₀ : W →ₗ[K] U₁} {L₁ : V →ₗ[K] U₁} {L₂ : U₁ →ₗ[K] U₂}
    (hL : ∀ x, L₁ x = q₀ (p x))
    {ZV : Submodule K V} {ZW : Submodule K W} {ZU₁ : Submodule K U₁} {ZU₂ : Submodule K U₂}
    (hq₀ : ∀ y ∈ ZW, q₀ y ∈ ZU₁) (hL₂ : ∀ u ∈ ZU₁, L₂ u ∈ ZU₂)
    (hinj : Function.Injective fun x => L₂ (L₁ x)) (hA : ∀ z ∈ ZU₂, ∃ x ∈ ZV, L₂ (L₁ x) = z) :
    ∀ x, p x ∈ ZW → x ∈ ZV := by
  intro x hx
  obtain ⟨x', hx', he⟩ := hA (L₂ (L₁ x)) (hL₂ _ (by rw [hL]; exact hq₀ _ hx))
  rwa [hinj he] at hx'

end Abstract

/-! ## In a classical Weil cohomology theory -/

section Weil

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  {Ch : ChowCycleData.{u, t} k} (T : ClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch)

omit [CharZero F] in
/-- Two transports of degree compose to one. -/
theorem degreeCast_trans {P : ℤ → Type*} [∀ n, AddCommGroup (P n)] [∀ n, Module F (P n)]
    {i j l : ℤ} (h₁ : i = j) (h₂ : j = l) (x : P i) :
    ExternallyGraded.degreeCast (R := F) (X := P) h₂
        (ExternallyGraded.degreeCast (R := F) (X := P) h₁ x) =
      ExternallyGraded.degreeCast (R := F) (X := P) (h₁.trans h₂) x :=
  eq_of_heq (((ExternallyGraded.degreeCast_heq (R := F) (X := P) h₂ _).trans
    (ExternallyGraded.degreeCast_heq (R := F) (X := P) h₁ x)).trans
      (ExternallyGraded.degreeCast_heq (R := F) (X := P) (h₁.trans h₂) x).symm)

/-- The algebraic classes `Z^r(X) ⊆ H^{2r}(X)`: the `F`-span of the image of the cycle class
map `γ : CHʳ(X) → H^{2r}(X)`. -/
def algebraicClasses (X : (SmoothProjective k).FullSubcategory) (r : ℤ) :
    Submodule F ((T.H X).piece (2 * r)) :=
  Submodule.span F (Set.range (T.cycleClass X r))

theorem degreeCast_mem_algebraicClasses (X : (SmoothProjective k).FullSubcategory) {r s : ℤ}
    (hrs : r = s) (h : 2 * r = 2 * s) {x : (T.H X).piece (2 * r)}
    (hx : x ∈ algebraicClasses T X r) :
    ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece) h x ∈ algebraicClasses T X s := by
  subst hrs
  rw [eq_of_heq (ExternallyGraded.degreeCast_heq (R := F) (X := (T.H X).piece) h x)]
  exact hx

/-- The Lefschetz operator `L = ξ ∪ − : H^{2r}(X) → H^{2r+2}(X)` of the polarisation
`ξ = γ(h)`, `h ∈ CH¹(X)`. -/
noncomputable def lefschetzOp (X : (SmoothProjective k).FullSubcategory) (h : Ch.group X 1)
    (r : ℤ) : (T.H X).piece (2 * r) →ₗ[F] (T.H X).piece (2 * (r + 1)) :=
  (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece) (by ring)).comp
    ((T.H X).evenCup 1 r (T.cycleClass X 1 h))

/-- The Gysin map `φ_* : H^{2r}(Y) → H^{2r+2}(X)` of a morphism `φ : Y → X` with
`dim X = dim Y + 1`: the pushforward determined by Poincaré duality. -/
noncomputable def sectionPushforward {X Y : (SmoothProjective k).FullSubcategory} (φ : Y ⟶ X)
    (hdim : T.dimension X = T.dimension Y + 1) (r : ℤ) :
    (T.H Y).piece (2 * r) →ₗ[F] (T.H X).piece (2 * (r + 1)) :=
  (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece)
      (show 2 * (T.dimension X : ℤ) - (2 * (T.dimension Y : ℤ) - 2 * r) = 2 * (r + 1) by
        omega)).comp
    ((T.pushforward φ (2 * (T.dimension Y : ℤ) - 2 * r)).comp
      (ExternallyGraded.degreeCast (R := F) (X := (T.H Y).piece)
        (show 2 * r = 2 * (T.dimension Y : ℤ) - (2 * (T.dimension Y : ℤ) - 2 * r) by ring)))

/-- `φ^*` carries algebraic classes to algebraic classes (`γ(φ^!β) = φ^*γ(β)`). -/
theorem pullback_mem {X Y : (SmoothProjective k).FullSubcategory} (φ : Y ⟶ X) (r : ℤ)
    {x : (T.H X).piece (2 * r)} (hx : x ∈ algebraicClasses T X r) :
    T.pullback φ (2 * r) x ∈ algebraicClasses T Y r := by
  have hle : algebraicClasses T X r ≤
      (algebraicClasses T Y r).comap (T.pullback φ (2 * r)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨α, rfl⟩
    show T.pullback φ (2 * r) (T.cycleClass X r α) ∈ algebraicClasses T Y r
    rw [← T.cycleClass_gysin φ r α]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact hle hx

/-- `L` carries algebraic classes to algebraic classes (`γ(h · α) = γ(h) ∪ γ(α)`). -/
theorem lefschetzOp_mem (X : (SmoothProjective k).FullSubcategory) (h : Ch.group X 1) (r : ℤ)
    {x : (T.H X).piece (2 * r)} (hx : x ∈ algebraicClasses T X r) :
    lefschetzOp T X h r x ∈ algebraicClasses T X (r + 1) := by
  have hle : algebraicClasses T X r ≤
      (algebraicClasses T X (r + 1)).comap (lefschetzOp T X h r) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨α, rfl⟩
    show lefschetzOp T X h r (T.cycleClass X r α) ∈ algebraicClasses T X (r + 1)
    simp only [lefschetzOp, LinearMap.comp_apply]
    rw [← T.cycleClass_mul X 1 r h α]
    exact degreeCast_mem_algebraicClasses T X (by ring) _ (Submodule.subset_span ⟨_, rfl⟩)
  exact hle hx

/-- `φ_*` carries algebraic classes to algebraic classes (`γ(φ_*α) = φ_*γ(α)`). -/
theorem sectionPushforward_mem {X Y : (SmoothProjective k).FullSubcategory} (φ : Y ⟶ X)
    (hdim : T.dimension X = T.dimension Y + 1) (r : ℤ) {y : (T.H Y).piece (2 * r)}
    (hy : y ∈ algebraicClasses T Y r) :
    sectionPushforward T φ hdim r y ∈ algebraicClasses T X (r + 1) := by
  have hle : algebraicClasses T Y r ≤
      (algebraicClasses T X (r + 1)).comap (sectionPushforward T φ hdim r) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨α, rfl⟩
    show sectionPushforward T φ hdim r (T.cycleClass Y r α) ∈ algebraicClasses T X (r + 1)
    simp only [sectionPushforward, LinearMap.comp_apply]
    rw [T.cycleClass_pushforward φ r α, degreeCast_trans]
    exact degreeCast_mem_algebraicClasses T X (by omega) _ (Submodule.subset_span ⟨_, rfl⟩)
  exact hle hy

/-- `A⁰(X)`: the Lefschetz-type statement on algebraic classes in the critical dimension. For
`dim X = 2r + 1`, every algebraic class of `H^{2r+2}(X)` is `L` of an algebraic class of
`H^{2r}(X)`; for `dim X = 2r + 2`, every algebraic class of `H^{2r+4}(X)` is `L²` of an
algebraic class of `H^{2r}(X)`. -/
def AZero (X : (SmoothProjective k).FullSubcategory) (h : Ch.group X 1) : Prop :=
  (∀ r : ℤ, (T.dimension X : ℤ) = 2 * r + 1 →
      ∀ z ∈ algebraicClasses T X (r + 1), ∃ x ∈ algebraicClasses T X r,
        lefschetzOp T X h r x = z) ∧
    (∀ r : ℤ, (T.dimension X : ℤ) = 2 * r + 2 →
      ∀ z ∈ algebraicClasses T X (r + 1 + 1), ∃ x ∈ algebraicClasses T X r,
        lefschetzOp T X h (r + 1) (lefschetzOp T X h r x) = z)

/-- `A′(X)`: for `2r ≤ dim X − 1`, a class of `H^{2r}(X)` whose restriction to `Y` is algebraic
is algebraic. -/
def APrime {X Y : (SmoothProjective k).FullSubcategory} (φ : Y ⟶ X) : Prop :=
  ∀ r : ℤ, 2 * r ≤ (T.dimension X : ℤ) - 1 → ∀ x : (T.H X).piece (2 * r),
    T.pullback φ (2 * r) x ∈ algebraicClasses T Y r → x ∈ algebraicClasses T X r

/-- `A′⁰(X)`: `A′(X)` in the critical dimension, `2r = dim X − 1` or `2r = dim X − 2`. -/
def APrimeZero {X Y : (SmoothProjective k).FullSubcategory} (φ : Y ⟶ X) : Prop :=
  ∀ r : ℤ, ((T.dimension X : ℤ) = 2 * r + 1 ∨ (T.dimension X : ℤ) = 2 * r + 2) →
    ∀ x : (T.H X).piece (2 * r),
      T.pullback φ (2 * r) x ∈ algebraicClasses T Y r → x ∈ algebraicClasses T X r

/-- `A″(X)`: for `2r ≥ dim X − 1`, every algebraic class of `H^{2r+2}(X)` is `φ_*` of an
algebraic class of `H^{2r}(Y)`. -/
def ADoublePrime {X Y : (SmoothProjective k).FullSubcategory} (φ : Y ⟶ X)
    (hdim : T.dimension X = T.dimension Y + 1) : Prop :=
  ∀ r : ℤ, (T.dimension X : ℤ) - 1 ≤ 2 * r → ∀ z ∈ algebraicClasses T X (r + 1),
    ∃ y ∈ algebraicClasses T Y r, sectionPushforward T φ hdim r y = z

/-- `A″⁰(X)`: the condition of `A″(X)` in the critical dimension of the reading,
`2r = dim X − 1` or `2r = dim X − 2` (the latter one step below the range of `A″`). -/
def ADoublePrimeZero {X Y : (SmoothProjective k).FullSubcategory} (φ : Y ⟶ X)
    (hdim : T.dimension X = T.dimension Y + 1) : Prop :=
  ∀ r : ℤ, ((T.dimension X : ℤ) = 2 * r + 1 ∨ (T.dimension X : ℤ) = 2 * r + 2) →
    ∀ z ∈ algebraicClasses T X (r + 1),
      ∃ y ∈ algebraicClasses T Y r, sectionPushforward T φ hdim r y = z

variable {T}

theorem aPrimeZero_of_aPrime {X Y : (SmoothProjective k).FullSubcategory} {φ : Y ⟶ X}
    (hA' : APrime T φ) : APrimeZero T φ := fun r hr => hA' r (by omega)

theorem aDoublePrimeZero_odd_of_aDoublePrime {X Y : (SmoothProjective k).FullSubcategory}
    {φ : Y ⟶ X} {hdim : T.dimension X = T.dimension Y + 1} (hA'' : ADoublePrime T φ hdim)
    (r : ℤ) (hn : (T.dimension X : ℤ) = 2 * r + 1) :
    ∀ z ∈ algebraicClasses T X (r + 1),
      ∃ y ∈ algebraicClasses T Y r, sectionPushforward T φ hdim r y = z :=
  hA'' r (by omega)

/-- `n = 2r + 1`: under hard Lefschetz (`L` injective on `H^{2r}`), `L = φ_*φ^*` and the
splitting of `Z^r(Y)` along `Im φ^*` and `Ker φ_*`, `A⁰` in degree `r` is equivalent to the
conjunction of `A′⁰` and `A″⁰` in degree `r`. -/
theorem aZero_odd_iff {X Y : (SmoothProjective k).FullSubcategory} (φ : Y ⟶ X)
    (hdim : T.dimension X = T.dimension Y + 1) (h : Ch.group X 1) (r : ℤ)
    (hfac : ∀ x, lefschetzOp T X h r x = sectionPushforward T φ hdim r (T.pullback φ (2 * r) x))
    (hHL : Function.Injective (lefschetzOp T X h r))
    (hsplit : algebraicClasses T Y r ≤
      (algebraicClasses T Y r ⊓ LinearMap.range (T.pullback φ (2 * r))) ⊔
        (algebraicClasses T Y r ⊓ LinearMap.ker (sectionPushforward T φ hdim r))) :
    (∀ z ∈ algebraicClasses T X (r + 1), ∃ x ∈ algebraicClasses T X r,
        lefschetzOp T X h r x = z) ↔
      (∀ x, T.pullback φ (2 * r) x ∈ algebraicClasses T Y r → x ∈ algebraicClasses T X r) ∧
        (∀ z ∈ algebraicClasses T X (r + 1),
          ∃ y ∈ algebraicClasses T Y r, sectionPushforward T φ hdim r y = z) :=
  ⟨odd_converse hfac (fun _ hx => pullback_mem T φ r hx)
      (fun _ hy => sectionPushforward_mem T φ hdim r hy) hHL,
    fun hA => odd_step hfac hA.1 hA.2 hsplit⟩

/-- The « trivial » direction for `A′⁰`: `L = φ_*φ^*` and hard Lefschetz in the critical degree
(`L`, resp. `L²`, injective) give `A⁰(X) ⇒ A′⁰(X)`. -/
theorem aPrimeZero_of_aZero {X Y : (SmoothProjective k).FullSubcategory} (φ : Y ⟶ X)
    (hdim : T.dimension X = T.dimension Y + 1) (h : Ch.group X 1)
    (hfac : ∀ r x,
      lefschetzOp T X h r x = sectionPushforward T φ hdim r (T.pullback φ (2 * r) x))
    (hHL₁ : ∀ r : ℤ, (T.dimension X : ℤ) = 2 * r + 1 →
      Function.Injective (lefschetzOp T X h r))
    (hHL₂ : ∀ r : ℤ, (T.dimension X : ℤ) = 2 * r + 2 →
      Function.Injective fun x => lefschetzOp T X h (r + 1) (lefschetzOp T X h r x))
    (hA : AZero T X h) : APrimeZero T φ := by
  intro r hr
  rcases hr with hn | hn
  · exact (odd_converse (hfac r) (fun _ hx => pullback_mem T φ r hx)
      (fun _ hy => sectionPushforward_mem T φ hdim r hy) (hHL₁ r hn) (hA.1 r hn)).1
  · exact even_converse (hfac r) (fun _ hy => sectionPushforward_mem T φ hdim r hy)
      (fun _ hu => lefschetzOp_mem T X h (r + 1) hu) (hHL₂ r hn) (hA.2 r hn)

/-- The « trivial » direction for `A″⁰`, `n` odd: `L = φ_*φ^*` gives `A⁰(X) ⇒ A″⁰(X)`. -/
theorem aDoublePrimeZero_odd_of_aZero {X Y : (SmoothProjective k).FullSubcategory} (φ : Y ⟶ X)
    (hdim : T.dimension X = T.dimension Y + 1) (h : Ch.group X 1) (r : ℤ)
    (hn : (T.dimension X : ℤ) = 2 * r + 1)
    (hfac : ∀ x, lefschetzOp T X h r x = sectionPushforward T φ hdim r (T.pullback φ (2 * r) x))
    (hA : AZero T X h) :
    ∀ z ∈ algebraicClasses T X (r + 1),
      ∃ y ∈ algebraicClasses T Y r, sectionPushforward T φ hdim r y = z := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hA.1 r hn z hz
  exact ⟨T.pullback φ (2 * r) x, pullback_mem T φ r hx, (hfac x).symm⟩

/-- `n = 2r + 2`, the half that `A′⁰ + A″⁰` give: with weak Lefschetz (`φ^*` onto in degree
`2r`) and `L = φ_*φ^*`, every algebraic class of `H^{2r+2}(X)` is `L` of an algebraic class. -/
theorem lefschetz_surj_of_aPrimeZero_even {X Y : (SmoothProjective k).FullSubcategory}
    (φ : Y ⟶ X) (hdim : T.dimension X = T.dimension Y + 1) (h : Ch.group X 1) (r : ℤ)
    (hn : (T.dimension X : ℤ) = 2 * r + 2)
    (hfac : ∀ x, lefschetzOp T X h r x = sectionPushforward T φ hdim r (T.pullback φ (2 * r) x))
    (hWL : Function.Surjective (T.pullback φ (2 * r)))
    (hA' : APrimeZero T φ) (hA'' : ADoublePrimeZero T φ hdim) :
    ∀ z ∈ algebraicClasses T X (r + 1), ∃ x ∈ algebraicClasses T X r,
      lefschetzOp T X h r x = z :=
  even_first_half hfac hWL (hA' r (Or.inr hn)) (hA'' r (Or.inr hn))

/-- `n = 2r + 2`: `A′⁰(X)`, the case `2r + 2` of `A″(X)` and `A⁰(Y)` give `A⁰(X)`, through
`L² = L φ_* φ^* = φ_* L_Y φ^*`, with weak Lefschetz (`φ^*` onto in degree `2r`), `L = φ_*φ^*`
and the projection formula `L φ_* = φ_* L_Y` as hypotheses. -/
theorem aZero_even_of {X Y : (SmoothProjective k).FullSubcategory} (φ : Y ⟶ X)
    (hdim : T.dimension X = T.dimension Y + 1) (h : Ch.group X 1) (hY : Ch.group Y 1)
    (hfac : ∀ r x,
      lefschetzOp T X h r x = sectionPushforward T φ hdim r (T.pullback φ (2 * r) x))
    (hproj : ∀ r w, lefschetzOp T X h (r + 1) (sectionPushforward T φ hdim r w) =
      sectionPushforward T φ hdim (r + 1) (lefschetzOp T Y hY r w))
    (hWL : ∀ r : ℤ, (T.dimension X : ℤ) = 2 * r + 2 →
      Function.Surjective (T.pullback φ (2 * r)))
    (hA' : APrimeZero T φ) (hA'' : ADoublePrime T φ hdim) (hAY : AZero T Y hY) (r : ℤ)
    (hn : (T.dimension X : ℤ) = 2 * r + 2) :
    ∀ z ∈ algebraicClasses T X (r + 1 + 1), ∃ x ∈ algebraicClasses T X r,
      lefschetzOp T X h (r + 1) (lefschetzOp T X h r x) = z :=
  even_step (hfac r) (hproj r) (hWL r hn) (hA' r (Or.inr hn)) (hA'' (r + 1) (by omega))
    (hAY.1 r (by omega))

/-- `A′⁰(X) + A″(X) + A⁰(Y) ⇒ A⁰(X)`, with `L = φ_*φ^*`, the projection formula, weak Lefschetz
in the critical degree for `n` even, and for `n` odd the splitting of the algebraic classes of
the middle degree of `Y` along `Im φ^*` and `Ker φ_*`. -/
theorem aZero_of {X Y : (SmoothProjective k).FullSubcategory} (φ : Y ⟶ X)
    (hdim : T.dimension X = T.dimension Y + 1) (h : Ch.group X 1) (hY : Ch.group Y 1)
    (hfac : ∀ r x,
      lefschetzOp T X h r x = sectionPushforward T φ hdim r (T.pullback φ (2 * r) x))
    (hproj : ∀ r w, lefschetzOp T X h (r + 1) (sectionPushforward T φ hdim r w) =
      sectionPushforward T φ hdim (r + 1) (lefschetzOp T Y hY r w))
    (hWL : ∀ r : ℤ, (T.dimension X : ℤ) = 2 * r + 2 →
      Function.Surjective (T.pullback φ (2 * r)))
    (hsplit : ∀ r : ℤ, (T.dimension X : ℤ) = 2 * r + 1 → algebraicClasses T Y r ≤
      (algebraicClasses T Y r ⊓ LinearMap.range (T.pullback φ (2 * r))) ⊔
        (algebraicClasses T Y r ⊓ LinearMap.ker (sectionPushforward T φ hdim r)))
    (hA' : APrimeZero T φ) (hA'' : ADoublePrime T φ hdim) (hAY : AZero T Y hY) :
    AZero T X h :=
  ⟨fun r hn => odd_step (hfac r) (hA' r (Or.inl hn))
      (aDoublePrimeZero_odd_of_aDoublePrime hA'' r hn) (hsplit r hn),
    fun r hn => aZero_even_of φ hdim h hY hfac hproj hWL hA' hA'' hAY r hn⟩

end Weil

end Grothendieck.Folder16Problem5
