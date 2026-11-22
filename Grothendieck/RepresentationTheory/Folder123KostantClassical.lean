/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib
public import OpenProblems.AbelianVarieties
public import Grothendieck.RepresentationTheory.Folder123KostantOpposite
import Grothendieck.Attr

/-!
# Folder 123: Kostant's opposite Borels in the classical types `B`, `C`, `D`

The letter to Kostant of 22 October 1969 (folder 123, pp. 21–22) asks whether, for maximal tori
`T, T'` in apposition and Borel subgroups `B ⊇ T`, `B' ⊇ T'`, the Borels `B` and `B'` are always
in general position. `Grothendieck/RepresentationTheory/Folder123KostantOpposite.lean` answers yes
in type `A`. This file does the classical groups in their standard matrix models
(`OpenProblems.AbelianVarieties`: the form pairing `e_i` with `e_{N-1-i}`, the diagonal torus, the
upper triangular Borel, Kostant's cyclic element `E'`, the sum of the simple root vectors and of the
lowest root vector with nonzero coefficients). The finding: the answer is yes in types `B` and `C`;
in type `D` the steps below the middle of the flag (which determine the Borel) are transverse, and
the middle step holds for one of the two maximal isotropic subspaces only.

**What is proved.**
* `kostantOppositeTypeC` (`KostantOppositeTypeC n`, `Sp_{2n}`): every `E'`-stable complete flag of
  `ℂ^{2n}` is opposite to the standard flag, self-orthogonal or not.
* `kostantOppositeTypeB` (`KostantOppositeTypeB n`, `SO_{2n+1}`, `n ≥ 1`): the same for `ℂ^{2n+1}`
  (`oppositeB`: every `E'`-stable subspace of dimension `k` meets `F_{2n+1-k}` in `0`), although
  `E'` is not invertible.
* `kostantOppositeTypeD` (`KostantOppositeTypeD n`, `SO_{2n}`, `n ≥ 3`): an isotropic
  `E'`-stable subspace of dimension `k < n` meets `F_{2n-k}` in `0` (`oppositeD`).
* `cyclicElementC_mem_sp`, `cyclicElementB_mem_so`, `cyclicElementD_mem_so`: the three cyclic
  elements lie in `𝔰𝔭_{2n}`, `𝔰𝔬_{2n+1}`, `𝔰𝔬_{2n}` (`E'ᵀ J + J E' = 0`), for every `n`.

**How.** `path_shift` abstracts the type `A` argument: an operator `S` preserving `W` that moves
the coordinate `p j` to `p (j + 1)` (up to a nonzero factor) along a path `p` of coordinates; a
vector of `W` vanishing on the last `dim W` coordinates of the path vanishes on the whole path.
* Type `C`: in the basis `e₀, …, e_{2n-1}`, `E'` is literally a type `A_{2n-1}` cyclic element
  (`cyclicElementC = cyclicElement (2n) (coeffC n a)`), so type `A` applies.
* Type `B`: `ker E'` is the line of `u = a₀ e₀ + a_n e_{2n}` and `im E'` is the hyperplane `μ = 0`;
  the explicit map `GB` satisfies `G (E' x) = x - μ(x) u`, so it inverts `E'` on every `E'`-stable
  subspace of `{μ = 0}` and moves the coordinate `j` to `j + 1`. If `E'` is injective on `W`, then
  `W = E' W ⊆ {μ = 0}` is `G`-stable and the path `0, …, 2n` gives `v = 0`; otherwise
  `W' = E' W` has dimension `< k`, contains `w = G (E' v) = v - μ(v) u`, and the path
  `0, …, 2n - 1` gives `w = 0`, so `v = μ(v) u`, and `v_{2n} = 0` forces `μ(v) = 0`.
* Type `D`: `ker E'` is spanned by `u = a₀ e₀ + a_n e_{2n-1}` and `u' = a_{n-1} e_{n-1} -
  a_{n-2} e_n`, `im E'` is `{μ = μ' = 0}`, and `GD (E' x) = x - μ(x) u - μ'(x) u'`. The same two
  cases, along the paths `1, …, n-1, n+1, …, 2n-2, 0` (`p1`) and `0, …, n-1, n+1, …, 2n-2`
  (`p2`), which skip the coordinate `n` (on `im E'` it is a multiple of the coordinate `n - 1`),
  leave `v = μ'(v) u'`; there isotropy is needed: `⟨u', u'⟩ = -2 a_{n-1} a_{n-2} ≠ 0`.

**Not formalised.** That two Borels are in general position exactly when their flags are
opposite (Mathlib has no Borel subgroups or Bruhat decomposition), and that the Borels through
`T'` are the stabilisers of the `E'`-stable flags. In type `D`, the steps `k > n` (the orthogonal
duals of the steps `k < n`) and the middle step `k = n`, which does not hold for every
maximal isotropic `V_n ⊇ V_{n-1}`: a numerical computation (`n = 3, 4, 5`) finds, for each of the
`2^{n-1} n!` Borels, exactly one of the two `V_n` opposite to `F_n`. The exceptional types are out
of reach: the standard models are no longer matrices of a classical form.
-/

@[expose] public section

namespace Grothendieck.Folder123KostantClassical

open Matrix Module OpenProblems.AbelianVarieties

/-! ### Coordinates read on `ℕ` -/

/-- The coordinates of `x : Fin N → ℂ` read on `ℕ`, zero from `N` on. -/
def ext {N : ℕ} (x : Fin N → ℂ) (j : ℕ) : ℂ := ∑ i : Fin N, if (i : ℕ) = j then x i else 0

theorem ext_of_lt {N : ℕ} (x : Fin N → ℂ) {j : ℕ} (h : j < N) : ext x j = x ⟨j, h⟩ := by
  unfold ext
  rw [Finset.sum_eq_single ⟨j, h⟩]
  · simp
  · intro b _ hb
    exact ite_eq_right (fun h' => hb (Fin.ext h'))
  · simp

theorem ext_of_le {N : ℕ} (x : Fin N → ℂ) {j : ℕ} (h : N ≤ j) : ext x j = 0 := by
  unfold ext
  exact Finset.sum_eq_zero fun i _ => ite_eq_right (by omega)

theorem ext_eq_ext {N : ℕ} {x y : Fin N → ℂ} (h : ∀ j < N, ext x j = ext y j) : x = y := by
  funext i
  have := h i i.2
  rwa [ext_of_lt x i.2, ext_of_lt y i.2] at this

theorem ext_zero {N : ℕ} (j : ℕ) : ext (0 : Fin N → ℂ) j = 0 := by
  simp [ext]

/-! ### The shift argument along a path of coordinates -/

/-- The argument of type `A`, abstracted. Let `S` preserve `W`, `dim W ≤ k`, and move the
coordinate `p j` of a vector to the coordinate `p (j + 1)` up to a nonzero factor
(`j + 1 < M`). A vector of `W` whose coordinates `p j` vanish for `M - k ≤ j < M` has all its
coordinates `p j` (`j < M`) zero: otherwise, with `q` the last `j` where it does not vanish, its
images under `S⁰, …, Sᵏ` have their last nonzero coordinates at `p q, …, p (q + k)`, and are
`k + 1` independent vectors of `W`. -/
theorem path_shift {N M : ℕ} (p : ℕ → ℕ) (hp : ∀ j < M, p j < N)
    (S : (Fin N → ℂ) → (Fin N → ℂ))
    (hS : ∀ j, j + 1 < M → ∃ s : ℂ, s ≠ 0 ∧ ∀ x, ext (S x) (p (j + 1)) = s * ext x (p j))
    (W : Submodule ℂ (Fin N → ℂ)) (hW : ∀ w ∈ W, S w ∈ W) (k : ℕ) (hk : finrank ℂ W ≤ k)
    (v : Fin N → ℂ) (hv : v ∈ W) (h0 : ∀ j < M, M - k ≤ j → ext v (p j) = 0) :
    ∀ j < M, ext v (p j) = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨j₀, hj₀M, hj₀⟩ := hne
  obtain ⟨q, hq, hqmax⟩ := Finset.exists_max_image
    ((Finset.range M).filter fun j => ext v (p j) ≠ 0) id ⟨j₀, by simp [hj₀M, hj₀]⟩
  simp only [Finset.mem_filter, Finset.mem_range, id] at hq hqmax
  obtain ⟨hqM, hq⟩ := hq
  have hqk : q + k < M := by
    by_contra h
    exact hq (h0 q hqM (by omega))
  let w : ℕ → Fin N → ℂ := fun r => S^[r] v
  have hw_mem : ∀ r, w r ∈ W := by
    intro r
    induction r with
    | zero => simpa [w] using hv
    | succ r ih =>
      simp only [w, Function.iterate_succ_apply']
      exact hW _ ih
  have hw_shape : ∀ r, q + r < M →
      (∀ j, q + r < j → j < M → ext (w r) (p j) = 0) ∧ ext (w r) (p (q + r)) ≠ 0 := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨fun j hj hjM => ?_, by simpa [w] using hq⟩
      by_contra h
      have := hqmax j ⟨hjM, h⟩
      omega
    | succ r ih =>
      intro hr
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hstep : w (r + 1) = S (w r) := Function.iterate_succ_apply' _ _ _
      refine ⟨fun j hj hjM => ?_, ?_⟩
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        obtain ⟨s, _, hs⟩ := hS j' hjM
        rw [hstep, hs, ih1 j' (by omega) (by omega), mul_zero]
      · obtain ⟨s, hs0, hs⟩ := hS (q + r) (by omega)
        rw [hstep, show q + (r + 1) = (q + r) + 1 by omega, hs]
        exact mul_ne_zero hs0 ih2
  have hli : LinearIndependent ℂ (fun r : Fin (k + 1) => w r) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hgne
    push Not at hgne
    obtain ⟨r₁, hr₁⟩ := hgne
    obtain ⟨r₀, hr₀, hr₀max⟩ := Finset.exists_max_image (Finset.univ.filter fun r => g r ≠ 0)
      (fun r : Fin (k + 1) => (r : ℕ)) ⟨r₁, by simp [hr₁]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr₀ hr₀max
    have hr₀k := r₀.2
    have hlt : p (q + r₀) < N := hp _ (by omega)
    have h := congrFun hg ⟨p (q + r₀), hlt⟩
    rw [Finset.sum_apply, Finset.sum_eq_single r₀] at h
    · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      have h2 := (hw_shape r₀ (by omega)).2
      rw [ext_of_lt _ hlt] at h2
      exact mul_ne_zero hr₀ h2 h
    · intro r _ hr
      simp only [Pi.smul_apply, smul_eq_mul]
      by_cases hgr : g r = 0
      · simp [hgr]
      · have h1 := hr₀max r hgr
        have h2 : (r : ℕ) < r₀ := lt_of_le_of_ne h1 (fun h => hr (Fin.ext h))
        have h3 := (hw_shape r (by omega)).1 (q + r₀) (by omega) (by omega)
        rw [ext_of_lt _ hlt] at h3
        rw [h3, mul_zero]
    · simp
  have hspan : Submodule.span ℂ (Set.range fun r : Fin (k + 1) => w r) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact hw_mem r
  have h := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, Fintype.card_fin] at h
  omega

/-! ### Type `B` -/

theorem sum_ite_mul {N : ℕ} (x : Fin N → ℂ) (m : ℕ) (c : ℂ) :
    ∑ j : Fin N, (if (j : ℕ) = m then c else 0) * x j = c * ext x m := by
  rw [ext, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem ite_and_val {P : Prop} [Decidable P] {N : ℕ} (j : Fin N) (m : ℕ) (c : ℂ) :
    (if P ∧ (j : ℕ) = m then c else 0) = if (j : ℕ) = m then (if P then c else 0) else 0 := by
  split_ifs <;> tauto

section B
variable (n : ℕ) (a : Fin (n + 1) → ℂ)

/-- The superdiagonal of `cyclicElementB`. -/
def sB (i : ℕ) : ℂ := if i < n then kostantCoeff n a i else -kostantCoeff n a (2 * n - 1 - i)

theorem mulVecB (x : Fin (2 * n + 1) → ℂ) (i : ℕ) (hi : i < 2 * n + 1) :
    ext (cyclicElementB n a *ᵥ x) i = sB n a i * ext x (i + 1)
      + (if i + 2 = 2 * n + 1 then kostantCoeff n a n * ext x 0 else 0)
      - (if i = 2 * n then kostantCoeff n a n * ext x 1 else 0) := by
  rw [ext_of_lt _ hi]
  simp only [mulVec, dotProduct, cyclicElementB, ite_and_val, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_ite_mul]
  simp only [sB]
  split_ifs <;> simp

theorem kc_ne_zero {n : ℕ} {a : Fin (n + 1) → ℂ} (ha : ∀ i, a i ≠ 0) {m : ℕ} (hm : m < n + 1) :
    kostantCoeff n a m ≠ 0 := by
  simp only [kostantCoeff, dite_eq_left hm]
  exact ha _

theorem sB_ne_zero {n : ℕ} {a : Fin (n + 1) → ℂ} (ha : ∀ i, a i ≠ 0) {i : ℕ} (hi : i < 2 * n) :
    sB n a i ≠ 0 := by
  unfold sB
  split_ifs
  · exact kc_ne_zero ha (by omega)
  · exact neg_ne_zero.mpr (kc_ne_zero ha (by omega))

/-- The left inverse of `E'` on the hyperplane `μ = 0`, coordinatewise. -/
noncomputable def gB (y : ℕ → ℂ) (j : ℕ) : ℂ :=
  if j = 0 then y (2 * n - 1) / (2 * kostantCoeff n a n)
  else if j = 2 * n then -y (2 * n - 1) / (2 * kostantCoeff n a 0)
  else y (j - 1) / sB n a (j - 1)

/-- The left inverse of `E'` on the hyperplane `μ = 0`. -/
noncomputable def GB (y : Fin (2 * n + 1) → ℂ) : Fin (2 * n + 1) → ℂ := fun j => gB n a (ext y) j

/-- The linear form whose kernel is the image of `E'` (the orthogonal of its kernel). -/
noncomputable def muB (x : Fin (2 * n + 1) → ℂ) : ℂ :=
  ext x 0 / (2 * kostantCoeff n a 0) + ext x (2 * n) / (2 * kostantCoeff n a n)

/-- The kernel of `E'`: `a₀ e₀ + a_n e_{2n}`. -/
def uB : Fin (2 * n + 1) → ℂ :=
  fun j => if (j : ℕ) = 0 then kostantCoeff n a 0 else if (j : ℕ) = 2 * n then kostantCoeff n a n
    else 0

theorem ext_GB (y : Fin (2 * n + 1) → ℂ) {j : ℕ} (hj : j < 2 * n + 1) :
    ext (GB n a y) j = gB n a (ext y) j := by
  rw [ext_of_lt _ hj]; rfl

theorem ext_uB {j : ℕ} (hj : j < 2 * n + 1) :
    ext (uB n a) j = if j = 0 then kostantCoeff n a 0 else if j = 2 * n then kostantCoeff n a n
      else 0 := by
  rw [ext_of_lt _ hj]; rfl

variable {n a}

theorem GB_mulVec (hn : 1 ≤ n) (ha : ∀ i, a i ≠ 0) (x : Fin (2 * n + 1) → ℂ) {j : ℕ}
    (hj : j < 2 * n + 1) :
    ext (GB n a (cyclicElementB n a *ᵥ x)) j = ext x j - muB n a x * ext (uB n a) j := by
  have h0 := kc_ne_zero ha (m := 0) (by omega)
  have hb := kc_ne_zero ha (m := n) (by omega)
  rw [ext_GB _ _ _ hj, ext_uB _ _ hj, muB, gB]
  split_ifs with h1 h2
  · subst h1
    rw [mulVecB _ _ _ _ (by omega)]
    simp only [show 2 * n - 1 + 1 = 2 * n by omega, show 2 * n - 1 + 2 = 2 * n + 1 by omega,
      show 2 * n - 1 ≠ 2 * n by omega, ite_true, ite_false, sB,
      show ¬ 2 * n - 1 < n by omega, show 2 * n - 1 - (2 * n - 1) = 0 by omega]
    field_simp
    ring
  · subst h2
    rw [mulVecB _ _ _ _ (by omega)]
    simp only [show 2 * n - 1 + 1 = 2 * n by omega, show 2 * n - 1 + 2 = 2 * n + 1 by omega,
      show 2 * n - 1 ≠ 2 * n by omega, ite_true, ite_false, sB,
      show ¬ 2 * n - 1 < n by omega, show 2 * n - 1 - (2 * n - 1) = 0 by omega]
    field_simp
    ring
  · rw [mulVecB _ _ _ _ (by omega)]
    simp only [show j - 1 + 1 = j by omega, show j - 1 + 2 ≠ 2 * n + 1 by omega,
      show j - 1 ≠ 2 * n by omega, ite_false]
    field_simp [sB_ne_zero ha (show j - 1 < 2 * n by omega)]
    ring

theorem muB_mulVec (hn : 1 ≤ n) (ha : ∀ i, a i ≠ 0) (x : Fin (2 * n + 1) → ℂ) :
    muB n a (cyclicElementB n a *ᵥ x) = 0 := by
  have h0 := kc_ne_zero ha (m := 0) (by omega)
  have hb := kc_ne_zero ha (m := n) (by omega)
  rw [muB, mulVecB _ _ _ _ (by omega), mulVecB _ _ _ _ (by omega)]
  simp only [show 0 + 2 ≠ 2 * n + 1 by omega, show (0 : ℕ) ≠ 2 * n by omega,
    show 2 * n + 2 ≠ 2 * n + 1 by omega, ite_true, ite_false, sB, show 0 < n by omega,
    ext_of_le x (show 2 * n + 1 ≤ 2 * n + 1 from le_rfl)]
  field_simp
  ring

/-- `G` moves the coordinate `j` to `j + 1`, up to a nonzero factor. -/
noncomputable def σB (j : ℕ) : ℂ :=
  if j + 1 = 2 * n then -1 / (2 * kostantCoeff n a 0) else 1 / sB n a j

theorem GB_shift (x : Fin (2 * n + 1) → ℂ) (j : ℕ) (hj : j + 1 < 2 * n + 1) :
    ext (GB n a x) (j + 1) = σB (n := n) (a := a) j * ext x j := by
  rw [ext_GB _ _ _ hj, gB, σB]
  simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
  split_ifs with h
  · rw [show 2 * n - 1 = j by omega]; ring
  · ring

theorem σB_ne_zero (hn : 1 ≤ n) (ha : ∀ i, a i ≠ 0) (j : ℕ) (hj : j + 1 < 2 * n + 1) :
    σB (n := n) (a := a) j ≠ 0 := by
  unfold σB
  split_ifs
  · exact div_ne_zero (by norm_num) (mul_ne_zero two_ne_zero (kc_ne_zero ha (by omega)))
  · exact one_div_ne_zero (sB_ne_zero ha (by omega))

/-- An `E'`-stable subspace on which `μ` vanishes is `G`-stable: `E'` is injective on it, hence
bijective, and `G` inverts it there. -/
theorem GB_mem (hn : 1 ≤ n) (ha : ∀ i, a i ≠ 0) (U : Submodule ℂ (Fin (2 * n + 1) → ℂ))
    (hU : ∀ x ∈ U, cyclicElementB n a *ᵥ x ∈ U) (hH : ∀ x ∈ U, muB n a x = 0)
    {y : Fin (2 * n + 1) → ℂ} (hy : y ∈ U) : GB n a y ∈ U := by
  have hGf : ∀ z ∈ U, GB n a (cyclicElementB n a *ᵥ z) = z := fun z hz =>
    ext_eq_ext fun j hj => by rw [GB_mulVec hn ha z hj, hH z hz, zero_mul, sub_zero]
  let f : U →ₗ[ℂ] U := (Matrix.toLin' (cyclicElementB n a)).restrict
    (fun v hv => by simpa using hU v hv)
  have hinj : Function.Injective f := by
    intro p q hpq
    have h := congrArg (fun z : U => GB n a (z : Fin (2 * n + 1) → ℂ)) hpq
    simp only [f, LinearMap.coe_restrict_apply, Matrix.toLin'_apply] at h
    rw [hGf _ p.2, hGf _ q.2] at h
    exact Subtype.ext h
  obtain ⟨y', hy'⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨y, hy⟩
  have h : cyclicElementB n a *ᵥ (y' : Fin (2 * n + 1) → ℂ) = y := by
    simpa [f] using congrArg Subtype.val hy'
  rw [← h, hGf _ y'.2]
  exact y'.2

/-- A `k`-dimensional `E'`-stable subspace of `ℂ^{2n+1}` meets `F_{2n+1-k}` in `0`. -/
theorem oppositeB (hn : 1 ≤ n) (ha : ∀ i, a i ≠ 0) (W : Submodule ℂ (Fin (2 * n + 1) → ℂ))
    (k : ℕ) (hW : finrank ℂ W = k) (hE : ∀ v ∈ W, cyclicElementB n a *ᵥ v ∈ W)
    (v : Fin (2 * n + 1) → ℂ) (hv : v ∈ W)
    (h0 : ∀ j : Fin (2 * n + 1), 2 * n + 1 - k ≤ (j : ℕ) → v j = 0) : v = 0 := by
  have h0' : ∀ j, 2 * n + 1 - k ≤ j → ext v j = 0 := fun j hj => by
    by_cases hjN : j < 2 * n + 1
    · rw [ext_of_lt _ hjN]; exact h0 _ hj
    · exact ext_of_le _ (by omega)
  by_cases hkN : 2 * n + 1 ≤ k
  · exact ext_eq_ext fun j _ => by rw [h0' j (by omega), ext_zero]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have : W = ⊥ := Submodule.finrank_eq_zero.mp hW
    rw [this] at hv
    simpa using hv
  let f := (Matrix.toLin' (cyclicElementB n a)).domRestrict W
  have hW'mem : ∀ y ∈ LinearMap.range f, ∃ z ∈ W, cyclicElementB n a *ᵥ z = y := by
    intro y hy
    rw [LinearMap.range_domRestrict] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hz, by simp⟩
  have hEW' : ∀ z ∈ W, cyclicElementB n a *ᵥ z ∈ LinearMap.range f := fun z hz => by
    rw [LinearMap.range_domRestrict]
    exact ⟨z, hz, by simp⟩
  have hW'le : LinearMap.range f ≤ W := fun y hy => by
    obtain ⟨z, hz, rfl⟩ := hW'mem y hy
    exact hE z hz
  have hW'E : ∀ y ∈ LinearMap.range f, cyclicElementB n a *ᵥ y ∈ LinearMap.range f :=
    fun y hy => hEW' y (hW'le hy)
  have hW'H : ∀ y ∈ LinearMap.range f, muB n a y = 0 := fun y hy => by
    obtain ⟨z, _, rfl⟩ := hW'mem y hy
    exact muB_mulVec hn ha z
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  by_cases hker : LinearMap.ker f = ⊥
  · rw [hker, finrank_bot, add_zero] at hrank
    have hWW : LinearMap.range f = W := Submodule.eq_of_le_of_finrank_eq hW'le hrank
    have hG : ∀ y ∈ W, GB n a y ∈ W := fun y hy => by
      rw [← hWW] at hy ⊢
      exact GB_mem hn ha _ hW'E hW'H hy
    have := path_shift (N := 2 * n + 1) (M := 2 * n + 1) (fun j => j) (fun j hj => hj) (GB n a)
      (fun j hj => ⟨_, σB_ne_zero hn ha j hj, fun x => GB_shift x j hj⟩) W hG k hW.le v hv
      (fun j _ hjk => h0' j hjk)
    exact ext_eq_ext fun j hj => by rw [this j hj, ext_zero]
  · have hpos : 0 < finrank ℂ (LinearMap.ker f) := by
      by_contra h
      exact hker (Submodule.finrank_eq_zero.mp (by omega))
    have hw : GB n a (cyclicElementB n a *ᵥ v) ∈ LinearMap.range f :=
      GB_mem hn ha _ hW'E hW'H (hEW' v hv)
    have hwz := path_shift (N := 2 * n + 1) (M := 2 * n) (fun j => j) (fun j hj => by omega)
      (GB n a) (fun j hj => ⟨_, σB_ne_zero hn ha j (by omega), fun x => GB_shift x j (by omega)⟩)
      _ (fun y hy => GB_mem hn ha _ hW'E hW'H hy) (k - 1)
      (by omega) _ hw (fun j hj hjk => by
        rw [GB_mulVec hn ha v (by omega), ext_uB _ _ (by omega), h0' j (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega), mul_zero, sub_zero])
    have hlast : ext (GB n a (cyclicElementB n a *ᵥ v)) (2 * n) = 0 := by
      have h := hW'H _ hw
      rw [muB, hwz 0 (by omega), zero_div, zero_add] at h
      simpa [kc_ne_zero ha (m := n) (by omega)] using h
    have hμ : muB n a v = 0 := by
      have h := GB_mulVec hn ha v (j := 2 * n) (by omega)
      rw [hlast, h0' _ (by omega), ext_uB _ _ (by omega), ite_eq_right (by omega),
        ite_eq_left rfl] at h
      have hb := kc_ne_zero ha (m := n) (by omega)
      have : muB n a v * kostantCoeff n a n = 0 := by linear_combination h
      simpa [hb] using this
    refine ext_eq_ext fun j hj => ?_
    have h := GB_mulVec hn ha v hj
    rw [hμ, zero_mul, sub_zero] at h
    rw [← h, ext_zero]
    by_cases hj' : j < 2 * n
    · exact hwz j hj'
    · rw [show j = 2 * n by omega]; exact hlast

/-- **p:kostant in type `B_n`** (folder 123, pp. 21–22): for `G = SO_{2n+1}(ℂ)`, every
`E'`-stable complete flag of `ℂ^{2n+1}`, self-orthogonal or not, is opposite to the standard one. -/
@[montpellier "123, 21–22"]
theorem kostantOppositeTypeB (n : ℕ) : KostantOppositeTypeB n := by
  intro hn a ha V _ hdim hstab _ k v hv h0
  exact oppositeB hn ha (V k) k (hdim k) (hstab k) v hv h0

end B

/-! ### Type `C` -/

theorem coeffC_ne_zero (n : ℕ) (a : Fin (n + 1) → ℂ) (ha : ∀ i, a i ≠ 0) (i : Fin (2 * n)) :
    coeffC n a i ≠ 0 := by
  have hk : ∀ m, m < n + 1 → kostantCoeff n a m ≠ 0 := fun m hm => by
    simp only [kostantCoeff, dite_eq_left hm]
    exact ha _
  have := i.2
  unfold coeffC
  split_ifs with h1 h2
  · exact hk _ (by omega)
  · exact hk _ (by omega)
  · exact neg_ne_zero.mpr (hk _ (by omega))

/-- **p:kostant in type `C_n`** (folder 123, pp. 21–22): for `G = Sp_{2n}(ℂ)`, every Borel
through the centraliser of Kostant's cyclic element is opposite to the upper triangular one. -/
@[montpellier "123, 21–22"]
theorem kostantOppositeTypeC (n : ℕ) : KostantOppositeTypeC n := by
  intro a ha V hV hdim hstab _
  exact Folder123KostantOpposite.kostantOppositeTypeA (2 * n) (coeffC n a)
    (coeffC_ne_zero n a ha) V hV hdim hstab

/-! ### Type `D` -/

/-- Close a branch of a case split: contradictory, or a field identity. -/
local macro "kclose" : tactic =>
  `(tactic| first | omega | exact (‹False›).elim | ring1 | (field_simp; ring1))

section D
variable (n : ℕ) (a : Fin (n + 1) → ℂ)

/-- The superdiagonal of `cyclicElementD` (zero at `n - 1`). -/
def sD (i : ℕ) : ℂ :=
  if i + 1 < n then kostantCoeff n a i else if n ≤ i then -kostantCoeff n a (2 * n - 2 - i) else 0

theorem mulVecD (x : Fin (2 * n) → ℂ) (i : ℕ) (hi : i < 2 * n) :
    ext (cyclicElementD n a *ᵥ x) i = sD n a i * ext x (i + 1)
      + (if i + 2 = n then kostantCoeff n a (n - 1) * ext x n else 0)
      - (if i + 1 = n then kostantCoeff n a (n - 1) * ext x (n + 1) else 0)
      + (if i + 2 = 2 * n then kostantCoeff n a n * ext x 0 else 0)
      - (if i + 1 = 2 * n then kostantCoeff n a n * ext x 1 else 0) := by
  rw [ext_of_lt _ hi]
  simp only [mulVec, dotProduct, cyclicElementD, ite_and_val, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_ite_mul]
  simp only [sD]
  split_ifs <;> simp

/-- The left inverse of `E'` on `H = {μ = μ' = 0}`, coordinatewise. -/
noncomputable def gD (y : ℕ → ℂ) (j : ℕ) : ℂ :=
  if j = 0 then y (2 * n - 2) / (2 * kostantCoeff n a n)
  else if j = 2 * n - 1 then -y (2 * n - 2) / (2 * kostantCoeff n a 0)
  else if j = n - 1 then y (n - 2) / (2 * kostantCoeff n a (n - 2))
  else if j = n then y (n - 2) / (2 * kostantCoeff n a (n - 1))
  else if j = n + 1 then -y (n - 1) / kostantCoeff n a (n - 1)
  else y (j - 1) / sD n a (j - 1)

/-- The left inverse of `E'` on `H`. -/
noncomputable def GD (y : Fin (2 * n) → ℂ) : Fin (2 * n) → ℂ := fun j => gD n a (ext y) j

/-- The two linear forms whose common kernel `H` is the image of `E'`. -/
noncomputable def muD (x : Fin (2 * n) → ℂ) : ℂ :=
  ext x 0 / (2 * kostantCoeff n a 0) + ext x (2 * n - 1) / (2 * kostantCoeff n a n)

/-- See `muD`. -/
noncomputable def muD' (x : Fin (2 * n) → ℂ) : ℂ :=
  ext x (n - 1) / (2 * kostantCoeff n a (n - 1)) - ext x n / (2 * kostantCoeff n a (n - 2))

/-- The kernel of `E'` is spanned by `uD = a₀ e₀ + a_n e_{2n-1}` and
`uD' = a_{n-1} e_{n-1} - a_{n-2} e_n`. -/
def uD (j : ℕ) : ℂ :=
  if j = 0 then kostantCoeff n a 0 else if j = 2 * n - 1 then kostantCoeff n a n else 0

/-- See `uD`. -/
def uD' (j : ℕ) : ℂ :=
  if j = n - 1 then kostantCoeff n a (n - 1) else if j = n then -kostantCoeff n a (n - 2) else 0

theorem ext_GD (y : Fin (2 * n) → ℂ) {j : ℕ} (hj : j < 2 * n) :
    ext (GD n a y) j = gD n a (ext y) j := by
  rw [ext_of_lt _ hj]; rfl

variable {n a}

theorem sD_ne_zero (ha : ∀ i, a i ≠ 0) {i : ℕ} (hi : i + 2 < 2 * n) (hin : i + 1 ≠ n) :
    sD n a i ≠ 0 := by
  unfold sD
  split_ifs
  · exact kc_ne_zero ha (by omega)
  · exact neg_ne_zero.mpr (kc_ne_zero ha (by omega))
  · omega

theorem sD_of_lt {i : ℕ} (h : i + 1 < n) : sD n a i = kostantCoeff n a i := by
  simp [sD, h]

theorem sD_of_ge {i : ℕ} (h : n ≤ i) : sD n a i = -kostantCoeff n a (2 * n - 2 - i) := by
  rw [sD, ite_eq_right (by omega), ite_eq_left h]

theorem sD_pred (hn : 1 ≤ n) : sD n a (n - 1) = 0 := by
  rw [sD, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem GD_mulVec (hn : 3 ≤ n) (ha : ∀ i, a i ≠ 0) (x : Fin (2 * n) → ℂ) {j : ℕ}
    (hj : j < 2 * n) :
    ext (GD n a (cyclicElementD n a *ᵥ x)) j
      = ext x j - muD n a x * uD n a j - muD' n a x * uD' n a j := by
  have h0 := kc_ne_zero ha (m := 0) (by omega)
  have hb := kc_ne_zero ha (m := n) (by omega)
  have hc := kc_ne_zero ha (m := n - 2) (by omega)
  have ha' := kc_ne_zero ha (m := n - 1) (by omega)
  rw [ext_GD _ _ _ hj, gD]
  by_cases h1 : j = 0
  · subst j
    rw [ite_eq_left rfl, mulVecD _ _ _ _ (by omega), sD_of_ge (by omega),
      show 2 * n - 2 + 1 = 2 * n - 1 by omega,
      show 2 * n - 2 - (2 * n - 2) = 0 by omega]
    rw [muD, muD', uD, uD']
    split_ifs <;> kclose
  by_cases h2 : j = 2 * n - 1
  · subst j
    rw [ite_eq_right h1, ite_eq_left rfl, mulVecD _ _ _ _ (by omega), sD_of_ge (by omega),
      show 2 * n - 2 + 1 = 2 * n - 1 by omega,
      show 2 * n - 2 - (2 * n - 2) = 0 by omega]
    rw [muD, muD', uD, uD']
    split_ifs <;> kclose
  by_cases h3 : j = n - 1
  · subst j
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left rfl, mulVecD _ _ _ _ (by omega),
      sD_of_lt (by omega), show n - 2 + 1 = n - 1 by omega]
    rw [muD, muD', uD, uD']
    split_ifs <;> kclose
  by_cases h4 : j = n
  · subst j
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left rfl,
      mulVecD _ _ _ _ (by omega), sD_of_lt (by omega), show n - 2 + 1 = n - 1 by omega]
    rw [muD, muD', uD, uD']
    split_ifs <;> kclose
  by_cases h5 : j = n + 1
  · subst j
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_left rfl,
      mulVecD _ _ _ _ (by omega), sD_pred (by omega)]
    rw [muD, muD', uD, uD']
    split_ifs <;> kclose
  have hs := sD_ne_zero ha (n := n) (a := a) (i := j - 1) (by omega) (by omega)
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5,
    mulVecD _ _ _ _ (by omega), show j - 1 + 1 = j by omega]
  rw [muD, muD', uD, uD']
  split_ifs <;> kclose

theorem muD_mulVec (hn : 3 ≤ n) (ha : ∀ i, a i ≠ 0) (x : Fin (2 * n) → ℂ) :
    muD n a (cyclicElementD n a *ᵥ x) = 0 := by
  have h0 := kc_ne_zero ha (m := 0) (by omega)
  have hb := kc_ne_zero ha (m := n) (by omega)
  rw [muD, mulVecD _ _ _ 0 (by omega), mulVecD _ _ _ (2 * n - 1) (by omega), sD_of_lt (by omega),
    show 2 * n - 1 + 1 = 2 * n by omega, ext_of_le x (le_refl (2 * n))]
  split_ifs <;> kclose

theorem muD'_mulVec (hn : 3 ≤ n) (ha : ∀ i, a i ≠ 0) (x : Fin (2 * n) → ℂ) :
    muD' n a (cyclicElementD n a *ᵥ x) = 0 := by
  have hc := kc_ne_zero ha (m := n - 2) (by omega)
  have ha' := kc_ne_zero ha (m := n - 1) (by omega)
  rw [muD', mulVecD _ _ _ (n - 1) (by omega), mulVecD _ _ _ n (by omega), sD_pred (by omega),
    sD_of_ge (le_refl n), show 2 * n - 2 - n = n - 2 by omega]
  split_ifs <;> kclose

/-- An `E'`-stable subspace on which `μ` and `μ'` vanish is `G`-stable. -/
theorem GD_mem (hn : 3 ≤ n) (ha : ∀ i, a i ≠ 0) (U : Submodule ℂ (Fin (2 * n) → ℂ))
    (hU : ∀ x ∈ U, cyclicElementD n a *ᵥ x ∈ U)
    (hH : ∀ x ∈ U, muD n a x = 0 ∧ muD' n a x = 0)
    {y : Fin (2 * n) → ℂ} (hy : y ∈ U) : GD n a y ∈ U := by
  have hGf : ∀ z ∈ U, GD n a (cyclicElementD n a *ᵥ z) = z := fun z hz =>
    ext_eq_ext fun j hj => by
      rw [GD_mulVec hn ha z hj, (hH z hz).1, (hH z hz).2, zero_mul, zero_mul, sub_zero, sub_zero]
  let f : U →ₗ[ℂ] U := (Matrix.toLin' (cyclicElementD n a)).restrict
    (fun v hv => by simpa using hU v hv)
  have hinj : Function.Injective f := by
    intro p q hpq
    have h := congrArg (fun z : U => GD n a (z : Fin (2 * n) → ℂ)) hpq
    simp only [f, LinearMap.coe_restrict_apply, Matrix.toLin'_apply] at h
    rw [hGf _ p.2, hGf _ q.2] at h
    exact Subtype.ext h
  obtain ⟨y', hy'⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨y, hy⟩
  have h : cyclicElementD n a *ᵥ (y' : Fin (2 * n) → ℂ) = y := by
    simpa [f] using congrArg Subtype.val hy'
  rw [← h, hGf _ y'.2]
  exact y'.2

variable (n) in
/-- The path `1, …, n - 1, n + 1, …, 2n - 2, 0` through the coordinates of `H`. -/
def p1 (j : ℕ) : ℕ := if j + 1 < n then j + 1 else if j + 3 < 2 * n then j + 2 else 0

variable (n) in
/-- The path `0, …, n - 1, n + 1, …, 2n - 2` through the coordinates of `H`. -/
def p2 (j : ℕ) : ℕ := if j < n then j else j + 1

theorem GD_shift1 (hn : 3 ≤ n) (ha : ∀ i, a i ≠ 0) (j : ℕ) (hj : j + 1 < 2 * n - 2) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ x, ext (GD n a x) (p1 n (j + 1)) = s * ext x (p1 n j) := by
  have hb := kc_ne_zero ha (m := n) (by omega)
  have hc := kc_ne_zero ha (m := n - 2) (by omega)
  have ha' := kc_ne_zero ha (m := n - 1) (by omega)
  rcases (by omega : j + 3 < n ∨ j + 3 = n ∨ j + 2 = n ∨ (n ≤ j + 1 ∧ j + 4 < 2 * n) ∨
      j + 4 = 2 * n) with h | h | h | h | h
  · refine ⟨1 / sD n a (j + 1), one_div_ne_zero (sD_ne_zero ha (by omega) (by omega)),
      fun x => ?_⟩
    rw [show p1 n (j + 1) = j + 2 by unfold p1; split_ifs <;> omega,
      show p1 n j = j + 1 by unfold p1; split_ifs <;> omega, ext_GD _ _ _ (by omega), gD]
    split_ifs <;> first | kclose | (rw [show j + 2 - 1 = j + 1 by omega]; ring)
  · refine ⟨1 / (2 * kostantCoeff n a (n - 2)), one_div_ne_zero (mul_ne_zero two_ne_zero hc),
      fun x => ?_⟩
    rw [show p1 n (j + 1) = j + 2 by unfold p1; split_ifs <;> omega,
      show p1 n j = n - 2 by unfold p1; split_ifs <;> omega, ext_GD _ _ _ (by omega), gD]
    split_ifs <;> kclose
  · refine ⟨-1 / kostantCoeff n a (n - 1), div_ne_zero (by norm_num) ha', fun x => ?_⟩
    rw [show p1 n (j + 1) = n + 1 by unfold p1; split_ifs <;> omega,
      show p1 n j = n - 1 by unfold p1; split_ifs <;> omega, ext_GD _ _ _ (by omega), gD]
    split_ifs <;> kclose
  · refine ⟨1 / sD n a (j + 2), one_div_ne_zero (sD_ne_zero ha (by omega) (by omega)),
      fun x => ?_⟩
    rw [show p1 n (j + 1) = j + 3 by unfold p1; split_ifs <;> omega,
      show p1 n j = j + 2 by unfold p1; split_ifs <;> omega, ext_GD _ _ _ (by omega), gD]
    split_ifs <;> first | kclose | (rw [show j + 3 - 1 = j + 2 by omega]; ring)
  · refine ⟨1 / (2 * kostantCoeff n a n), one_div_ne_zero (mul_ne_zero two_ne_zero hb),
      fun x => ?_⟩
    rw [show p1 n (j + 1) = 0 by unfold p1; split_ifs <;> omega,
      show p1 n j = 2 * n - 2 by unfold p1; split_ifs <;> omega, ext_GD _ _ _ (by omega), gD]
    split_ifs <;> kclose

theorem GD_shift2 (hn : 3 ≤ n) (ha : ∀ i, a i ≠ 0) (j : ℕ) (hj : j + 1 < 2 * n - 2) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ x, ext (GD n a x) (p2 n (j + 1)) = s * ext x (p2 n j) := by
  have hc := kc_ne_zero ha (m := n - 2) (by omega)
  have ha' := kc_ne_zero ha (m := n - 1) (by omega)
  rcases (by omega : j + 2 < n ∨ j + 2 = n ∨ j + 1 = n ∨ n ≤ j) with h | h | h | h
  · refine ⟨1 / sD n a j, one_div_ne_zero (sD_ne_zero ha (by omega) (by omega)), fun x => ?_⟩
    rw [show p2 n (j + 1) = j + 1 by unfold p2; split_ifs <;> omega,
      show p2 n j = j by unfold p2; split_ifs <;> omega, ext_GD _ _ _ (by omega), gD]
    split_ifs <;> first | kclose | (rw [show j + 1 - 1 = j by omega]; ring)
  · refine ⟨1 / (2 * kostantCoeff n a (n - 2)), one_div_ne_zero (mul_ne_zero two_ne_zero hc),
      fun x => ?_⟩
    rw [show p2 n (j + 1) = j + 1 by unfold p2; split_ifs <;> omega,
      show p2 n j = n - 2 by unfold p2; split_ifs <;> omega, ext_GD _ _ _ (by omega), gD]
    split_ifs <;> kclose
  · refine ⟨-1 / kostantCoeff n a (n - 1), div_ne_zero (by norm_num) ha', fun x => ?_⟩
    rw [show p2 n (j + 1) = n + 1 by unfold p2; split_ifs <;> omega,
      show p2 n j = n - 1 by unfold p2; split_ifs <;> omega, ext_GD _ _ _ (by omega), gD]
    split_ifs <;> kclose
  · refine ⟨1 / sD n a (j + 1), one_div_ne_zero (sD_ne_zero ha (by omega) (by omega)),
      fun x => ?_⟩
    rw [show p2 n (j + 1) = j + 2 by unfold p2; split_ifs <;> omega,
      show p2 n j = j + 1 by unfold p2; split_ifs <;> omega, ext_GD _ _ _ (by omega), gD]
    split_ifs <;> first | kclose | (rw [show j + 2 - 1 = j + 1 by omega]; ring)

theorem uD'_pred : uD' n a (n - 1) = kostantCoeff n a (n - 1) := by
  simp [uD']

theorem uD'_self (hn : 3 ≤ n) : uD' n a n = -kostantCoeff n a (n - 2) := by
  rw [uD', ite_eq_right (by omega), ite_eq_left rfl]

theorem p1_lt (hn : 3 ≤ n) (j : ℕ) : p1 n j < 2 * n := by
  unfold p1; split_ifs <;> omega

theorem p2_lt (hn : 3 ≤ n) {j : ℕ} (hj : j < 2 * n - 2) : p2 n j < 2 * n := by
  unfold p2; split_ifs <;> omega

/-- A vector vanishing on both paths' coordinates (all but `n` and `2n - 1`), at `n` and at
`2n - 1` is zero. -/
theorem eq_zero_of_p2 (hn : 3 ≤ n) (y : Fin (2 * n) → ℂ) (hp : ∀ j < 2 * n - 2, ext y (p2 n j) = 0)
    (hn' : ext y n = 0) (hl : ext y (2 * n - 1) = 0) : y = 0 := by
  refine ext_eq_ext fun i hi => ?_
  rw [ext_zero]
  rcases (by omega : i < n ∨ i = n ∨ (n < i ∧ i + 1 < 2 * n) ∨ i + 1 = 2 * n) with h | h | h | h
  · have := hp i (by omega)
    rwa [show p2 n i = i by unfold p2; exact ite_eq_left h] at this
  · rw [h]; exact hn'
  · have := hp (i - 1) (by omega)
    rwa [show p2 n (i - 1) = i by unfold p2; split_ifs <;> omega] at this
  · rw [show i = 2 * n - 1 by omega]; exact hl

theorem antidiag_mulVec {N : ℕ} (y : Fin N → ℂ) (i : Fin N) :
    (antidiagForm N *ᵥ y) i = ext y (N - 1 - i) := by
  have hi := i.2
  have h : ∀ j : Fin N, (if (i : ℕ) + j + 1 = N then (1 : ℂ) else 0)
      = if (j : ℕ) = N - 1 - i then 1 else 0 := fun j => by
    split_ifs <;> first | rfl | omega
  simp only [mulVec, dotProduct, antidiagForm, h, sum_ite_mul, one_mul]

/-- A `k`-dimensional isotropic `E'`-stable subspace of `ℂ^{2n}`, `k < n`, meets `F_{2n-k}` in
`0`. -/
theorem oppositeD (hn : 3 ≤ n) (ha : ∀ i, a i ≠ 0) (W : Submodule ℂ (Fin (2 * n) → ℂ))
    (k : ℕ) (hkn : k < n) (hW : finrank ℂ W = k) (hE : ∀ v ∈ W, cyclicElementD n a *ᵥ v ∈ W)
    (hiso : ∀ x ∈ W, ∀ y ∈ W, x ⬝ᵥ (antidiagForm (2 * n) *ᵥ y) = 0)
    (v : Fin (2 * n) → ℂ) (hv : v ∈ W)
    (h0 : ∀ j : Fin (2 * n), 2 * n - k ≤ (j : ℕ) → v j = 0) : v = 0 := by
  have h0' : ∀ j, 2 * n - k ≤ j → ext v j = 0 := fun j hj => by
    by_cases hjN : j < 2 * n
    · rw [ext_of_lt _ hjN]; exact h0 _ hj
    · exact ext_of_le _ (by omega)
  have h0c := kc_ne_zero ha (m := 0) (by omega)
  have hb := kc_ne_zero ha (m := n) (by omega)
  have hc := kc_ne_zero ha (m := n - 2) (by omega)
  have ha' := kc_ne_zero ha (m := n - 1) (by omega)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have : W = ⊥ := Submodule.finrank_eq_zero.mp hW
    rw [this] at hv
    simpa using hv
  have hlastv : ext v (2 * n - 1) = 0 := h0' _ (by omega)
  let f := (Matrix.toLin' (cyclicElementD n a)).domRestrict W
  have hW'mem : ∀ y ∈ LinearMap.range f, ∃ z ∈ W, cyclicElementD n a *ᵥ z = y := by
    intro y hy
    rw [LinearMap.range_domRestrict] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hz, by simp⟩
  have hEW' : ∀ z ∈ W, cyclicElementD n a *ᵥ z ∈ LinearMap.range f := fun z hz => by
    rw [LinearMap.range_domRestrict]
    exact ⟨z, hz, by simp⟩
  have hW'le : LinearMap.range f ≤ W := fun y hy => by
    obtain ⟨z, hz, rfl⟩ := hW'mem y hy
    exact hE z hz
  have hW'E : ∀ y ∈ LinearMap.range f, cyclicElementD n a *ᵥ y ∈ LinearMap.range f :=
    fun y hy => hEW' y (hW'le hy)
  have hW'H : ∀ y ∈ LinearMap.range f, muD n a y = 0 ∧ muD' n a y = 0 := fun y hy => by
    obtain ⟨z, _, rfl⟩ := hW'mem y hy
    exact ⟨muD_mulVec hn ha z, muD'_mulVec hn ha z⟩
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  by_cases hker : LinearMap.ker f = ⊥
  · rw [hker, finrank_bot, add_zero] at hrank
    have hWW : LinearMap.range f = W := Submodule.eq_of_le_of_finrank_eq hW'le hrank
    have hG : ∀ y ∈ W, GD n a y ∈ W := fun y hy => by
      rw [← hWW] at hy ⊢
      exact GD_mem hn ha _ hW'E hW'H hy
    have hH : muD n a v = 0 ∧ muD' n a v = 0 := hW'H v (by rw [hWW]; exact hv)
    have hv0 : ext v 0 = 0 := by
      have h := hH.1
      rw [muD, hlastv, zero_div, add_zero, div_eq_zero_iff] at h
      exact h.resolve_right (mul_ne_zero two_ne_zero h0c)
    have hp := path_shift (N := 2 * n) (M := 2 * n - 2) (p1 n) (fun j _ => p1_lt hn j) (GD n a)
      (GD_shift1 hn ha) W hG k hW.le v hv (fun j hj hjk => by
        unfold p1
        split_ifs
        · omega
        · exact h0' _ (by omega)
        · exact hv0)
    have hp2 : ∀ j < 2 * n - 2, ext v (p2 n j) = 0 := by
      intro j hj
      rcases (by omega : j = 0 ∨ (1 ≤ j ∧ j < n) ∨ n ≤ j) with h | h | h
      · rw [h, show p2 n 0 = 0 by unfold p2; split_ifs <;> omega]; exact hv0
      · have := hp (j - 1) (by omega)
        rwa [show p1 n (j - 1) = p2 n j by unfold p1 p2; split_ifs <;> omega] at this
      · by_cases h' : j + 1 = 2 * n - 1
        · rw [show p2 n j = 2 * n - 1 by unfold p2; split_ifs <;> omega]; exact hlastv
        · have := hp (j - 1) (by omega)
          rwa [show p1 n (j - 1) = p2 n j by unfold p1 p2; split_ifs <;> omega] at this
    refine eq_zero_of_p2 hn v hp2 ?_ hlastv
    have h := hH.2
    have hn1 : ext v (n - 1) = 0 := by
      have := hp2 (n - 1) (by omega)
      rwa [show p2 n (n - 1) = n - 1 by unfold p2; split_ifs <;> omega] at this
    rw [muD', hn1, zero_div, zero_sub, neg_eq_zero, div_eq_zero_iff] at h
    exact h.resolve_right (mul_ne_zero two_ne_zero hc)
  · have hpos : 0 < finrank ℂ (LinearMap.ker f) := by
      by_contra h
      exact hker (Submodule.finrank_eq_zero.mp (by omega))
    have hw : GD n a (cyclicElementD n a *ᵥ v) ∈ LinearMap.range f :=
      GD_mem hn ha _ hW'E hW'H (hEW' v hv)
    have hp := path_shift (N := 2 * n) (M := 2 * n - 2) (p2 n) (fun j hj => p2_lt hn hj)
      (GD n a) (GD_shift2 hn ha) _ (fun y hy => GD_mem hn ha _ hW'E hW'H hy) (k - 1)
      (by omega) _ hw (fun j hj hjk => by
        rw [show p2 n j = j + 1 by unfold p2; split_ifs <;> omega,
          GD_mulVec hn ha v (by omega), h0' _ (by omega), uD, uD',
          ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
        ring)
    have hH := hW'H _ hw
    set w := GD n a (cyclicElementD n a *ᵥ v) with hw_def
    have hw0 : ext w 0 = 0 := by
      have := hp 0 (by omega)
      rwa [show p2 n 0 = 0 by unfold p2; split_ifs <;> omega] at this
    have hwn1 : ext w (n - 1) = 0 := by
      have := hp (n - 1) (by omega)
      rwa [show p2 n (n - 1) = n - 1 by unfold p2; split_ifs <;> omega] at this
    have hwl : ext w (2 * n - 1) = 0 := by
      have h := hH.1
      rw [muD, hw0, zero_div, zero_add, div_eq_zero_iff] at h
      exact h.resolve_right (mul_ne_zero two_ne_zero hb)
    have hwn : ext w n = 0 := by
      have h := hH.2
      rw [muD', hwn1, zero_div, zero_sub, neg_eq_zero, div_eq_zero_iff] at h
      exact h.resolve_right (mul_ne_zero two_ne_zero hc)
    have hw00 : w = 0 := eq_zero_of_p2 hn w hp hwn hwl
    -- `v = μ uD + μ' uD'`
    have hvK : ∀ i < 2 * n, ext v i = muD n a v * uD n a i + muD' n a v * uD' n a i := by
      intro i hi
      have h := GD_mulVec hn ha v hi
      rw [← hw_def, hw00, ext_zero] at h
      linear_combination -h
    have hμ : muD n a v = 0 := by
      have h := hvK (2 * n - 1) (by omega)
      rw [hlastv, uD, uD', ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega),
        ite_eq_right (by omega), mul_zero, add_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_right hb
    have hvK' : ∀ i < 2 * n, ext v i = muD' n a v * uD' n a i := fun i hi => by
      rw [hvK i hi, hμ, zero_mul, zero_add]
    -- isotropy: `⟨v, v⟩ = -2 μ'² a_{n-1} a_{n-2}`
    have hq := hiso v hv v hv
    have hsum : v ⬝ᵥ (antidiagForm (2 * n) *ᵥ v)
        = ∑ i ∈ Finset.range (2 * n), ext v i * ext v (2 * n - 1 - i) := by
      rw [dotProduct, ← Fin.sum_univ_eq_sum_range (fun i => ext v i * ext v (2 * n - 1 - i))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [antidiag_mulVec, ext_of_lt v i.2]
    rw [hsum, Finset.sum_eq_add (n - 1) n (by omega)] at hq
    · rw [hvK' _ (by omega), hvK' _ (by omega), hvK' _ (by omega), hvK' _ (by omega),
        show 2 * n - 1 - (n - 1) = n by omega, show 2 * n - 1 - n = n - 1 by omega,
        uD'_pred, uD'_self hn] at hq
      have h2 : muD' n a v ^ 2 * (kostantCoeff n a (n - 1) * kostantCoeff n a (n - 2)) = 0 := by
        linear_combination -hq / 2
      have hμ' : muD' n a v = 0 := by
        simpa [ha', hc] using h2
      exact ext_eq_ext fun i hi => by rw [hvK' i hi, hμ', zero_mul, ext_zero]
    · intro i hi hne
      rw [Finset.mem_range] at hi
      rw [hvK' i hi, uD', ite_eq_right hne.1, ite_eq_right hne.2, mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **p:kostant in type `D_n`** (folder 123, pp. 21–22), the steps `k < n`: for
`G = SO_{2n}(ℂ)`, `n ≥ 3`, an `E'`-stable isotropic flag is transverse to the standard flag
below the middle. -/
@[montpellier "123, 21–22"]
theorem kostantOppositeTypeD (n : ℕ) : KostantOppositeTypeD n := by
  intro hn a ha V _ hdim hstab hiso k v hv h0
  exact oppositeD hn ha (V k) k k.2 (hdim k) (hstab k) (hiso k) v hv h0

end D

/-! ### The cyclic elements lie in the Lie algebras -/

theorem mul_antidiag {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (Aᵀ * antidiagForm N) i j = A ⟨N - 1 - j, by omega⟩ i := by
  have hj := j.2
  simp only [mul_apply, transpose_apply, antidiagForm]
  rw [Finset.sum_eq_single ⟨N - 1 - j, by omega⟩]
  · simp [show N - 1 - (j : ℕ) + j + 1 = N by omega]
  · intro b _ hb
    rw [ite_eq_right (fun h => hb (Fin.ext (by simp; omega))), mul_zero]
  · simp

theorem antidiag_mul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (antidiagForm N * A) i j = A ⟨N - 1 - i, by omega⟩ j := by
  have hi := i.2
  simp only [mul_apply, antidiagForm]
  rw [Finset.sum_eq_single ⟨N - 1 - i, by omega⟩]
  · simp [show (i : ℕ) + (N - 1 - i) + 1 = N by omega]
  · intro b _ hb
    rw [ite_eq_right (fun h => hb (Fin.ext (by simp; omega))), zero_mul]
  · simp

theorem kc_congr {n : ℕ} (a : Fin (n + 1) → ℂ) {i j : ℕ} (h : i = j) :
    kostantCoeff n a i = kostantCoeff n a j := by rw [h]

/-- Normalise the signs in a branch of the entrywise skewness check. -/
local macro "skew_norm" : tactic => `(tactic|
  try simp only [add_zero, sub_zero, mul_one, one_mul, neg_one_mul, mul_neg_one, neg_neg])

/-- Close a branch of the entrywise skewness check. -/
local macro "skew_close" : tactic => `(tactic| first
  | omega
  | ring1
  | (skew_norm; rw [add_neg_eq_zero]; exact kc_congr _ (by omega))
  | (skew_norm; rw [neg_add_eq_zero]; exact kc_congr _ (by omega)))

theorem cyclicElementB_mem_so (n : ℕ) (a : Fin (n + 1) → ℂ) :
    (cyclicElementB n a)ᵀ * antidiagForm (2 * n + 1)
      + antidiagForm (2 * n + 1) * cyclicElementB n a = 0 := by
  ext i j
  rw [Matrix.add_apply, mul_antidiag, antidiag_mul, Matrix.zero_apply]
  have hi := i.2
  have hj := j.2
  simp only [cyclicElementB]
  split_ifs <;> skew_close


/-- The skewness condition is additive. -/
theorem skew_add {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ)
    (hA : Aᵀ * antidiagForm N + antidiagForm N * A = 0)
    (hB : Bᵀ * antidiagForm N + antidiagForm N * B = 0) :
    (A + B)ᵀ * antidiagForm N + antidiagForm N * (A + B) = 0 := by
  rw [transpose_add, Matrix.add_mul, Matrix.mul_add]
  calc _ = (Aᵀ * antidiagForm N + antidiagForm N * A)
        + (Bᵀ * antidiagForm N + antidiagForm N * B) := by abel
    _ = 0 := by rw [hA, hB, add_zero]

theorem cyclicElementD_mem_so (n : ℕ) (hn : 3 ≤ n) (a : Fin (n + 1) → ℂ) :
    (cyclicElementD n a)ᵀ * antidiagForm (2 * n)
      + antidiagForm (2 * n) * cyclicElementD n a = 0 := by
  let P : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ := fun i j =>
    if (j : ℕ) = i + 1 then
      (if (i : ℕ) + 1 < n then kostantCoeff n a i
        else if n ≤ (i : ℕ) then -kostantCoeff n a (2 * n - 2 - i) else 0) else 0
  let Q : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ := fun i j =>
    (if (i : ℕ) + 2 = n ∧ (j : ℕ) = n then kostantCoeff n a (n - 1) else 0)
    - (if (i : ℕ) + 1 = n ∧ (j : ℕ) = n + 1 then kostantCoeff n a (n - 1) else 0)
  let R : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ := fun i j =>
    (if (i : ℕ) + 2 = 2 * n ∧ (j : ℕ) = 0 then kostantCoeff n a n else 0)
    - (if (i : ℕ) + 1 = 2 * n ∧ (j : ℕ) = 1 then kostantCoeff n a n else 0)
  have hPQR : cyclicElementD n a = P + (Q + R) := by
    ext i j
    rw [Matrix.add_apply, Matrix.add_apply]
    simp only [cyclicElementD, P, Q, R]
    ring
  have hskew : ∀ M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ,
      (∀ i j : Fin (2 * n), M ⟨2 * n - 1 - j, by omega⟩ i + M ⟨2 * n - 1 - i, by omega⟩ j = 0) →
      Mᵀ * antidiagForm (2 * n) + antidiagForm (2 * n) * M = 0 := fun M hM => by
    ext i j
    rw [Matrix.add_apply, mul_antidiag, antidiag_mul, Matrix.zero_apply]
    exact hM i j
  rw [hPQR]
  refine skew_add _ _ (hskew _ fun i j => ?_) (skew_add _ _ (hskew _ fun i j => ?_)
    (hskew _ fun i j => ?_))
  all_goals
    have hi := i.2
    have hj := j.2
    simp only [P, Q, R]
    split_ifs <;> skew_close

theorem mul_symp {n : ℕ} (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (i j : Fin (2 * n)) :
    (Aᵀ * sympForm n) i j
      = A ⟨2 * n - 1 - j, by omega⟩ i * (if 2 * n - 1 - (j : ℕ) < n then 1 else -1) := by
  have hj := j.2
  simp only [mul_apply, transpose_apply, sympForm]
  rw [Finset.sum_eq_single ⟨2 * n - 1 - j, by omega⟩]
  · simp [show 2 * n - 1 - (j : ℕ) + j + 1 = 2 * n by omega]
  · intro b _ hb
    rw [ite_eq_right (fun h => hb (Fin.ext (by simp; omega))), mul_zero]
  · simp

theorem symp_mul {n : ℕ} (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (i j : Fin (2 * n)) :
    (sympForm n * A) i j = (if (i : ℕ) < n then 1 else -1) * A ⟨2 * n - 1 - i, by omega⟩ j := by
  have hi := i.2
  simp only [mul_apply, sympForm]
  rw [Finset.sum_eq_single ⟨2 * n - 1 - i, by omega⟩]
  · simp [show (i : ℕ) + (2 * n - 1 - i) + 1 = 2 * n by omega]
  · intro b _ hb
    rw [ite_eq_right (fun h => hb (Fin.ext (by simp; omega))), zero_mul]
  · simp

theorem cyclicElement_apply' {N : ℕ} (c : Fin N → ℂ) (i j : Fin N) :
    cyclicElement N c i j
      = if (j : ℕ) = i + 1 ∨ ((i : ℕ) + 1 = N ∧ (j : ℕ) = 0) then c i else 0 := by
  have hi := i.2
  have hj := j.2
  unfold cyclicElement
  congr 1
  apply propext
  rcases (by omega : (i : ℕ) + 1 < N ∨ (i : ℕ) + 1 = N) with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [h, Nat.mod_self]; omega

/-- Kostant's cyclic element of type `C_n` lies in `𝔰𝔭_{2n}`: `E'ᵀ J + J E' = 0`. -/
theorem cyclicElementC_mem_sp (n : ℕ) (a : Fin (n + 1) → ℂ) :
    (cyclicElementC n a)ᵀ * sympForm n + sympForm n * cyclicElementC n a = 0 := by
  ext i j
  rw [Matrix.add_apply, mul_symp, symp_mul, Matrix.zero_apply]
  have hi := i.2
  have hj := j.2
  simp only [cyclicElementC, cyclicElement_apply', coeffC]
  split_ifs <;> skew_close

end Grothendieck.Folder123KostantClassical
