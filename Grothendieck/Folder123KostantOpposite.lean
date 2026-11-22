module

public import Mathlib
public import OpenProblems.AbelianVarieties
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 123: Kostant's opposite Borels in type `A`

The letter to Kostant of 22 October 1969 (folder 123, pp. 21–22) asks whether, for maximal tori
`T, T'` in apposition and Borel subgroups `B ⊇ T`, `B' ⊇ T'`, the Borels `B` and `B'` are always in
general position. Problem p:kostant of the note on the open problems (`docs/problems/article.tex`)
states it for `PGL_n(ℂ)` as `OpenProblems.AbelianVarieties.KostantOppositeTypeA`; this file proves
that proposition for every `n` (`kostantOppositeTypeA`). The classical types `B`, `C`, `D` are in
`Grothendieck/Folder123KostantClassical.lean`; the exceptional types stay open.

The proof uses no eigenvectors. Let `E' = cyclicElement n c`, all `cᵢ ≠ 0`, and let `W` be an
`E'`-stable subspace of dimension `k`. The weighted shift `x ↦ (x_{j-1} / c_{j-1})_j` (indices mod
`n`, `shiftInv`) is a left inverse of `E'`, so `E'` is injective, hence bijective on `W`, and `W`
is stable under `shiftInv` (`shiftInv_mem`). If `v ∈ W` is nonzero and vanishes on the coordinates
of index `≥ n - k`, let `p < n - k` be the largest index with `v_p ≠ 0`. For `r ≤ k` the vector
`shiftInv^r v` vanishes above `p + r` and not at `p + r` (no index wraps around, since
`p + k < n`), so the `k + 1` vectors `v, shiftInv v, …, shiftInv^k v` of `W` are linearly
independent, which contradicts `dim W = k` (`opposite`).
-/

namespace Grothendieck.Folder123KostantOpposite

open Matrix Module OpenProblems.AbelianVarieties

variable {m : ℕ} (c : Fin (m + 1) → ℂ)

/-- `(E' x)ᵢ = cᵢ x_{i+1}`, indices mod `m + 1`. -/
theorem cyclicElement_mulVec_apply (x : Fin (m + 1) → ℂ) (i : Fin (m + 1)) :
    (cyclicElement (m + 1) c *ᵥ x) i = c i * x (i + 1) := by
  have key : ∀ j : Fin (m + 1), ((j : ℕ) = ((i : ℕ) + 1) % (m + 1)) ↔ j = i + 1 := by
    intro j
    rw [Fin.ext_iff, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  simp only [mulVec, dotProduct, cyclicElement, key, ite_mul, zero_mul]
  simp

/-- The inverse of `cyclicElement`: shift the coordinates up by one (mod `m + 1`), dividing by
the weights. -/
noncomputable def shiftInv (x : Fin (m + 1) → ℂ) : Fin (m + 1) → ℂ := fun j => x (j - 1) / c (j - 1)

theorem shiftInv_cyclicElement (hc : ∀ i, c i ≠ 0) (x : Fin (m + 1) → ℂ) :
    shiftInv c (cyclicElement (m + 1) c *ᵥ x) = x := by
  funext j
  simp only [shiftInv, cyclicElement_mulVec_apply, sub_add_cancel]
  exact mul_div_cancel_left₀ (x j) (hc _)

/-- An `E'`-stable subspace is `shiftInv`-stable: `E'` is injective, so bijective on it. -/
theorem shiftInv_mem (hc : ∀ i, c i ≠ 0) (W : Submodule ℂ (Fin (m + 1) → ℂ))
    (hE : ∀ v ∈ W, cyclicElement (m + 1) c *ᵥ v ∈ W) {w : Fin (m + 1) → ℂ} (hw : w ∈ W) :
    shiftInv c w ∈ W := by
  let f : W →ₗ[ℂ] W := (Matrix.toLin' (cyclicElement (m + 1) c)).restrict
    (fun v hv => by simpa using hE v hv)
  have hinj : Function.Injective f := by
    intro a b hab
    have h := congrArg (fun z : W => shiftInv c (z : Fin (m + 1) → ℂ)) hab
    simp only [f, LinearMap.coe_restrict_apply, Matrix.toLin'_apply,
      shiftInv_cyclicElement c hc] at h
    exact Subtype.ext h
  obtain ⟨w', hw'⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨w, hw⟩
  have h : cyclicElement (m + 1) c *ᵥ (w' : Fin (m + 1) → ℂ) = w := by
    simpa [f] using congrArg Subtype.val hw'
  rw [← h, shiftInv_cyclicElement c hc]
  exact w'.2

/-- A `k`-dimensional `E'`-stable subspace meets `F_{m+1-k}` (the vectors whose coordinates of
index `≥ m + 1 - k` vanish) in `0`. -/
theorem opposite (hc : ∀ i, c i ≠ 0) (W : Submodule ℂ (Fin (m + 1) → ℂ)) (k : ℕ)
    (hW : finrank ℂ W = k) (hE : ∀ v ∈ W, cyclicElement (m + 1) c *ᵥ v ∈ W)
    (v : Fin (m + 1) → ℂ) (hv : v ∈ W)
    (h0 : ∀ j : Fin (m + 1), m + 1 - k ≤ (j : ℕ) → v j = 0) : v = 0 := by
  by_contra hne
  obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨q, hq, hqmax⟩ := Finset.exists_max_image (Finset.univ.filter fun j => v j ≠ 0)
    (fun j : Fin (m + 1) => (j : ℕ)) ⟨j₀, by simp [hj₀]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hqmax
  have hpk : (q : ℕ) + k ≤ m := by
    by_contra h
    exact hq (h0 q (by omega))
  have hv_above : ∀ j : Fin (m + 1), (q : ℕ) < j → v j = 0 := by
    intro j hj
    by_contra h
    have := hqmax j h
    omega
  let w : ℕ → Fin (m + 1) → ℂ := fun r => (shiftInv c)^[r] v
  have hw_mem : ∀ r, w r ∈ W := by
    intro r
    induction r with
    | zero => simpa [w] using hv
    | succ r ih =>
      simp only [w, Function.iterate_succ_apply']
      exact shiftInv_mem c hc W hE ih
  have hw_shape : ∀ r, (q : ℕ) + r ≤ m →
      (∀ j : Fin (m + 1), (q : ℕ) + r < j → w r j = 0) ∧
      (∀ j : Fin (m + 1), (j : ℕ) = q + r → w r j ≠ 0) := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨fun j hj => hv_above j (by simpa using hj), fun j hj => ?_⟩
      have : j = q := Fin.ext (by simpa using hj)
      simpa [w, this] using hq
    | succ r ih =>
      intro hr
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hsub : ∀ j : Fin (m + 1), (q : ℕ) + r < j → ((j - 1 : Fin (m + 1)) : ℕ) = j - 1 := by
        intro j hj
        rw [Fin.coe_sub_one]
        split_ifs with h
        · subst h
          simp at hj
        · rfl
      have hstep : w (r + 1) = shiftInv c (w r) := Function.iterate_succ_apply' _ _ _
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · rw [hstep]
        change w r (j - 1) / c (j - 1) = 0
        rw [ih1 _ (by rw [hsub j (by omega)]; omega), zero_div]
      · rw [hstep]
        change w r (j - 1) / c (j - 1) ≠ 0
        exact div_ne_zero (ih2 _ (by rw [hsub j (by omega)]; omega)) (hc _)
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
    have h := congrFun hg ⟨q + r₀, by omega⟩
    rw [Finset.sum_apply, Finset.sum_eq_single r₀] at h
    · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      exact mul_ne_zero hr₀ ((hw_shape r₀ (by omega)).2 _ rfl) h
    · intro r _ hr
      simp only [Pi.smul_apply, smul_eq_mul]
      by_cases hgr : g r = 0
      · simp [hgr]
      · have h1 := hr₀max r hgr
        have h2 : (r : ℕ) < r₀ := lt_of_le_of_ne h1 (fun h => hr (Fin.ext h))
        have hrk := r.2
        rw [(hw_shape r (by omega)).1 _ (by simp only; omega), mul_zero]
    · simp
  have hspan : Submodule.span ℂ (Set.range fun r : Fin (k + 1) => w r) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact hw_mem r
  have h := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, hW, Fintype.card_fin] at h
  omega

/-- **p:kostant in type `A_{n-1}`** (folder 123, pp. 21–22): for `G = PGL_n(ℂ)`, the upper
triangular Borel and any Borel containing the centraliser of a cyclic element are opposite. -/
@[montpellier "123, 21–22"]
theorem kostantOppositeTypeA (n : ℕ) : KostantOppositeTypeA n := by
  intro c hc V _ hdim hstab k v hv h0
  cases n with
  | zero => funext j; exact j.elim0
  | succ m => exact opposite c hc (V k) k (hdim k) (hstab k) v hv h0

end Grothendieck.Folder123KostantOpposite
