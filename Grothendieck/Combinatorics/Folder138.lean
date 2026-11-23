/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib
import Grothendieck.Attr

/-!
# Folder 138, pages 113–119: the spherical maps with at most six darts

Pages 113–119 list by hand, up to homeomorphism of the sphere (reflections included), the
connected maps on the sphere with `n ≤ 6` darts in which a dart may end freely, class by class of
vertex degrees, each drawn with its full automorphism group and its type (degrees of the vertices,
edges and faces). The table has `1, 3, 3, 9, 13, 42` maps for `n = 1, …, 6` (the edition's
reading, `138.modern.tex` §14, and its finding `138-spherical-maps-census-6`, whose counts rest on
the transcription, batch 06). This file proves those six numbers, and the order of the full
automorphism group of every map.

A map is a pair of permutations `(σ, α)` of the darts `Fin n` with `α² = 1` (`DartMap`): the
cycles of `σ` are the vertices, those of `α` the edges, a fixed point of `α` being a dart that ends
freely, and those of `σα` the faces. It is spherical when `⟨σ, α⟩` is transitive and
`V + E + F = n + 2` (`DartMap.IsSpherical`). Two maps are the same up to homeomorphism when a
relabelling of the darts carries `(σ, α)` to `(σ', α')` or to `(σ'⁻¹, α')`, the mirror image
(`DartMap.Homeo`).

## Main results

* `card_census_one` … `card_census_six`, and `card_census`: the numbers of classes are
  `1, 3, 3, 9, 13, 42`, as on the page.
* `fullAutOrder_reps1` … `fullAutOrder_reps6`: the orders of the full automorphism groups of
  the maps, in the order of the page (by vertex degrees). For `n ≤ 5` they agree with the page's
  groups. For `n = 6` (pp. 118–119) the orders by class of vertex degrees are

  | class | maps | orders |
  |---|---|---|
  | a) `6` | 11 | `12, 6, 4, 4, 4, 4, 2, 2, 2, 2, 1` |
  | b) `5 1` | 7 | `2, 2, 2, 2, 2, 1, 1` |
  | c) `4 2` | 6 | `4, 2, 2, 2, 2, 1` |
  | d) `4 1 1` | 4 | `4, 4, 2, 2` |
  | e) `3 3` | 6 | `12, 4, 4, 4, 4, 2` |
  | f) `3 2 1` | 4 | `2, 2, 2, 1` |
  | g) `3 1 1 1` | 1 | `6` |
  | h) `2 2 2` | 2 | `12, 4` |
  | i) `2 2 1 1` | 1 | `4` |

  so the page's groups are off in four classes, by a factor `2` each time, as the finding says:
  a) the page has five `ℤ₂` and three groups of order `4`, there are four of each; b) four `ℤ₂` and
  three `1` on the page, five and two here; c) five `ℤ₂` and one `1`, here one group of order `4`,
  four `ℤ₂` and one `1`; d) three `ℤ₂` and one `ℤ₂ × ℤ₂`, here two and two. The counts of maps per
  class, `11, 7, 6, 4, 6, 4, 1, 2, 1` (and none for `2 1 1 1 1`, « impossible »), are the page's.

## Implementation notes

The proof is a computation checked by the kernel (`decide +kernel`, no `native_decide`), resting
on three facts proved in general:

* every involution is conjugate to `(0 1)(2 3) ⋯ (2j−2 2j−1)` for `2j` its number of moved
  darts (`exists_conj_of_mul_self`, through `Equiv.Perm.isConj_iff_cycleType_eq` and
  `Equiv.Perm.cycleType_of_pow_prime_eq_one`), so every map is isomorphic to one of the
  candidates `cands n`: all `n!` rotations, with one of these involutions (2880 candidates for
  `n = 6`);
* the numbers of cycles and connectedness are read on tables (`numCycles_eq`, through the least
  dart of each cycle; `connected_iff`, through the sets of darts stable under `σ` and `α`);
* in a connected map, a homeomorphism is determined by the image of one dart: every dart is
  reached from `0` by a word in `σ` and `α` (`words`, checked by `validB`), and a relabelling
  carrying the map onto another sends the end of a word from `0` to the end of the same word from
  the image of `0` (`isoSearch_of_iso`). So a homeomorphism between two maps exists iff one of
  the `2n` relabellings `transport` is one, and the automorphisms are counted by these.

Each candidate is then checked to be disconnected, or not spherical, or homeomorphic to one of
the listed maps (`coverB`), and the listed maps to be spherical and pairwise not homeomorphic. The
`2880` candidates of degree `6` are checked in twelve slices of `240` (`cover_six_0` …), each a
declaration of its own, so that the kernel's memory is freed between them; the whole file takes
about five minutes.

The groups are counted, not identified: `fullAutOrder` is the number of relabellings carrying the
map onto itself plus the number carrying it onto its mirror image, the order of the group of
homeomorphisms of the sphere preserving the map, up to isotopy. The listed maps were found by a
search outside Lean; the proof does not depend on how.

## Not formalised

The types of the maps (pp. 116–119) and the dual pairs that the page joins by braces; which drawn
map of degree `6` carries a faulty group.

## References

* A. Grothendieck, folder 138, pp. 113–119 (finding `138-spherical-maps-census-6`)
-/

@[expose] public section

namespace Grothendieck.Folder138

open Equiv Equiv.Perm Finset

variable {n : ℕ}

/-- A map on `n` darts in which a dart may end freely: `σ` turns the darts around their vertex,
`α` exchanges the two darts of an edge and fixes a dart that ends freely. -/
@[montpellier "138, 113–119"]
structure DartMap (n : ℕ) where
  /-- The rotation of the darts around their vertex; its cycles are the vertices. -/
  σ : Perm (Fin n)
  /-- The edges: an involution whose fixed points are the free darts. -/
  α : Perm (Fin n)
  /-- `α` is an involution. -/
  α_mul_self : α * α = 1

namespace DartMap

/-- The faces: the cycles of `σα`. -/
def φ (M : DartMap n) : Perm (Fin n) := M.σ * M.α

/-- The map is connected: the group generated by `σ` and `α` is transitive on the darts. -/
def Connected (M : DartMap n) : Prop :=
  MulAction.IsPretransitive (Subgroup.closure ({M.σ, M.α} : Set (Perm (Fin n)))) (Fin n)

/-- The number of cycles of a permutation, fixed points included. -/
noncomputable def numCycles (f : Perm (Fin n)) : ℕ := Nat.card (Quotient (SameCycle.setoid f))

/-- The map is connected and of genus `0`: `V + E + F = n + 2`, where `V`, `E`, `F` are the
numbers of cycles of `σ`, `α` and `σα` (Euler). -/
def IsSpherical (M : DartMap n) : Prop :=
  M.Connected ∧ numCycles M.σ + numCycles M.α + numCycles M.φ = n + 2

/-- The mirror image: the rotation reversed. -/
def mirror (M : DartMap n) : DartMap n := ⟨M.σ⁻¹, M.α, M.α_mul_self⟩

/-- An isomorphism: a relabelling of the darts carrying `σ` to `σ'` and `α` to `α'`, that is, an
orientation-preserving homeomorphism of the sphere carrying one map onto the other. -/
def Iso (M M' : DartMap n) : Prop :=
  ∃ τ : Perm (Fin n), τ * M.σ * τ⁻¹ = M'.σ ∧ τ * M.α * τ⁻¹ = M'.α

/-- A homeomorphism of the sphere, possibly reversing the orientation, carries `M` onto `M'`. -/
def Homeo (M M' : DartMap n) : Prop := M.Iso M' ∨ M.Iso M'.mirror

@[simp] theorem mirror_mirror (M : DartMap n) : M.mirror.mirror = M := by
  cases M; simp [mirror]

theorem Iso.refl (M : DartMap n) : M.Iso M := ⟨1, by simp, by simp⟩

theorem Iso.symm {M M' : DartMap n} (h : M.Iso M') : M'.Iso M := by
  obtain ⟨τ, h1, h2⟩ := h
  exact ⟨τ⁻¹, by rw [← h1]; group, by rw [← h2]; group⟩

theorem Iso.trans {M M' M'' : DartMap n} (h : M.Iso M') (h' : M'.Iso M'') : M.Iso M'' := by
  obtain ⟨τ, h1, h2⟩ := h
  obtain ⟨τ', h1', h2'⟩ := h'
  exact ⟨τ' * τ, by rw [← h1', ← h1]; group, by rw [← h2', ← h2]; group⟩

theorem Iso.mirror {M M' : DartMap n} (h : M.Iso M') : M.mirror.Iso M'.mirror := by
  obtain ⟨τ, h1, h2⟩ := h
  exact ⟨τ, by simp only [DartMap.mirror]; rw [← h1]; group, h2⟩

theorem homeo_equivalence : Equivalence (@Homeo n) where
  refl M := Or.inl (Iso.refl M)
  symm := by
    rintro M M' (h | h)
    · exact Or.inl h.symm
    · right; simpa using h.symm.mirror
  trans := by
    rintro M M' M'' (h | h) (h' | h')
    · exact Or.inl (h.trans h')
    · exact Or.inr (h.trans h')
    · exact Or.inr (h.trans h'.mirror)
    · left; simpa using h.trans h'.mirror

theorem Iso.homeo {M M' : DartMap n} (h : M.Iso M') : M.Homeo M' := Or.inl h

/-! ### Invariance -/

theorem numCycles_conj (τ f : Perm (Fin n)) : numCycles (τ * f * τ⁻¹) = numCycles f :=
  Nat.card_congr (Quotient.congr τ.symm fun _ _ => sameCycle_conj)

/-- A set of darts stable under `σ` and `α`. -/
def IsClosed (M : DartMap n) (S : Set (Fin n)) : Prop := ∀ x ∈ S, M.σ x ∈ S ∧ M.α x ∈ S

theorem inv_mem_of_mapsTo {f : Perm (Fin n)} {S : Set (Fin n)} (h : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, f⁻¹ x ∈ S := by
  intro x hx
  have hb : Set.BijOn f S S := (S.toFinite.injOn_iff_bijOn_of_mapsTo h).1 f.injective.injOn
  obtain ⟨y, hy, rfl⟩ := hb.surjOn hx
  simpa using hy

theorem IsClosed.mem_closure {M : DartMap n} {S : Set (Fin n)} (hS : M.IsClosed S)
    {g : Perm (Fin n)} (hg : g ∈ Subgroup.closure ({M.σ, M.α} : Set (Perm (Fin n)))) :
    ∀ x ∈ S, g x ∈ S := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    exacts [fun x hx => (hS x hx).1, fun x hx => (hS x hx).2]
  | one => simp
  | mul g h _ _ hg hh => intro x hx; simpa [Perm.mul_apply] using hg _ (hh x hx)
  | inv g _ hg => exact inv_mem_of_mapsTo hg

theorem connected_iff (M : DartMap n) :
    M.Connected ↔ ∀ S, M.IsClosed S → ∀ x ∈ S, ∀ y, y ∈ S := by
  constructor
  · intro h S hS x hx y
    obtain ⟨g, rfl⟩ := h.exists_smul_eq x y
    exact hS.mem_closure g.2 x hx
  · intro h
    refine ⟨fun x y => h {z | ∃ g : Subgroup.closure ({M.σ, M.α} : Set (Perm (Fin n))), g • x = z}
      (fun z ⟨g, hg⟩ => ⟨⟨⟨M.σ, Subgroup.subset_closure (by simp)⟩ * g, by rw [mul_smul, hg]; rfl⟩,
        ⟨⟨M.α, Subgroup.subset_closure (by simp)⟩ * g, by rw [mul_smul, hg]; rfl⟩⟩) x
      ⟨1, one_smul _ _⟩ y⟩

theorem Iso.connected {M M' : DartMap n} (h : M.Iso M') (hM : M.Connected) : M'.Connected := by
  obtain ⟨τ, h1, h2⟩ := h
  rw [connected_iff] at hM ⊢
  intro S hS x hx y
  have hT : M.IsClosed {z | τ z ∈ S} := fun z hz =>
    ⟨by simpa [← h1] using (hS _ hz).1, by simpa [← h2] using (hS _ hz).2⟩
  simpa using hM _ hT (τ⁻¹ x) (by simpa using hx) (τ⁻¹ y)

theorem Iso.isSpherical {M M' : DartMap n} (h : M.Iso M') (hM : M.IsSpherical) :
    M'.IsSpherical := by
  refine ⟨h.connected hM.1, ?_⟩
  obtain ⟨τ, h1, h2⟩ := h
  have h3 : M'.φ = τ * M.φ * τ⁻¹ := by simp only [φ, ← h1, ← h2]; group
  rw [h3, ← h1, ← h2, numCycles_conj, numCycles_conj, numCycles_conj]
  exact hM.2

end DartMap

/-! ### Involutions -/

theorem cycleType_of_mul_self {f : Perm (Fin n)} (hf : f * f = 1) :
    f.cycleType = Multiset.replicate (#f.support / 2) 2 ∧ #f.support = 2 * (#f.support / 2) := by
  have hrep := cycleType_of_pow_prime_eq_one (p := 2) (by rw [sq]; exact hf)
  have hs := sum_cycleType f
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hs
  exact ⟨by rw [hrep, ← hs]; congr 1; omega, by omega⟩

theorem exists_conj_of_mul_self {f g : Perm (Fin n)} (hf : f * f = 1) (hg : g * g = 1)
    (h : #f.support = #g.support) : ∃ τ : Perm (Fin n), τ * f * τ⁻¹ = g :=
  isConj_iff.1 (isConj_iff_cycleType_eq.2 (by
    rw [(cycleType_of_mul_self hf).1, (cycleType_of_mul_self hg).1, h]))

/-! ### Computation -/

/-- The function `Fin n → Fin n` that the list `l` tabulates. -/
def app (l : List (Fin n)) (x : Fin n) : Fin n := l.getD x x

/-- The table of a function `Fin n → Fin n`. -/
def tab (f : Fin n → Fin n) : List (Fin n) := (List.finRange n).map f

/-- A word in `s` (`true`) and `a` (`false`) applied to a dart; the head of the list acts last. -/
def evalW (s a : Fin n → Fin n) : List Bool → Fin n → Fin n
  | [], x => x
  | true :: w, x => s (evalW s a w x)
  | false :: w, x => a (evalW s a w x)

/-- The entry of a dart in a table of words. -/
def look (W : List (Option (List Bool))) (y : Fin n) : Option (List Bool) := W.getD y none

/-- One step of a breadth-first search: a dart without a word gets one from a dart that has one. -/
def bfsStep (s a : Fin n → Fin n) (W : List (Option (List Bool))) : List (Option (List Bool)) :=
  (List.finRange n).map fun y =>
    match look W y with
    | some w => some w
    | none => (List.finRange n).findSome? fun x =>
        match look W x with
        | some w =>
          if s x = y then some (true :: w) else if a x = y then some (false :: w) else none
        | none => none

/-- Words reaching the darts from the dart `0`, after `n` steps of `bfsStep`. -/
def words [NeZero n] (s a : Fin n → Fin n) : List (Option (List Bool)) :=
  (bfsStep s a)^[n] ((List.finRange n).map fun y => if y = 0 then some [] else none)

/-- Every dart has a word, and that word carries `0` to it. -/
def validB [NeZero n] (s a : Fin n → Fin n) (W : List (Option (List Bool))) : Bool :=
  (List.finRange n).all fun y => match look W y with
    | some w => evalW s a w 0 = y
    | none => false

/-- The darts that have a word form a set stable under `s` and `a`. -/
def closedB (s a : Fin n → Fin n) (W : List (Option (List Bool))) : Bool :=
  (List.finRange n).all fun y =>
    !(look W y).isSome || ((look W (s y)).isSome && (look W (a y)).isSome)

/-- Every dart has a word. -/
def allSomeB (W : List (Option (List Bool))) : Bool :=
  (List.finRange n).all fun y => (look W y).isSome

/-- `x` is the least dart of its cycle under `f`. -/
def isMinB (f : Fin n → Fin n) (x : Fin n) : Bool := (List.range (n + 2)).all fun k => x ≤ f^[k] x

/-- The number of cycles of `f`, counted by their least darts. -/
def numCyclesL (f : Fin n → Fin n) : ℕ := (List.finRange n).countP (isMinB f)

/-- Euler's relation `V + E + F = n + 2`, computed. -/
def eulerB (s a : Fin n → Fin n) : Bool :=
  numCyclesL s + numCyclesL a + numCyclesL (fun x => s (a x)) = n + 2

/-- The relabelling sending `0` to `d` and the end of each dart's word to the end of the same word
from `d`. -/
def transport (W : List (Option (List Bool))) (s' a' : Fin n → Fin n) (d : Fin n) : List (Fin n) :=
  (List.finRange n).map fun y => match look W y with
    | some w => evalW s' a' w d
    | none => d

/-- `t` is injective and carries `s`, `a` to `s'`, `a'`. -/
def isoB (s a s' a' : Fin n → Fin n) (t : List (Fin n)) : Bool :=
  (List.finRange n).all fun x =>
    ((List.finRange n).all fun y => app t x != app t y || x == y) &&
    app t (s x) == s' (app t x) && app t (a x) == a' (app t x)

/-- Some relabelling `transport W s' a' d` is an isomorphism. -/
def isoSearch (W : List (Option (List Bool))) (s a s' a' : Fin n → Fin n) : Bool :=
  (List.finRange n).any fun d => isoB s a s' a' (transport W s' a' d)

/-- A map given by tables: `σ`, its inverse, `α`. -/
structure Rep (n : ℕ) where
  /-- The table of `σ`. -/
  σ : List (Fin n)
  /-- The table of `σ⁻¹`. -/
  σinv : List (Fin n)
  /-- The table of `α`. -/
  α : List (Fin n)

/-- The map is isomorphic to `r` or to its mirror image, computed. -/
def homeoB (W : List (Option (List Bool))) (s a : Fin n → Fin n) (r : Rep n) : Bool :=
  isoSearch W s a (app r.σ) (app r.α) || isoSearch W s a (app r.σinv) (app r.α)

/-- The involution `(0 1)(2 3) ⋯ (2j−2 2j−1)`. -/
def iotaL (n j : ℕ) [NeZero n] : List (Fin n) :=
  (List.finRange n).map fun x =>
    if x.val < 2 * j then Fin.ofNat n (if x.val % 2 = 0 then x.val + 1 else x.val - 1) else x

/-- The length of the cycle of `x`. -/
def cycLen (f : Fin n → Fin n) (x : Fin n) : ℕ :=
  ((List.range n).find? fun k => f^[k + 1] x = x).getD n

/-- The cycle types of `s`, `a`, `sa`, as counts of darts by cycle length (a quick filter). -/
def sig (s a : Fin n → Fin n) : List ℕ × List ℕ × List ℕ :=
  let d := fun f : Fin n → Fin n => (List.range (n + 1)).map fun m =>
    (List.finRange n).countP fun x => cycLen f x = m
  (d s, d a, d fun x => s (a x))

/-- The map `(l, (0 1) ⋯ (2j−2 2j−1))` is disconnected, or not spherical, or isomorphic to an
entry of `reps` or to its mirror image. -/
def coverB [NeZero n] (reps : List (Rep n)) (l : List (Fin n)) (j : ℕ) : Bool :=
  let s := app l
  let a := app (iotaL n j)
  let W := words s a
  (closedB s a W && (look W (0 : Fin n)).isSome && !allSomeB (n := n) W) || !eulerB s a ||
    reps.any fun r => sig s a == sig (app r.σ) (app r.α) && homeoB W s a r


/-! ### Bridges -/

theorem app_tab (f : Fin n → Fin n) : app (tab f) = f := by
  funext x
  simp [app, tab, List.getD_eq_getElem?_getD]

theorem countP_finRange (p : Fin n → Bool) :
    (List.finRange n).countP p = #(univ.filter fun x => p x = true) := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
    ((List.nodup_finRange n).filter _)]
  congr 1
  ext x
  simp

theorem isMinB_iff (f : Perm (Fin n)) (x : Fin n) :
    isMinB f x = true ↔ ∀ y, SameCycle f x y → x ≤ y := by
  simp only [isMinB, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h y hy
    obtain ⟨i, -, hi, rfl⟩ := hy.exists_pow_eq f
    have : #(f.cycleOf x).support ≤ n := (card_le_univ _).trans (by simp)
    rw [coe_pow]
    exact h i (by omega)
  · intro h k _
    apply h
    have := (sameCycle_pow_right (f := f) (n := k)).2 (SameCycle.refl f x)
    rwa [coe_pow] at this

theorem numCycles_eq (f : Perm (Fin n)) : DartMap.numCycles f = numCyclesL f := by
  classical
  rw [numCyclesL, countP_finRange, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    DartMap.numCycles]
  symm
  refine Nat.card_eq_of_bijective (fun x => (⟦x.1⟧ : Quotient (SameCycle.setoid f))) ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    have h' : SameCycle f x y := Quotient.exact h
    rw [isMinB_iff] at hx hy
    exact Subtype.ext (le_antisymm (hx y h') (hy x h'.symm))
  · intro q
    induction q using Quotient.inductionOn with
    | h y =>
      have hne : (univ.filter fun z => SameCycle f y z).Nonempty := ⟨y, by simp [SameCycle.refl]⟩
      set m := (univ.filter fun z => SameCycle f y z).min' hne
      have hm : SameCycle f y m := by
        simpa using (univ.filter fun z => SameCycle f y z).min'_mem hne
      refine ⟨⟨m, (isMinB_iff f m).2 fun z hz => ?_⟩, Quotient.sound hm.symm⟩
      exact (univ.filter fun z => SameCycle f y z).min'_le z (by simpa using hm.trans hz)

theorem card_support_eq (f : Perm (Fin n)) :
    #f.support = (List.finRange n).countP fun x => f x != x := by
  rw [countP_finRange]; congr 1

/-! ### Words -/

/-- The permutation a word stands for. -/
def wordPerm (σ α : Perm (Fin n)) : List Bool → Perm (Fin n)
  | [] => 1
  | true :: w => σ * wordPerm σ α w
  | false :: w => α * wordPerm σ α w

theorem coe_wordPerm (σ α : Perm (Fin n)) (w : List Bool) :
    ⇑(wordPerm σ α w) = evalW σ α w := by
  induction w with
  | nil => funext x; rfl
  | cons b w ih => cases b <;> funext x <;> simp [wordPerm, evalW, ih]

theorem wordPerm_mem (σ α : Perm (Fin n)) (w : List Bool) :
    wordPerm σ α w ∈ Subgroup.closure ({σ, α} : Set (Perm (Fin n))) := by
  induction w with
  | nil => exact one_mem _
  | cons b w ih => cases b <;> exact mul_mem (Subgroup.subset_closure (by simp)) ih

theorem evalW_conj {τ : Fin n → Fin n} {s a s' a' : Fin n → Fin n}
    (hs : ∀ x, τ (s x) = s' (τ x)) (ha : ∀ x, τ (a x) = a' (τ x)) (w : List Bool) (x : Fin n) :
    τ (evalW s a w x) = evalW s' a' w (τ x) := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [evalW, hs, ha, ih]

theorem validB_spec [NeZero n] {s a : Fin n → Fin n} {W : List (Option (List Bool))}
    (h : validB s a W = true) (y : Fin n) : ∃ w, look W y = some w ∧ evalW s a w 0 = y := by
  have := List.all_eq_true.1 h y (List.mem_finRange y)
  revert this
  rcases hy : look W y with _ | w
  · simp
  · intro h'; exact ⟨w, rfl, by simpa using h'⟩

namespace DartMap

theorem connected_of_validB [NeZero n] (M : DartMap n) {W : List (Option (List Bool))}
    (h : validB M.σ M.α W = true) : M.Connected := by
  rw [connected_iff]
  intro S hS x hx y
  obtain ⟨wx, -, hwx⟩ := validB_spec h x
  obtain ⟨wy, -, hwy⟩ := validB_spec h y
  have h0 : (0 : Fin n) ∈ S := by
    have := hS.mem_closure (inv_mem (wordPerm_mem M.σ M.α wx)) x hx
    rwa [Perm.inv_eq_iff_eq.2 (by rw [coe_wordPerm, hwx])] at this
  have := hS.mem_closure (wordPerm_mem M.σ M.α wy) 0 h0
  rwa [coe_wordPerm, hwy] at this

theorem not_connected_of_closedB [NeZero n] (M : DartMap n) {W : List (Option (List Bool))}
    (hc : closedB M.σ M.α W = true) (h0 : (look W (0 : Fin n)).isSome = true)
    (hall : allSomeB (n := n) W = false) : ¬ M.Connected := by
  rw [connected_iff]
  intro h
  have hS : M.IsClosed {y | (look W y).isSome = true} := fun y hy => by
    have := List.all_eq_true.1 hc y (List.mem_finRange y)
    simp only [Set.mem_ofPred_eq] at hy
    simpa [hy] using this
  obtain ⟨y, hy⟩ : ∃ y, look W y = none := by simpa [allSomeB] using hall
  have := h _ hS 0 h0 y
  simp [hy] at this

end DartMap

/-! ### Isomorphisms from the tables -/

theorem isoB_spec {s a s' a' : Fin n → Fin n} {t : List (Fin n)} :
    isoB s a s' a' t = true ↔ (∀ x y, app t x = app t y → x = y) ∧
      (∀ x, app t (s x) = s' (app t x)) ∧ ∀ x, app t (a x) = a' (app t x) := by
  simp only [isoB, List.all_eq_true, List.mem_finRange, forall_true_left, Bool.and_eq_true,
    Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  constructor
  · intro h
    exact ⟨fun x y hxy => ((h x).1.1 y).resolve_left (not_not.2 hxy), fun x => (h x).1.2,
      fun x => (h x).2⟩
  · rintro ⟨h1, h2, h3⟩ x
    exact ⟨⟨fun y => (em (app t x = app t y)).elim (fun e => Or.inr (h1 x y e)) Or.inl, h2 x⟩,
      h3 x⟩

theorem conj_apply {τ σ σ' : Perm (Fin n)} (h : τ * σ * τ⁻¹ = σ') (x : Fin n) :
    τ (σ x) = σ' (τ x) := by
  rw [← h]; simp

theorem perm_of_isoB {σ α σ' α' : Perm (Fin n)} {t : List (Fin n)}
    (h : isoB σ α σ' α' t = true) :
    ∃ τ : Perm (Fin n), ⇑τ = app t ∧ τ * σ * τ⁻¹ = σ' ∧ τ * α * τ⁻¹ = α' := by
  obtain ⟨hi, hs, ha⟩ := isoB_spec.1 h
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 fun x y => hi x y), rfl, ?_, ?_⟩ <;>
    rw [mul_inv_eq_iff_eq_mul] <;> ext x <;> simp [hs, ha]

theorem isoB_tab {σ α σ' α' τ : Perm (Fin n)} (h1 : τ * σ * τ⁻¹ = σ') (h2 : τ * α * τ⁻¹ = α') :
    isoB σ α σ' α' (tab τ) = true := by
  rw [isoB_spec, app_tab]
  exact ⟨fun x y h => τ.injective h, conj_apply h1, conj_apply h2⟩

theorem transport_eq [NeZero n] {σ α σ' α' : Perm (Fin n)} {W : List (Option (List Bool))}
    (hW : validB σ α W = true) {τ : Perm (Fin n)} (h1 : τ * σ * τ⁻¹ = σ')
    (h2 : τ * α * τ⁻¹ = α') : transport W σ' α' (τ 0) = tab τ := by
  refine List.map_congr_left fun y _ => ?_
  obtain ⟨w, hw, hwy⟩ := validB_spec hW y
  simp only [hw]
  rw [← evalW_conj (conj_apply h1) (conj_apply h2), hwy]

theorem isoSearch_of_iso [NeZero n] {σ α σ' α' : Perm (Fin n)} {W : List (Option (List Bool))}
    (hW : validB σ α W = true) {τ : Perm (Fin n)} (h1 : τ * σ * τ⁻¹ = σ')
    (h2 : τ * α * τ⁻¹ = α') : isoSearch W σ α σ' α' = true :=
  List.any_eq_true.2 ⟨τ 0, List.mem_finRange _, by rw [transport_eq hW h1 h2]; exact isoB_tab h1 h2⟩

/-! ### The census -/

namespace DartMap

/-- The maps of `n` darts that are connected and spherical. -/
def SphericalMap (n : ℕ) : Type := {M : DartMap n // M.IsSpherical}

/-- Two spherical maps are equivalent when some homeomorphism of the sphere, possibly reversing
its orientation, carries one onto the other. -/
def homeoSetoid (n : ℕ) : Setoid (SphericalMap n) where
  r M M' := M.1.Homeo M'.1
  iseqv := ⟨fun M => homeo_equivalence.refl M.1, homeo_equivalence.symm,
    homeo_equivalence.trans⟩

/-- The classes of spherical maps of `n` darts up to homeomorphism. -/
def Census (n : ℕ) : Type := Quotient (homeoSetoid n)

theorem eulerB_iff (M : DartMap n) :
    eulerB M.σ M.α = true ↔ numCycles M.σ + numCycles M.α + numCycles M.φ = n + 2 := by
  rw [numCycles_eq, numCycles_eq, numCycles_eq]
  simp only [eulerB, decide_eq_true_eq]
  rfl

end DartMap

open DartMap

/-- `f` is injective, computed. -/
def injB (f : Fin n → Fin n) : Bool :=
  (List.finRange n).all fun x => (List.finRange n).all fun y => f x != f y || x == y

/-- `f` is an involution, computed. -/
def involB (f : Fin n → Fin n) : Bool := (List.finRange n).all fun x => f (f x) == x

theorem injB_spec {f : Fin n → Fin n} (h : injB f = true) : Function.Injective f := by
  intro x y hxy
  have := List.all_eq_true.1 (List.all_eq_true.1 h x (List.mem_finRange x)) y
    (List.mem_finRange y)
  simpa [hxy] using this

theorem involB_spec {f : Fin n → Fin n} (h : involB f = true) : Function.Involutive f := by
  intro x
  simpa using List.all_eq_true.1 h x (List.mem_finRange x)

/-- The permutation with table `f`, when `f` is injective. -/
noncomputable def ofFun (f : Fin n → Fin n) : Perm (Fin n) :=
  if h : Function.Injective f then Equiv.ofBijective f (Finite.injective_iff_bijective.1 h) else 1

theorem coe_ofFun {f : Fin n → Fin n} (h : Function.Injective f) : ⇑(ofFun f) = f := by
  simp [ofFun, h]

namespace Rep

/-- The tables are those of a spherical map: `σ` injective with inverse `σinv`, `α` an involution,
every dart reached from `0` by a word, Euler's relation, and the empty word at `0`. -/
def ok [NeZero n] (r : Rep n) : Bool :=
  injB (app r.σ) && ((List.finRange n).all fun x => app r.σ (app r.σinv x) == x) &&
    involB (app r.α) && validB (app r.σ) (app r.α) (words (app r.σ) (app r.α)) &&
    eulerB (app r.σ) (app r.α) && look (words (app r.σ) (app r.α)) (0 : Fin n) == some []

/-- The map with these tables. -/
noncomputable def toMap (r : Rep n) : DartMap n :=
  if h : ofFun (app r.α) * ofFun (app r.α) = 1 then ⟨ofFun (app r.σ), ofFun (app r.α), h⟩
  else ⟨1, 1, by simp⟩

variable [NeZero n] {r : Rep n}

theorem toMap_spec (h : r.ok = true) : ⇑r.toMap.σ = app r.σ ∧ ⇑r.toMap.α = app r.α ∧
    ⇑r.toMap.mirror.σ = app r.σinv ∧
    validB (app r.σ) (app r.α) (words (app r.σ) (app r.α)) = true ∧
    eulerB (app r.σ) (app r.α) = true ∧ look (words (app r.σ) (app r.α)) (0 : Fin n) = some [] := by
  simp only [ok, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hs, hsi⟩, ha⟩, hv⟩, he⟩, h0⟩ := h
  have hs' := coe_ofFun (injB_spec hs)
  have ha' := coe_ofFun (involB_spec ha).injective
  have hαα : ofFun (app r.α) * ofFun (app r.α) = 1 := by
    ext x; simp [ha', involB_spec ha x]
  have hσ : r.toMap.σ = ofFun (app r.σ) := by simp [toMap, hαα]
  have hα : r.toMap.α = ofFun (app r.α) := by simp [toMap, hαα]
  refine ⟨by rw [hσ, hs'], by rw [hα, ha'], ?_, hv, he, h0⟩
  funext x
  simp only [DartMap.mirror, hσ]
  rw [Perm.inv_eq_iff_eq, hs']
  have := List.all_eq_true.1 hsi x (List.mem_finRange x)
  exact (by simpa using this : app r.σ (app r.σinv x) = x).symm

theorem isSpherical (h : r.ok = true) : r.toMap.IsSpherical := by
  obtain ⟨hs, ha, -, hv, he, -⟩ := toMap_spec h
  rw [← hs, ← ha] at hv he
  exact ⟨connected_of_validB _ hv, (eulerB_iff _).1 he⟩

end Rep

theorem homeo_of_homeoB [NeZero n] (M : DartMap n) {W : List (Option (List Bool))} {r : Rep n}
    (hr : r.ok = true) (h : homeoB W M.σ M.α r = true) : M.Homeo r.toMap := by
  obtain ⟨hs, ha, hm, -⟩ := Rep.toMap_spec hr
  simp only [homeoB, Bool.or_eq_true, isoSearch, List.any_eq_true] at h
  rcases h with ⟨d, -, hd⟩ | ⟨d, -, hd⟩
  · rw [← hs, ← ha] at hd
    obtain ⟨τ, -, h⟩ := perm_of_isoB hd; exact Or.inl ⟨τ, h⟩
  · rw [← hm, ← ha] at hd
    obtain ⟨τ, -, h⟩ := perm_of_isoB hd; exact Or.inr ⟨τ, h⟩

theorem homeoB_of_homeo [NeZero n] {r r' : Rep n} (hr : r.ok = true) (hr' : r'.ok = true)
    (h : r.toMap.Homeo r'.toMap) :
    homeoB (words (app r.σ) (app r.α)) (app r.σ) (app r.α) r' = true := by
  obtain ⟨hs, ha, -, hv, -, -⟩ := Rep.toMap_spec hr
  obtain ⟨hs', ha', hm', -⟩ := Rep.toMap_spec hr'
  simp only [homeoB, Bool.or_eq_true]
  rw [← hs, ← ha] at hv ⊢
  rcases h with ⟨τ, h1, h2⟩ | ⟨τ, h1, h2⟩
  · left; rw [← hs', ← ha']; exact isoSearch_of_iso hv h1 h2
  · right; rw [← hm', ← ha']; exact isoSearch_of_iso hv h1 h2

/-- No two entries of `reps` are homeomorphic, computed. -/
abbrev distinctB [NeZero n] (reps : List (Rep n)) : Prop :=
  reps.Pairwise fun r r' => homeoB (words (app r.σ) (app r.α)) (app r.σ) (app r.α) r' = false

/-- `iotaL n j` is an involution moving `2j` darts. -/
def iotaOK (n : ℕ) [NeZero n] (j : ℕ) : Bool :=
  involB (app (iotaL n j)) && ((List.finRange n).countP fun x => app (iotaL n j) x != x) == 2 * j

/-- The candidates: every `σ`, with `α` one of the involutions `iotaL n j`. -/
def cands (n : ℕ) : List (List (Fin n) × ℕ) :=
  (List.range (n / 2 + 1)).flatMap fun j => (List.permutations' (List.finRange n)).map (·, j)

/-- Every spherical map is homeomorphic to an entry of `reps`, once the candidates are checked. -/
theorem exists_rep [NeZero n] (reps : List (Rep n)) (hok : reps.all Rep.ok = true)
    (hι : (List.range (n / 2 + 1)).all (iotaOK n) = true)
    (hc : (cands n).all (fun p => coverB reps p.1 p.2) = true) (M : DartMap n)
    (hM : M.IsSpherical) : ∃ r ∈ reps, M.Homeo r.toMap := by
  have hev := (cycleType_of_mul_self M.α_mul_self).2
  set c := #M.α.support / 2
  have hcn : c ≤ n / 2 := by
    have := card_le_univ M.α.support
    simp only [Fintype.card_fin] at this
    omega
  have hιc := List.all_eq_true.1 hι c (List.mem_range.2 (by omega))
  simp only [iotaOK, Bool.and_eq_true, beq_iff_eq] at hιc
  obtain ⟨hinv, hcard⟩ := hιc
  have hinv' := involB_spec hinv
  set ι := ofFun (app (iotaL n c))
  have hcoe : ⇑ι = app (iotaL n c) := coe_ofFun hinv'.injective
  have hιι : ι * ι = 1 := by ext x; simp [hcoe, hinv' x]
  have hsupp : #M.α.support = #ι.support := by
    rw [card_support_eq ι, hcoe, hcard]; omega
  obtain ⟨τ, hτ⟩ := exists_conj_of_mul_self M.α_mul_self hιι hsupp
  let M' : DartMap n := ⟨τ * M.σ * τ⁻¹, ι, hιι⟩
  have hMM' : M.Iso M' := ⟨τ, rfl, hτ⟩
  have hM' := hMM'.isSpherical hM
  have hl : tab M'.σ ∈ List.permutations' (List.finRange n) :=
    List.mem_permutations'.2 (Perm.map_finRange_perm _)
  have hcov := List.all_eq_true.1 hc (tab M'.σ, c)
    (List.mem_flatMap.2 ⟨c, List.mem_range.2 (by omega), List.mem_map.2 ⟨_, hl, rfl⟩⟩)
  simp only [coverB, app_tab, ← hcoe, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    List.any_eq_true] at hcov
  rcases hcov with (⟨⟨hc1, hc2⟩, hc3⟩ | h) | ⟨r, hr, -, h⟩
  · exact absurd hM'.1 (not_connected_of_closedB M' hc1 hc2 hc3)
  · exact absurd ((eulerB_iff M').2 hM'.2) (by rw [Bool.not_eq_true]; exact h)
  · exact ⟨r, hr, homeo_equivalence.trans hMM'.homeo
      (homeo_of_homeoB M' (List.all_eq_true.1 hok r hr) h)⟩

/-- The number of classes is the length of `reps`, once the tables and the candidates are
checked. -/
theorem card_census [NeZero n] (reps : List (Rep n)) (hok : reps.all Rep.ok = true)
    (hd : distinctB reps) (hι : (List.range (n / 2 + 1)).all (iotaOK n) = true)
    (hc : (cands n).all (fun p => coverB reps p.1 p.2) = true) :
    Nat.card (Census n) = reps.length := by
  have hok' : ∀ r ∈ reps, r.ok = true := List.all_eq_true.1 hok
  let F : Fin reps.length → Census n := fun i =>
    (⟦⟨reps[i].toMap, Rep.isSpherical (hok' _ (List.getElem_mem _))⟩⟧ : Quotient _)
  have hF : Function.Bijective F := by
    refine ⟨fun i k h => ?_, fun q => ?_⟩
    · have hH : reps[i].toMap.Homeo reps[k].toMap := Quotient.exact h
      have hp := List.pairwise_iff_getElem.1 hd
      have hb {r r' : Rep n} (hr : r ∈ reps) (hr' : r' ∈ reps) :=
        homeoB_of_homeo (hok' r hr) (hok' r' hr')
      by_contra hik
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hik) with hlt | hlt
      · simpa [hb (List.getElem_mem _) (List.getElem_mem _) hH] using hp i k i.2 k.2 hlt
      · simpa [hb (List.getElem_mem _) (List.getElem_mem _) (homeo_equivalence.symm hH)] using
          hp k i k.2 i.2 hlt
    · induction q using Quotient.inductionOn with
      | h M =>
        obtain ⟨r, hr, hH⟩ := exists_rep reps hok hι hc M.1 M.2
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
        exact ⟨⟨i, hi⟩, Quotient.sound (homeo_equivalence.symm hH)⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### Automorphisms -/

namespace DartMap

/-- `τ` carries `M` onto `M'`. -/
def IsoVia (τ : Perm (Fin n)) (M M' : DartMap n) : Prop :=
  τ * M.σ * τ⁻¹ = M'.σ ∧ τ * M.α * τ⁻¹ = M'.α

/-- The order of the full automorphism group of `M`: the relabellings carrying `M` onto itself
(the rotations of the sphere) and those carrying it onto its mirror image (the reflections). -/
@[montpellier "138, 113–119"]
noncomputable def fullAutOrder (M : DartMap n) : ℕ :=
  Nat.card {τ // IsoVia τ M M} + Nat.card {τ // IsoVia τ M M.mirror}

end DartMap

theorem card_isoVia [NeZero n] {σ α σ' α' : Perm (Fin n)} {W : List (Option (List Bool))}
    (hW : validB σ α W = true) (h0 : look W (0 : Fin n) = some []) :
    Nat.card {τ : Perm (Fin n) // τ * σ * τ⁻¹ = σ' ∧ τ * α * τ⁻¹ = α'} =
      (List.finRange n).countP fun d => isoB σ α σ' α' (transport W σ' α' d) := by
  classical
  rw [countP_finRange, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_eq_of_bijective (fun τ => ⟨τ.1 0, ?_⟩) ⟨?_, ?_⟩
  · rw [transport_eq hW τ.2.1 τ.2.2]; exact isoB_tab τ.2.1 τ.2.2
  · rintro ⟨τ, h1, h2⟩ ⟨τ', h1', h2'⟩ h
    have := congrArg app (transport_eq hW h1 h2)
    rw [Subtype.mk.inj h, transport_eq hW h1' h2', app_tab,
      app_tab] at this
    exact Subtype.ext (Equiv.ext fun x => (congrFun this x).symm)
  · rintro ⟨d, hd⟩
    obtain ⟨τ, hτ, h⟩ := perm_of_isoB hd
    refine ⟨⟨τ, h⟩, Subtype.ext ?_⟩
    change τ 0 = d
    rw [hτ, show transport W σ' α' d = tab _ from rfl, app_tab]
    simp [h0, evalW]

/-- The order of the full automorphism group, computed from the tables. -/
def autB [NeZero n] (r : Rep n) : ℕ :=
  ((List.finRange n).countP fun d => isoB (app r.σ) (app r.α) (app r.σ) (app r.α)
      (transport (words (app r.σ) (app r.α)) (app r.σ) (app r.α) d)) +
    (List.finRange n).countP fun d => isoB (app r.σ) (app r.α) (app r.σinv) (app r.α)
      (transport (words (app r.σ) (app r.α)) (app r.σinv) (app r.α) d)

theorem fullAutOrder_eq [NeZero n] {r : Rep n} (hr : r.ok = true) :
    r.toMap.fullAutOrder = autB r := by
  obtain ⟨hs, ha, hm, hv, -, h0⟩ := Rep.toMap_spec hr
  rw [← hs, ← ha] at hv h0
  rw [DartMap.fullAutOrder, autB]
  simp only [DartMap.IsoVia]
  rw [card_isoVia hv h0, card_isoVia hv h0, ← hs, ← ha, ← hm]
  rfl

theorem map_fullAutOrder [NeZero n] {reps : List (Rep n)} (hok : reps.all Rep.ok = true) :
    reps.map (fun r => r.toMap.fullAutOrder) = reps.map autB :=
  List.map_congr_left fun r hr => fullAutOrder_eq (List.all_eq_true.1 hok r hr)

/-! ### The tables -/

/-- The 1 spherical map with 1 dart, as `(σ, σ⁻¹, α)`, by vertex degrees as on the page. -/
@[montpellier "138, 113–119"]
def reps1 : List (Rep 1) := [
  ⟨[0], [0], [0]⟩]

/-- The 3 spherical maps with 2 darts, as `(σ, σ⁻¹, α)`, by vertex degrees as on the page. -/
@[montpellier "138, 113–119"]
def reps2 : List (Rep 2) := [
  ⟨[1, 0], [1, 0], [0, 1]⟩,
  ⟨[1, 0], [1, 0], [1, 0]⟩,
  ⟨[0, 1], [0, 1], [1, 0]⟩]

/-- The 3 spherical maps with 3 darts, as `(σ, σ⁻¹, α)`, by vertex degrees as on the page. -/
@[montpellier "138, 113–119"]
def reps3 : List (Rep 3) := [
  ⟨[1, 2, 0], [2, 0, 1], [0, 1, 2]⟩,
  ⟨[1, 2, 0], [2, 0, 1], [1, 0, 2]⟩,
  ⟨[0, 2, 1], [0, 2, 1], [1, 0, 2]⟩]

/-- The 9 spherical maps with 4 darts, as `(σ, σ⁻¹, α)`, by vertex degrees as on the page. -/
@[montpellier "138, 113–119"]
def reps4 : List (Rep 4) := [
  ⟨[1, 2, 3, 0], [3, 0, 1, 2], [0, 1, 2, 3]⟩,
  ⟨[1, 2, 3, 0], [3, 0, 1, 2], [1, 0, 2, 3]⟩,
  ⟨[2, 3, 1, 0], [3, 2, 0, 1], [1, 0, 2, 3]⟩,
  ⟨[1, 2, 3, 0], [3, 0, 1, 2], [1, 0, 3, 2]⟩,
  ⟨[0, 2, 3, 1], [0, 3, 1, 2], [1, 0, 2, 3]⟩,
  ⟨[0, 2, 3, 1], [0, 3, 1, 2], [1, 0, 3, 2]⟩,
  ⟨[2, 3, 0, 1], [2, 3, 0, 1], [1, 0, 2, 3]⟩,
  ⟨[2, 3, 0, 1], [2, 3, 0, 1], [1, 0, 3, 2]⟩,
  ⟨[0, 2, 1, 3], [0, 2, 1, 3], [1, 0, 3, 2]⟩]

/-- The 13 spherical maps with 5 darts, as `(σ, σ⁻¹, α)`, by vertex degrees as on the page. -/
@[montpellier "138, 113–119"]
def reps5 : List (Rep 5) := [
  ⟨[1, 2, 3, 4, 0], [4, 0, 1, 2, 3], [0, 1, 2, 3, 4]⟩,
  ⟨[1, 2, 3, 4, 0], [4, 0, 1, 2, 3], [1, 0, 2, 3, 4]⟩,
  ⟨[2, 3, 1, 4, 0], [4, 2, 0, 1, 3], [1, 0, 2, 3, 4]⟩,
  ⟨[1, 2, 3, 4, 0], [4, 0, 1, 2, 3], [1, 0, 3, 2, 4]⟩,
  ⟨[1, 2, 4, 0, 3], [3, 0, 1, 4, 2], [1, 0, 3, 2, 4]⟩,
  ⟨[0, 2, 3, 4, 1], [0, 4, 1, 2, 3], [1, 0, 2, 3, 4]⟩,
  ⟨[0, 2, 3, 4, 1], [0, 4, 1, 2, 3], [1, 0, 3, 2, 4]⟩,
  ⟨[0, 2, 4, 1, 3], [0, 3, 1, 4, 2], [1, 0, 3, 2, 4]⟩,
  ⟨[2, 3, 0, 4, 1], [2, 4, 0, 1, 3], [1, 0, 2, 3, 4]⟩,
  ⟨[1, 2, 0, 4, 3], [2, 0, 1, 4, 3], [1, 0, 3, 2, 4]⟩,
  ⟨[2, 3, 0, 4, 1], [2, 4, 0, 1, 3], [1, 0, 3, 2, 4]⟩,
  ⟨[0, 2, 4, 3, 1], [0, 4, 1, 3, 2], [1, 0, 3, 2, 4]⟩,
  ⟨[0, 2, 1, 4, 3], [0, 2, 1, 4, 3], [1, 0, 3, 2, 4]⟩]

/-- The 42 spherical maps with 6 darts, as `(σ, σ⁻¹, α)`, by vertex degrees as on the page. -/
@[montpellier "138, 113–119"]
def reps6 : List (Rep 6) := [
  ⟨[1, 2, 3, 4, 5, 0], [5, 0, 1, 2, 3, 4], [0, 1, 2, 3, 4, 5]⟩,
  ⟨[1, 2, 3, 4, 5, 0], [5, 0, 1, 2, 3, 4], [1, 0, 2, 3, 4, 5]⟩,
  ⟨[2, 3, 1, 4, 5, 0], [5, 2, 0, 1, 3, 4], [1, 0, 2, 3, 4, 5]⟩,
  ⟨[1, 2, 3, 4, 5, 0], [5, 0, 1, 2, 3, 4], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[1, 4, 3, 5, 2, 0], [5, 0, 4, 2, 1, 3], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[2, 3, 4, 5, 1, 0], [5, 4, 0, 1, 2, 3], [1, 0, 2, 3, 4, 5]⟩,
  ⟨[1, 2, 4, 5, 3, 0], [5, 0, 1, 4, 2, 3], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[1, 2, 4, 0, 5, 3], [3, 0, 1, 5, 2, 4], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[1, 2, 3, 4, 5, 0], [5, 0, 1, 2, 3, 4], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[2, 4, 5, 1, 0, 3], [4, 3, 0, 5, 1, 2], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[1, 2, 4, 0, 5, 3], [3, 0, 1, 5, 2, 4], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[0, 2, 3, 4, 5, 1], [0, 5, 1, 2, 3, 4], [1, 0, 2, 3, 4, 5]⟩,
  ⟨[0, 2, 3, 4, 5, 1], [0, 5, 1, 2, 3, 4], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[0, 4, 3, 5, 2, 1], [0, 5, 4, 2, 1, 3], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[0, 2, 4, 5, 3, 1], [0, 5, 1, 4, 2, 3], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[0, 2, 3, 4, 5, 1], [0, 5, 1, 2, 3, 4], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[0, 2, 4, 1, 5, 3], [0, 3, 1, 5, 2, 4], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[0, 2, 4, 1, 5, 3], [0, 3, 1, 5, 2, 4], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[2, 3, 0, 4, 5, 1], [2, 5, 0, 1, 3, 4], [1, 0, 2, 3, 4, 5]⟩,
  ⟨[1, 2, 4, 5, 0, 3], [4, 0, 1, 5, 2, 3], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[2, 3, 0, 4, 5, 1], [2, 5, 0, 1, 3, 4], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[2, 4, 1, 5, 0, 3], [4, 2, 0, 5, 1, 3], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[2, 4, 0, 5, 3, 1], [2, 5, 0, 4, 1, 3], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[1, 2, 4, 5, 0, 3], [4, 0, 1, 5, 2, 3], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[0, 2, 4, 3, 5, 1], [0, 5, 1, 3, 2, 4], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[0, 4, 2, 5, 3, 1], [0, 5, 2, 4, 1, 3], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[0, 2, 3, 4, 1, 5], [0, 4, 1, 2, 3, 5], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[0, 2, 4, 1, 3, 5], [0, 3, 1, 4, 2, 5], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[2, 3, 4, 5, 0, 1], [4, 5, 0, 1, 2, 3], [1, 0, 2, 3, 4, 5]⟩,
  ⟨[1, 2, 0, 4, 5, 3], [2, 0, 1, 5, 3, 4], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[2, 4, 5, 1, 3, 0], [5, 3, 0, 4, 1, 2], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[1, 2, 0, 4, 5, 3], [2, 0, 1, 5, 3, 4], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[2, 3, 4, 5, 0, 1], [4, 5, 0, 1, 2, 3], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[2, 4, 5, 1, 3, 0], [5, 3, 0, 4, 1, 2], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[0, 2, 4, 5, 1, 3], [0, 4, 1, 5, 2, 3], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[0, 2, 1, 4, 5, 3], [0, 2, 1, 5, 3, 4], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[0, 2, 1, 4, 5, 3], [0, 2, 1, 5, 3, 4], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[0, 2, 4, 5, 1, 3], [0, 4, 1, 5, 2, 3], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[0, 2, 4, 3, 1, 5], [0, 4, 1, 3, 2, 5], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[2, 4, 0, 5, 1, 3], [2, 4, 0, 5, 1, 3], [1, 0, 3, 2, 4, 5]⟩,
  ⟨[2, 4, 0, 5, 1, 3], [2, 4, 0, 5, 1, 3], [1, 0, 3, 2, 5, 4]⟩,
  ⟨[0, 2, 1, 4, 3, 5], [0, 2, 1, 4, 3, 5], [1, 0, 3, 2, 5, 4]⟩]

/-! ### The counts -/

/-- The `k`-th slice of length `m` of `L`. -/
def chunk {α : Type*} (L : List α) (m k : ℕ) : List α := (L.drop (k * m)).take m

theorem all_of_chunks {α : Type*} (L : List α) (p : α → Bool) (m K : ℕ)
    (hlen : L.length ≤ K * m) (h : ∀ k < K, (chunk L m k).all p = true) : L.all p = true := by
  refine List.all_eq_true.2 fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hm : 0 < m := Nat.pos_of_ne_zero fun h0 => by subst h0; rw [Nat.mul_zero] at hlen; omega
  have hk : i / m < K := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have hmod := Nat.mod_lt i hm
  have hdm := Nat.div_add_mod' i m
  have hlt : i / m * m + i % m < L.length := by omega
  have hidx : i % m < (chunk L m (i / m)).length := by
    simp only [chunk, List.length_take, List.length_drop]; omega
  have := List.all_eq_true.1 (h _ hk) _ (List.getElem_mem hidx)
  simpa [chunk, List.getElem_take, List.getElem_drop, hdm] using this

/-- 1 spherical map with 1 dart, up to homeomorphism. -/
@[montpellier "138, 113–119"]
theorem card_census_one : Nat.card (Census 1) = 1 := by
  apply card_census reps1 <;> decide +kernel

/-- 3 spherical maps with 2 darts, up to homeomorphism. -/
@[montpellier "138, 113–119"]
theorem card_census_two : Nat.card (Census 2) = 3 := by
  apply card_census reps2 <;> decide +kernel

/-- 3 spherical maps with 3 darts, up to homeomorphism. -/
@[montpellier "138, 113–119"]
theorem card_census_three : Nat.card (Census 3) = 3 := by
  apply card_census reps3 <;> decide +kernel

/-- 9 spherical maps with 4 darts, up to homeomorphism. -/
@[montpellier "138, 113–119"]
theorem card_census_four : Nat.card (Census 4) = 9 := by
  apply card_census reps4 <;> decide +kernel

/-- 13 spherical maps with 5 darts, up to homeomorphism. -/
@[montpellier "138, 113–119"]
theorem card_census_five : Nat.card (Census 5) = 13 := by
  apply card_census reps5 <;> decide +kernel

theorem cover_six_0 :
    (chunk (cands 6) 240 0).all (fun p => coverB reps6 p.1 p.2) = true := by
  decide +kernel

theorem cover_six_1 :
    (chunk (cands 6) 240 1).all (fun p => coverB reps6 p.1 p.2) = true := by
  decide +kernel

theorem cover_six_2 :
    (chunk (cands 6) 240 2).all (fun p => coverB reps6 p.1 p.2) = true := by
  decide +kernel

theorem cover_six_3 :
    (chunk (cands 6) 240 3).all (fun p => coverB reps6 p.1 p.2) = true := by
  decide +kernel

theorem cover_six_4 :
    (chunk (cands 6) 240 4).all (fun p => coverB reps6 p.1 p.2) = true := by
  decide +kernel

theorem cover_six_5 :
    (chunk (cands 6) 240 5).all (fun p => coverB reps6 p.1 p.2) = true := by
  decide +kernel

theorem cover_six_6 :
    (chunk (cands 6) 240 6).all (fun p => coverB reps6 p.1 p.2) = true := by
  decide +kernel

theorem cover_six_7 :
    (chunk (cands 6) 240 7).all (fun p => coverB reps6 p.1 p.2) = true := by
  decide +kernel

theorem cover_six_8 :
    (chunk (cands 6) 240 8).all (fun p => coverB reps6 p.1 p.2) = true := by
  decide +kernel

theorem cover_six_9 :
    (chunk (cands 6) 240 9).all (fun p => coverB reps6 p.1 p.2) = true := by
  decide +kernel

theorem cover_six_10 :
    (chunk (cands 6) 240 10).all (fun p => coverB reps6 p.1 p.2) = true := by
  decide +kernel

theorem cover_six_11 :
    (chunk (cands 6) 240 11).all (fun p => coverB reps6 p.1 p.2) = true := by
  decide +kernel

theorem cover_six : (cands 6).all (fun p => coverB reps6 p.1 p.2) = true :=
  all_of_chunks _ _ 240 12 (by decide +kernel) fun k hk => by
    interval_cases k
    exacts [cover_six_0, cover_six_1, cover_six_2, cover_six_3, cover_six_4, cover_six_5,
      cover_six_6, cover_six_7, cover_six_8, cover_six_9, cover_six_10, cover_six_11]

/-- 42 spherical maps with 6 darts, up to homeomorphism. -/
@[montpellier "138, 118–119"]
theorem card_census_six : Nat.card (Census 6) = 42 :=
  card_census reps6 (by decide +kernel) (by decide +kernel) (by decide +kernel) cover_six

/-- The page's numbers: `1, 3, 3, 9, 13, 42` maps with `1, …, 6` darts. -/
@[montpellier "138, 113–119"]
theorem census_counts :
    [Nat.card (Census 1), Nat.card (Census 2), Nat.card (Census 3), Nat.card (Census 4),
      Nat.card (Census 5), Nat.card (Census 6)] = [1, 3, 3, 9, 13, 42] := by
  rw [card_census_one, card_census_two, card_census_three, card_census_four, card_census_five,
    card_census_six]

/-! ### The groups -/

/-- The orders of the full automorphism groups of the maps with 1 dart, in the order of `reps1`. -/
@[montpellier "138, 113–119"]
theorem fullAutOrder_reps1 :
    reps1.map (fun r => r.toMap.fullAutOrder) = [2] := by
  rw [map_fullAutOrder (by decide +kernel)]; decide +kernel

/-- The orders of the full automorphism groups of the maps with 2 darts, in the order of `reps2`. -/
@[montpellier "138, 113–119"]
theorem fullAutOrder_reps2 :
    reps2.map (fun r => r.toMap.fullAutOrder) = [4, 4, 4] := by
  rw [map_fullAutOrder (by decide +kernel)]; decide +kernel

/-- The orders of the full automorphism groups of the maps with 3 darts, in the order of `reps3`. -/
@[montpellier "138, 113–119"]
theorem fullAutOrder_reps3 :
    reps3.map (fun r => r.toMap.fullAutOrder) = [6, 2, 2] := by
  rw [map_fullAutOrder (by decide +kernel)]; decide +kernel

/-- The orders of the full automorphism groups of the maps with 4 darts, in the order of `reps4`. -/
@[montpellier "138, 113–119"]
theorem fullAutOrder_reps4 :
    reps4.map (fun r => r.toMap.fullAutOrder) = [8, 2, 4, 4, 2, 2, 4, 8, 4] := by
  rw [map_fullAutOrder (by decide +kernel)]; decide +kernel

/-- The orders of the full automorphism groups of the maps with 5 darts, in the order of `reps5`. -/
@[montpellier "138, 113–119"]
theorem fullAutOrder_reps5 :
    reps5.map (fun r => r.toMap.fullAutOrder) = [10, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2] := by
  rw [map_fullAutOrder (by decide +kernel)]; decide +kernel

/-- The orders of the full automorphism groups of the maps with 6 darts, in the order of `reps6`. -/
@[montpellier "138, 113–119"]
theorem fullAutOrder_reps6 :
    reps6.map (fun r => r.toMap.fullAutOrder) = [12, 2, 2, 2, 4, 4, 1, 2, 6, 4, 4, 2, 1, 2, 1, 2, 2,
      2, 2, 1, 2, 2, 4, 2, 2, 4, 2, 4, 4, 2, 4, 4, 4, 12, 1, 2, 2, 2, 6, 4, 12, 4] := by
  rw [map_fullAutOrder (by decide +kernel)]; decide +kernel

end Grothendieck.Folder138
