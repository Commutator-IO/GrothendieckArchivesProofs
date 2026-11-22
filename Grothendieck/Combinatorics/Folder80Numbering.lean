module

public import OpenProblems.Pseudolines
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 80, page 28: the numbering lemma, for combinatorial pseudoline maps

Proof of `OpenProblems.Pseudolines.NumberingLemma` (the proof is the edition's, in the
Proposition of § Pseudoline arrangements of the note on the open problems): the lines of a
bigon-free `PseudolineMap` can be numbered `ℓ₀, ℓ₁, …` so that the first four form a `II_4` or
the first six a complete quadrangle `III_6`, and every partial arrangement `{ℓ₀, …, ℓ_{k-1}}`
from there on is bigon-free.

**Reduction** (`bigonFree_of`, `Good.mono`). A line `l` is *good* for a set `S` of lines
(`Good`) when it carries three distinct vertices, each on a line of `S` other than `l`. Every
such vertex is a vertex of the partial arrangement of any set of lines containing `S` and `l`,
so if every line of a set `T` is good for some subset of `T`, the partial arrangement of `T`
is bigon-free: adding lines never removes a vertex of a line already there.

**The quadrangle** (`good_of_pencil`). A line not through a vertex `x` meets three distinct
lines through `x` in three distinct vertices. In a `III_6` every vertex is on three of the six
sides, and a line misses one of the four vertices (through two of them it is the side joining
them, and misses a third): every line is good for the six sides (`good_iii6`). Numbering: the
six sides, then the other lines in any order.

**Otherwise** the map contains no `III_6`. Melchior and `exists_gp4` give four lines
`x, y, z, w` in general position, each good for them (`good_gp4`). A further line not good for
them meets them in two vertices only, two opposite vertices of the quadrilateral
(`diag_of_not_good`): it is a diagonal. Two diagonals are equal or give a `III_6`
(`diag_unique`, `iii6_of`), so at most one line `δ` is not good for `x, y, z, w`; it is good for
all the lines (the map is bigon-free). Numbering: `x, y, z, w`, the other lines, and `δ` last
(`exists_numbering`), so that a partial arrangement containing `δ` is the whole map. This covers
the case where the map itself is `II_4` (`n = k₀ = 4`).
-/

namespace Grothendieck.Folder80Numbering

open Grothendieck.Folder80Maps2 OpenProblems.Pseudolines

variable {D L : Type*} {X : PseudolineMap D L}

/-- The line `l` carries three distinct vertices, each on a line of `S` other than `l`. -/
def Good (X : PseudolineMap D L) (S : Set L) (l : L) : Prop :=
  ∃ p q r, X.On p l ∧ X.On q l ∧ X.On r l ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    (∃ m ∈ S, m ≠ l ∧ X.On p m) ∧ (∃ m ∈ S, m ≠ l ∧ X.On q m) ∧ (∃ m ∈ S, m ≠ l ∧ X.On r m)

theorem Good.mono {S T : Set L} {l : L} (h : Good X S l) (hST : S ⊆ T) : Good X T l := by
  obtain ⟨p, q, r, h1, h2, h3, h4, h5, h6, ⟨a, ha, ha', ha''⟩, ⟨b, hb, hb', hb''⟩,
    ⟨c, hc, hc', hc''⟩⟩ := h
  exact ⟨p, q, r, h1, h2, h3, h4, h5, h6, ⟨a, hST ha, ha', ha''⟩, ⟨b, hST hb, hb', hb''⟩,
    ⟨c, hST hc, hc', hc''⟩⟩

/-- Three distinct vertices of `l`, on three lines of `S` other than `l`. -/
theorem good_of_three {S : Set L} {l a b c : L} {p q r : X.M.Vtx} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hal : a ≠ l) (hbl : b ≠ l) (hcl : c ≠ l) (hpa : X.On p a) (hqb : X.On q b)
    (hrc : X.On r c) (hp : X.On p l) (hq : X.On q l) (hr : X.On r l) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) : Good X S l :=
  ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr, ⟨a, ha, hal, hpa⟩, ⟨b, hb, hbl, hqb⟩, ⟨c, hc, hcl, hrc⟩⟩

/-- **Adding lines removes no vertex**: if every line of `T` is good for a subset of `T`, the
partial arrangement of `T` is bigon-free. -/
theorem bigonFree_of {T : Set L} (h : ∀ l ∈ T, Good X T l) : BigonFree (PartialOn X T) := by
  rintro ⟨l, hl⟩
  obtain ⟨p, q, r, h1, h2, h3, h4, h5, h6, ⟨a, ha, ha', ha''⟩, ⟨b, hb, hb', hb''⟩,
    ⟨c, hc, hc', hc''⟩⟩ := h l hl
  exact ⟨⟨p, l, hl, a, ha, ha'.symm, h1, ha''⟩, ⟨q, l, hl, b, hb, hb'.symm, h2, hb''⟩,
    ⟨r, l, hl, c, hc, hc'.symm, h3, hc''⟩, h1, h2, h3, fun h => h4 (congrArg Subtype.val h),
    fun h => h5 (congrArg Subtype.val h), fun h => h6 (congrArg Subtype.val h)⟩

/-- Every vertex of a line is on a second line. -/
theorem two' (X : PseudolineMap D L) : ∀ p l, X.On p l → ∃ m, m ≠ l ∧ X.On p m :=
  fun _ _ ⟨d, hd, hl⟩ => by
    obtain ⟨e, he, hle⟩ := X.two d
    exact ⟨_, hl ▸ hle, e, he.trans hd, rfl⟩

/-- In a bigon-free map, every line is good for all the lines. -/
theorem good_univ (hbf : BigonFree X.On) (l : L) : Good X Set.univ l := by
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := hbf l
  obtain ⟨a, ha, hpa⟩ := two' X p l hp
  obtain ⟨b, hb, hqb⟩ := two' X q l hq
  obtain ⟨c, hc, hrc⟩ := two' X r l hr
  exact good_of_three trivial trivial trivial ha hb hc hpa hqb hrc hp hq hr hpq hpr hqr

/-- A line not through `x` meets three distinct lines through `x` in three distinct vertices. -/
theorem good_of_pencil {S : Set L} {l a b c : L} {x : X.M.Vtx} (hx : ¬X.On x l) (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hxa : X.On x a)
    (hxb : X.On x b) (hxc : X.On x c) : Good X S l := by
  have hal : a ≠ l := fun h => hx (h ▸ hxa)
  have hbl : b ≠ l := fun h => hx (h ▸ hxb)
  have hcl : c ≠ l := fun h => hx (h ▸ hxc)
  obtain ⟨p, ⟨hpa, hpl⟩, -⟩ := X.meet a l hal
  obtain ⟨q, ⟨hqb, hql⟩, -⟩ := X.meet b l hbl
  obtain ⟨r, ⟨hrc, hrl⟩, -⟩ := X.meet c l hcl
  refine good_of_three ha hb hc hal hbl hcl hpa hqb hrc hpl hql hrl ?_ ?_ ?_ <;> rintro rfl
  · exact hx ((X.meet a b hab).unique ⟨hpa, hqb⟩ ⟨hxa, hxb⟩ ▸ hpl)
  · exact hx ((X.meet a c hac).unique ⟨hpa, hrc⟩ ⟨hxa, hxc⟩ ▸ hpl)
  · exact hx ((X.meet b c hbc).unique ⟨hqb, hrc⟩ ⟨hxb, hxc⟩ ▸ hql)

/-- A line of four lines in general position is good for the other three. -/
theorem good_gp4 {S : Set L} {a b c d : L} (g : GP4 X.On a b c d) (hb : b ∈ S) (hc : c ∈ S)
    (hd : d ∈ S) : Good X S a := by
  obtain ⟨hab, hac, had, -, -, -, habc, habd, hacd, -⟩ := g
  obtain ⟨p, ⟨hpb, hpa⟩, -⟩ := X.meet b a hab.symm
  obtain ⟨q, ⟨hqc, hqa⟩, -⟩ := X.meet c a hac.symm
  obtain ⟨r, ⟨hrd, hra⟩, -⟩ := X.meet d a had.symm
  exact good_of_three hb hc hd hab.symm hac.symm had.symm hpb hqc hrd hpa hqa hra
    (ne_of_nc habc hpb hqa hqc) (ne_of_nc habd hpb hra hrd) (ne_of_nc hacd hqc hra hrd)

/-- A fifth line that is not good for four lines in general position is a diagonal: it passes
through two opposite vertices of the quadrilateral. -/
theorem diag_of_not_good {S : Set L} {a b c d l : L} (g : GP4 X.On a b c d) (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) (hla : l ≠ a) (hlb : l ≠ b) (hlc : l ≠ c)
    (hld : l ≠ d) (h : ¬Good X S l) :
    (C X.On a b l ∧ C X.On c d l) ∨ (C X.On a c l ∧ C X.On b d l) ∨
      (C X.On a d l ∧ C X.On b c l) := by
  obtain ⟨-, -, -, -, -, -, habc, habd, hacd, hbcd⟩ := g
  obtain ⟨pa, ⟨hpa, hpal⟩, -⟩ := X.meet a l hla.symm
  obtain ⟨pb, ⟨hpb, hpbl⟩, -⟩ := X.meet b l hlb.symm
  obtain ⟨pc, ⟨hpc, hpcl⟩, -⟩ := X.meet c l hlc.symm
  obtain ⟨pd, ⟨hpd, hpdl⟩, -⟩ := X.meet d l hld.symm
  have t1 : ¬(pa ≠ pb ∧ pa ≠ pc ∧ pb ≠ pc) := fun ⟨h1, h2, h3⟩ => h (good_of_three ha hb hc
    hla.symm hlb.symm hlc.symm hpa hpb hpc hpal hpbl hpcl h1 h2 h3)
  have t2 : ¬(pa ≠ pb ∧ pa ≠ pd ∧ pb ≠ pd) := fun ⟨h1, h2, h3⟩ => h (good_of_three ha hb hd
    hla.symm hlb.symm hld.symm hpa hpb hpd hpal hpbl hpdl h1 h2 h3)
  have t3 : ¬(pa ≠ pc ∧ pa ≠ pd ∧ pc ≠ pd) := fun ⟨h1, h2, h3⟩ => h (good_of_three ha hc hd
    hla.symm hlc.symm hld.symm hpa hpc hpd hpal hpcl hpdl h1 h2 h3)
  have t4 : ¬(pb ≠ pc ∧ pb ≠ pd ∧ pc ≠ pd) := fun ⟨h1, h2, h3⟩ => h (good_of_three hb hc hd
    hlb.symm hlc.symm hld.symm hpb hpc hpd hpbl hpcl hpdl h1 h2 h3)
  have n1 : ¬(pa = pb ∧ pa = pc) := fun ⟨h1, h2⟩ => habc ⟨pa, hpa, h1 ▸ hpb, h2 ▸ hpc⟩
  have n2 : ¬(pa = pb ∧ pa = pd) := fun ⟨h1, h2⟩ => habd ⟨pa, hpa, h1 ▸ hpb, h2 ▸ hpd⟩
  have n3 : ¬(pa = pc ∧ pa = pd) := fun ⟨h1, h2⟩ => hacd ⟨pa, hpa, h1 ▸ hpc, h2 ▸ hpd⟩
  have n4 : ¬(pb = pc ∧ pb = pd) := fun ⟨h1, h2⟩ => hbcd ⟨pb, hpb, h1 ▸ hpc, h2 ▸ hpd⟩
  have key : (pa = pb ∧ pc = pd) ∨ (pa = pc ∧ pb = pd) ∨ (pa = pd ∧ pb = pc) := by grind
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨⟨pa, hpa, h1 ▸ hpb, hpal⟩, ⟨pc, hpc, h2 ▸ hpd, hpcl⟩⟩
  · exact .inr (.inl ⟨⟨pa, hpa, h1 ▸ hpc, hpal⟩, ⟨pb, hpb, h2 ▸ hpd, hpbl⟩⟩)
  · exact .inr (.inr ⟨⟨pa, hpa, h1 ▸ hpd, hpal⟩, ⟨pb, hpb, h2 ▸ hpc, hpbl⟩⟩)

/-- The numbering: `B` first, the lines in neither `B` nor `late` next, `late` (at most one
line) last. The first `|B|` lines are those of `B`; from there on every initial segment contains
`B`, and one containing a line of `late` contains all the lines. -/
theorem exists_numbering [Finite L] (B late : List L) (hB : B.Nodup) (hl : late.length ≤ 1)
    (hdisj : ∀ x ∈ late, x ∉ B) :
    ∃ (n : ℕ) (e : Fin n ≃ L), e '' {i | (i : ℕ) < B.length} = {x | x ∈ B} ∧
      ∀ k, B.length ≤ k → k ≤ n → (∀ x ∈ B, x ∈ e '' {i | (i : ℕ) < k}) ∧
        ∀ x ∈ late, x ∈ e '' {i | (i : ℕ) < k} → ∀ y, y ∈ e '' {i | (i : ℕ) < k} := by
  classical
  have := Fintype.ofFinite L
  set mid := (Finset.univ.filter fun x => x ∉ B ∧ x ∉ late).toList
  set xs := B ++ (mid ++ late)
  have hlate : late.Nodup := by
    match late, hl with
    | [], _ => exact List.nodup_nil
    | [_], _ => exact List.nodup_singleton _
  have hnd : xs.Nodup := by
    simp only [xs, mid, List.nodup_append, Finset.nodup_toList, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and, List.mem_append]
    refine ⟨hB, ⟨hlate, fun a ha b hb h => ha.2 (h ▸ hb)⟩, fun a ha b hb h => ?_⟩
    rcases hb with hb | hb
    · exact hb.1 (h ▸ ha)
    · exact hdisj b hb (h ▸ ha)
  have hall : ∀ x, x ∈ xs := fun x => by
    by_cases h1 : x ∈ B
    · exact List.mem_append_left _ h1
    by_cases h2 : x ∈ late
    · exact List.mem_append_right _ (List.mem_append_right _ h2)
    · exact List.mem_append_right _ (List.mem_append_left _ (by simp [mid, h1, h2]))
  let e : Fin xs.length ≃ L := Equiv.ofBijective xs.get
    ⟨List.nodup_iff_injective_get.1 hnd, fun x => List.mem_iff_get.1 (hall x)⟩
  have he : ∀ k x, x ∈ e '' {i | (i : ℕ) < k} ↔ x ∈ xs.take k := fun k x => by
    rw [List.mem_take_iff_getElem]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, lt_min hi i.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, (lt_min_iff.1 hj).2⟩, (lt_min_iff.1 hj).1, rfl⟩
  have hB' : ∀ k, B.length ≤ k → ∀ x ∈ B, x ∈ xs.take k := fun k hk x hx => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    exact List.mem_take_iff_getElem.2 ⟨j, lt_min (hj.trans_le hk)
      (hj.trans_le (by simp [xs])), by simp [xs, List.getElem_append_left hj]⟩
  refine ⟨xs.length, e, ?_, fun k hk hkn => ⟨fun x hx => (he k x).2 (hB' k hk x hx), ?_⟩⟩
  · ext x
    rw [Set.mem_ofPred_eq, he, List.take_left' rfl]
  · intro x hx hxk y
    rw [he] at hxk ⊢
    rcases hkn.lt_or_eq with hkn | rfl
    · exfalso
      have hlen : late.length = 1 := by
        have := List.length_pos_of_mem hx; omega
      have hk' : k ≤ (B ++ mid).length := by
        simp only [xs, List.length_append] at hkn ⊢; omega
      rw [show xs = (B ++ mid) ++ late by simp [xs], List.take_append_of_le_length hk'] at hxk
      rcases List.mem_append.1 (List.mem_of_mem_take hxk) with h | h
      · exact hdisj x hx h
      · simp [mid] at h; exact h.2 hx
    · rw [List.take_of_length_le le_rfl]; exact hall y

/-- From a numbering in which every line not in `late` is good for `B`, the partial
arrangements from `|B|` lines on are bigon-free. -/
theorem assemble [Finite L] (hbf : BigonFree X.On) (B late : List L) (hB : B.Nodup)
    (hl : late.length ≤ 1) (hdisj : ∀ x ∈ late, x ∉ B)
    (hgood : ∀ l, l ∉ late → Good X {x | x ∈ B} l) :
    ∃ (n : ℕ) (e : Fin n ≃ L), e '' {i | (i : ℕ) < B.length} = {x | x ∈ B} ∧
      ∀ k, B.length ≤ k → k ≤ n → BigonFree (PartialOn X (e '' {i | (i : ℕ) < k})) := by
  obtain ⟨n, e, h1, h2⟩ := exists_numbering B late hB hl hdisj
  refine ⟨n, e, h1, fun k hk hkn => bigonFree_of fun l hlk => ?_⟩
  obtain ⟨hBk, hlate⟩ := h2 k hk hkn
  by_cases h : l ∈ late
  · exact (good_univ hbf l).mono fun y _ => hlate l h hlk y
  · exact (hgood l h).mono fun y hy => hBk y hy

/-- Four lines in general position stay in general position in a partial arrangement. -/
theorem gp4_partial {S : Set L} {a b c d : L} (g : GP4 X.On a b c d) (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S) :
    GP4 (PartialOn X S) ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := g
  have hC : ∀ {u v w : S}, C (PartialOn X S) u v w → C X.On u.1 v.1 w.1 :=
    fun ⟨p, hp1, hp2, hp3⟩ => ⟨p.1, hp1, hp2, hp3⟩
  exact ⟨fun h => h1 (congrArg Subtype.val h), fun h => h2 (congrArg Subtype.val h),
    fun h => h3 (congrArg Subtype.val h), fun h => h4 (congrArg Subtype.val h),
    fun h => h5 (congrArg Subtype.val h), fun h => h6 (congrArg Subtype.val h),
    fun h => h7 (hC h), fun h => h8 (hC h), fun h => h9 (hC h), fun h => h10 (hC h)⟩

/-- The case of a complete quadrangle. -/
theorem numbering_iii6 [Finite L] (hbf : BigonFree X.On) (h6 : HasIII6 X.On) :
    ∃ (n : ℕ) (e : Fin n ≃ L), HasIII6 (PartialOn X (e '' {i | (i : ℕ) < 6})) ∧
      ∀ k, 6 ≤ k → k ≤ n → BigonFree (PartialOn X (e '' {i | (i : ℕ) < k})) := by
  obtain ⟨p, q, r, s, ⟨m1, h1p, h1q⟩, ⟨m2, h2p, h2r⟩, ⟨m3, h3p, h3s⟩, ⟨m4, h4q, h4r⟩,
    ⟨m5, h5q, h5s⟩, ⟨m6, h6r, h6s⟩, npqr, npqs, nprs, nqrs⟩ := h6
  have d12 : m1 ≠ m2 := fun h => npqr m1 h1p h1q (h ▸ h2r)
  have d13 : m1 ≠ m3 := fun h => npqs m1 h1p h1q (h ▸ h3s)
  have d14 : m1 ≠ m4 := fun h => npqr m1 h1p h1q (h ▸ h4r)
  have d15 : m1 ≠ m5 := fun h => npqs m1 h1p h1q (h ▸ h5s)
  have d16 : m1 ≠ m6 := fun h => npqr m1 h1p h1q (h ▸ h6r)
  have d23 : m2 ≠ m3 := fun h => nprs m2 h2p h2r (h ▸ h3s)
  have d24 : m2 ≠ m4 := fun h => npqr m2 h2p (h ▸ h4q) h2r
  have d25 : m2 ≠ m5 := fun h => npqr m2 h2p (h ▸ h5q) h2r
  have d26 : m2 ≠ m6 := fun h => nprs m2 h2p h2r (h ▸ h6s)
  have d34 : m3 ≠ m4 := fun h => npqs m3 h3p (h ▸ h4q) h3s
  have d35 : m3 ≠ m5 := fun h => npqs m3 h3p (h ▸ h5q) h3s
  have d36 : m3 ≠ m6 := fun h => nprs m3 h3p (h ▸ h6r) h3s
  have d45 : m4 ≠ m5 := fun h => nqrs m4 h4q h4r (h ▸ h5s)
  have d46 : m4 ≠ m6 := fun h => nqrs m4 h4q h4r (h ▸ h6s)
  have d56 : m5 ≠ m6 := fun h => nqrs m5 h5q (h ▸ h6r) h5s
  have hpq : p ≠ q := fun h => npqr m2 h2p (h ▸ h2p) h2r
  set B := [m1, m2, m3, m4, m5, m6]
  have hB : B.Nodup := by simp [B, *]
  have hgood : ∀ l, Good X {x | x ∈ B} l := fun l => by
    by_cases hp : X.On p l
    · by_cases hq : X.On q l
      · exact good_of_pencil (npqr l hp hq) (by simp [B]) (by simp [B]) (by simp [B]) d24 d26
          d46 h2r h4r h6r
      · exact good_of_pencil hq (by simp [B]) (by simp [B]) (by simp [B]) d14 d15 d45 h1q h4q
          h5q
    · exact good_of_pencil hp (by simp [B]) (by simp [B]) (by simp [B]) d12 d13 d23 h1p h2p h3p
  obtain ⟨n, e, h1, h2⟩ := assemble hbf B [] hB (by simp) (by simp) fun l _ => hgood l
  refine ⟨n, e, ?_, h2⟩
  rw [show (6 : ℕ) = B.length from rfl, h1]
  have M : ∀ {m}, m ∈ B → m ∈ {x | x ∈ B} := id
  exact ⟨⟨p, m1, M (by simp [B]), m2, M (by simp [B]), d12, h1p, h2p⟩,
    ⟨q, m1, M (by simp [B]), m4, M (by simp [B]), d14, h1q, h4q⟩,
    ⟨r, m2, M (by simp [B]), m4, M (by simp [B]), d24, h2r, h4r⟩,
    ⟨s, m3, M (by simp [B]), m5, M (by simp [B]), d35, h3s, h5s⟩,
    ⟨⟨m1, by simp [B]⟩, h1p, h1q⟩, ⟨⟨m2, by simp [B]⟩, h2p, h2r⟩, ⟨⟨m3, by simp [B]⟩, h3p, h3s⟩,
    ⟨⟨m4, by simp [B]⟩, h4q, h4r⟩, ⟨⟨m5, by simp [B]⟩, h5q, h5s⟩, ⟨⟨m6, by simp [B]⟩, h6r, h6s⟩,
    fun m => npqr m.1, fun m => npqs m.1, fun m => nprs m.1, fun m => nqrs m.1⟩

/-- The case without a complete quadrangle: four lines in general position first, the lone
diagonal (if any) last. -/
theorem numbering_ii4 [Fintype D] [Finite L] (hbf : BigonFree X.On) (n6 : ¬HasIII6 X.On) :
    ∃ (n : ℕ) (e : Fin n ≃ L), IsII4 (PartialOn X (e '' {i | (i : ℕ) < 4})) ∧
      ∀ k, 4 ≤ k → k ≤ n → BigonFree (PartialOn X (e '' {i | (i : ℕ) < k})) := by
  classical
  obtain ⟨v, a, b, hab, hva, hvb, honly⟩ := PseudolineMap.melchior hbf
  obtain ⟨x, y, z, w, g⟩ := exists_gp4 X.meet (two' X) hbf hab hva hvb honly
  set B := [x, y, z, w]
  set S := {u | u ∈ B}
  have mx : x ∈ S := by simp [S, B]
  have my : y ∈ S := by simp [S, B]
  have mz : z ∈ S := by simp [S, B]
  have mw : w ∈ S := by simp [S, B]
  have hB : B.Nodup := by
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := g
    simp [B, *]
  have gQ : ∀ l ∈ B, Good X S l := fun l hl => by
    simp only [B, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact good_gp4 g my mz mw
    · exact good_gp4 g.swap12 mx mz mw
    · exact good_gp4 g.swap23.swap12 mx my mw
    · exact good_gp4 g.swap34.swap23.swap12 mx my mz
  have cls : ∀ l, ¬Good X S l → _ := fun l hl =>
    have hlB : l ∉ B := fun h => hl (gQ l h)
    diag_of_not_good g mx my mz mw (fun h => hlB (by simp [B, h]))
      (fun h => hlB (by simp [B, h])) (fun h => hlB (by simp [B, h]))
      (fun h => hlB (by simp [B, h])) hl
  have g2 := g.swap23
  have g3 := g.swap34.swap23
  have uniq : ∀ δ m, ¬Good X S δ → ¬Good X S m → m = δ := fun δ m hδ hm => by
    rcases cls δ hδ with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rcases cls m hm with ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2⟩
    · exact diag_unique X.meet g f1 f2 e1 e2
    · exact (n6 (iii6_of X.meet g e1 e2 f1 f2)).elim
    · exact (n6 (iii6_of X.meet g.swap34 e1 e2.swap12 f1 f2)).elim
    · exact (n6 (iii6_of X.meet g f1 f2 e1 e2)).elim
    · exact diag_unique X.meet g2 f1 f2 e1 e2
    · exact (n6 (iii6_of X.meet g2.swap34 e1 e2.swap12 f1 f2.swap12)).elim
    · exact (n6 (iii6_of X.meet g.swap34 f1 f2.swap12 e1 e2)).elim
    · exact (n6 (iii6_of X.meet g2.swap34 f1 f2.swap12 e1 e2.swap12)).elim
    · exact diag_unique X.meet g3 f1 f2 e1 e2
  have main : ∃ late : List L, late.length ≤ 1 ∧ (∀ u ∈ late, u ∉ B) ∧
      ∀ l, l ∉ late → Good X S l := by
    by_cases hbad : ∃ δ, ¬Good X S δ
    · obtain ⟨δ, hδ⟩ := hbad
      refine ⟨[δ], by simp, fun u hu huB => ?_, fun l hl => by_contra fun h => ?_⟩
      · rw [List.mem_singleton] at hu; exact hδ (hu ▸ gQ u huB)
      · exact hl (List.mem_singleton.2 (uniq δ l hδ h))
    · exact ⟨[], by simp, by simp, fun l _ => by_contra fun h => hbad ⟨l, h⟩⟩
  obtain ⟨late, hl1, hdisj, hgood⟩ := main
  obtain ⟨n, e, h1, h2⟩ := assemble hbf B late hB hl1 hdisj hgood
  refine ⟨n, e, ?_, h2⟩
  rw [show (4 : ℕ) = B.length from rfl, h1]
  refine ⟨⟨x, mx⟩, ⟨y, my⟩, ⟨z, mz⟩, ⟨w, mw⟩, gp4_partial g mx my mz mw, fun m => ?_⟩
  obtain ⟨m, hm⟩ := m
  simp only [B, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> simp

/-- **The numbering lemma** (folder 80, p. 28): the lines of a bigon-free pseudoline map can be
numbered `ℓ₀, ℓ₁, …` so that the first four form a `II_4` or the first six a complete
quadrangle `III_6`, and every partial arrangement `{ℓ₀, …, ℓ_{k-1}}` from there on is
bigon-free. -/
@[montpellier "80, 28"]
theorem numberingLemma : NumberingLemma := by
  intro D L _ _ X hbf
  by_cases h6 : HasIII6 X.On
  · obtain ⟨n, e, h1, h2⟩ := numbering_iii6 hbf h6
    exact ⟨n, e, 6, .inr ⟨rfl, h1⟩, h2⟩
  · obtain ⟨n, e, h1, h2⟩ := numbering_ii4 hbf h6
    exact ⟨n, e, 4, .inl ⟨rfl, h1⟩, h2⟩

end Grothendieck.Folder80Numbering
