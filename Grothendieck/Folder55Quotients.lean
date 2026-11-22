module

public import Grothendieck.Folder55Ideals
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 55, page 13: condition (v) of Lemme B holds for every coherent Ideal

Condition (v) of Lemme B (folder 55, page 13; see `Grothendieck/Folder55LemmaB.lean`) is stated
for every coherent Ideal `𝒥` of `𝒪_X`, through the ringed space `Y = (Supp 𝒪_X/𝒥, 𝒪_X/𝒥)`.
`Grothendieck/Folder55LemmaB.lean` proves it for `𝒥 = 0` only. This file builds the quotient
`𝒪/𝒥` and its support for an arbitrary Ideal `𝒥` of the counterexample and proves (v) for every
Ideal of finite type, coherent ones included. So the counterexample satisfies (i), (ii), (iv)
and (v) as stated, and Lemme B, read for an arbitrary ringed space, is refuted
(`lemmeB_counterexample_v`).

**The finding.** (v) holds for every Ideal of finite type, and the hypothesis that `𝒪_{Y,y}` be
a domain is never used. At a point `y ≠ infty` it holds for any sheaf at all, because `y` has a
smallest open neighbourhood: a section vanishing on some neighbourhood of `y` vanishes on that
smallest one. At `infty`, the stalk `k` is a field, so `infty ∈ Supp 𝒪/𝒥` forces `𝒥_infty = 0`.
Since `𝒥` is of finite type, its finitely many local generators near `infty` then vanish on a
common `B_M`, so `𝒥 = 0` on `B_M`. There `𝒪/𝒥 = 𝒪`, and (v) is `identity_principle`. No
classification of the coherent Ideals is needed.

**What is proved.** An Ideal is a sub-sheaf of modules `𝒥 : IdealO κ ε ι` of `𝒪`
(`SheafOfModules.Submodule`). Its sections over `U` as functions are `Jsec 𝒥 U`.
* `O_eq_zero_near`: a section of `𝒪` is determined near `x` by its value at `x`.
  `stalkEquivO`: Mathlib's stalk `(Opre κ ε ι).stalk x` is isomorphic to `OStalk x`, the ring of
  values at `x` of the sections near `x`.
* `Jst 𝒥 x`, an ideal of `OStalk x`, is the stalk `𝒥_x`; `mem_Jgerm` identifies its image
  `Jgerm 𝒥 x` in Mathlib's stalk as the ideal of germs of `𝒥`. `Fib 𝒥 x = 𝒪_x/𝒥_x`, and
  `fibEquiv` gives `Fib 𝒥 x ≃+* 𝒪_x ⧸ Jgerm 𝒥 x`.
* `Qpre 𝒥`, `Qsheaf 𝒥`: **the sheaf of rings `𝒪/𝒥`**. Its sections are the functions with
  values in the `Fib 𝒥 x` that are locally the class of a section of `𝒪` (`IsQ`). `quotMap` is
  the quotient map `𝒪 → 𝒪/𝒥`.
* `stalkQuotientEquiv`: **the stalk of `𝒪/𝒥` at `x` is `𝒪_x/𝒥_x`** (`stalkEquivQ`,
  `Q_eq_zero_near`, `fibEquiv`).
* `Supp 𝒥 = {x | 𝒥_x ≠ 𝒪_x}`, and `mem_Supp_iff_nontrivial_stalk` says this is where the
  stalk of `𝒪/𝒥` is nonzero. Off `Supp`, the stalks are zero (`subsingleton_of_not_mem_Supp`),
  so a section of `𝒪/𝒥` is determined on `Supp` (`Q_ext_of_eqOn_Supp`).
* `identity_principle_quotient_of_ne_infty`, `Jsec_infty_eq_zero`, `Jsec_eq_zero_basic`,
  `identity_principle_quotient_infty`; `identity_principle_quotient`,
  `identity_principle_quotient'`: **(v) for every Ideal of finite type.**
* `lemmeB_counterexample_v`: over `k⟦X⟧ ⊂ k⸨X⸩`, (i), (ii), (iv), and (v) for every coherent
  Ideal hold, and the coherent Ideals `𝒢_j` increase without becoming stationary.

**How.** The quotient is built the way Mathlib builds sheaves of functions: a local predicate
(`TopCat.LocalPredicate`) on functions with values in the stalks `Fib 𝒥 x`, made a sheaf of rings
as `Osheaf` is in `Grothendieck/Folder55Sheaf.lean`. Its stalks are computed by evaluating at the
point (`stalkEval`, a map out of the colimit), which is injective because values determine germs.
The finite type of `𝒥` is used in its sectionwise form, through
`Stacks.SheafOfModules.isFiniteTypeSections_of_isFiniteType'` (Stacks 03DL).

**Not formalised.** `Y` is not built as a ringed space in its own right. Opens of `Y` are the
traces `U ∩ Y` of opens of `X`, and `𝒪_Y(U ∩ Y)` is identified with `(𝒪/𝒥)(U)`: `𝒪/𝒥` is the
direct image of `𝒪_Y`, which `Q_ext_of_eqOn_Supp` and `subsingleton_of_not_mem_Supp` justify.
So (v) is stated on `X`, with `U` an open set of `X` containing `y`. The universal property of
`𝒪/𝒥` as the cokernel of `𝒥 → 𝒪` (equivalently, that it is the sheafification of
`U ↦ 𝒪(U)/𝒥(U)`) is not proved: `𝒪/𝒥` is defined by its sections, and what is proved is that its
stalks are the quotients `𝒪_x/𝒥_x`. Nor is it proved that `Supp 𝒪/𝒥` is closed.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Grothendieck.Folder55LemmaB
open Pt

variable {k D K : Type} [CommRing k] [CommRing D] [CommRing K] (κ : k →+* D) (ε : D →+* k)
  (ι : D →+* K)

/-! ### Values determine germs -/

/-- **A section of `𝒪` vanishing at a point vanishes near it.** -/
theorem O_eq_zero_near {U : Opens Xsp} {s : Sec k D K U} (hs : s ∈ (O κ ε ι).sections U)
    {x : Xsp} (hx : x ∈ U) (h0 : s ⟨x, hx⟩ = 0) :
    ∃ (W : Opens Xsp) (hWU : W ≤ U), x ∈ W ∧ ∀ y : W, s ⟨y.1, hWU y.2⟩ = 0 := by
  obtain ⟨hC, hE, hI⟩ := hs
  cases x with
  | infty =>
    obtain ⟨N, hN⟩ := hI hx
    obtain ⟨M, hM⟩ := exists_basicOpen_le hx
    refine ⟨basicOpen (max N M), le_trans (basic_anti (le_max_right N M)) hM, trivial,
      fun y => ?_⟩
    rw [hN ⟨y.1, _⟩ (inBasic_anti (le_max_left N M) y.1 y.2)]
    change constHom κ ι y.1 (atInf s hx) = 0
    rw [show atInf s hx = 0 from h0, map_zero]
  | c n =>
    refine ⟨cOpen n, cOpen_le hx, c_mem_cOpen n, fun ⟨y, hy⟩ => ?_⟩
    obtain ⟨h1, h2, _⟩ := hC n hx
    have h0' : atC s hx = 0 := h0
    cases y with
    | c m => obtain rfl : m = n := hy; exact h0
    | o m =>
      obtain rfl : m = n := hy
      exact h1.symm.trans (by rw [h0', Prod.fst_zero, map_zero])
    | d m =>
      obtain rfl : m = n := hy
      exact h2.symm.trans (by rw [h0', Prod.snd_zero, map_zero])
    | infty => exact (hy : False).elim
    | e _ => exact (hy : False).elim
  | e n =>
    refine ⟨eoOpen n, eoOpen_le hx, (rfl : n = n), fun ⟨y, hy⟩ => ?_⟩
    have h0' : atE s hx = 0 := h0
    have hEn := hE n hx
    cases y with
    | e m => obtain rfl : m = n := hy; exact h0
    | o m =>
      obtain rfl : m = n := hy
      exact hEn.symm.trans (by rw [h0', map_zero, map_zero])
    | infty => exact (hy : False).elim
    | c _ => exact (hy : False).elim
    | d _ => exact (hy : False).elim
  | o n =>
    refine ⟨oOpen n, oOpen_le hx, o_mem_oOpen n, fun ⟨y, hy⟩ => ?_⟩
    cases y with
    | o m => obtain rfl : m = n := hy; exact h0
    | _ => exact (hy : False).elim
  | d n =>
    refine ⟨dOpen n, dOpen_le hx, d_mem_dOpen n, fun ⟨y, hy⟩ => ?_⟩
    cases y with
    | d m => obtain rfl : m = n := hy; exact h0
    | _ => exact (hy : False).elim

/-! ### The stalks of `𝒪`, as values -/

/-- **The stalk `𝒪_x`**, as the ring of values at `x` of the sections of `𝒪` near `x`
(`stalkEquiv` identifies it with the stalk of `Opre`). -/
def OStalk (x : Xsp) : Subring (Val k D K x) where
  carrier := {v | ∃ (U : Opens Xsp) (h : x ∈ U) (s : Sec k D K U),
    s ∈ (O κ ε ι).sections U ∧ s ⟨x, h⟩ = v}
  one_mem' := ⟨⊤, trivial, 1, O_one_mem κ ε ι ⊤, rfl⟩
  zero_mem' := ⟨⊤, trivial, 0, O_zero_mem κ ε ι ⊤, rfl⟩
  add_mem' := by
    rintro _ _ ⟨U, hU, s, hs, rfl⟩ ⟨V, hV, t, ht, rfl⟩
    exact ⟨U ⊓ V, ⟨hU, hV⟩, _, O_add_mem κ ε ι ((O κ ε ι).restrict inf_le_left hs)
      ((O κ ε ι).restrict inf_le_right ht), rfl⟩
  mul_mem' := by
    rintro _ _ ⟨U, hU, s, hs, rfl⟩ ⟨V, hV, t, ht, rfl⟩
    exact ⟨U ⊓ V, ⟨hU, hV⟩, _, O_mul_mem κ ε ι ((O κ ε ι).restrict inf_le_left hs)
      ((O κ ε ι).restrict inf_le_right ht), rfl⟩
  neg_mem' := by
    rintro _ ⟨U, hU, s, hs, rfl⟩
    exact ⟨U, hU, _, O_neg_mem κ ε ι hs, rfl⟩

/-- The value at `y` of a section of `𝒪`, as an element of the stalk. -/
def toStalk {U : Opens Xsp} {s : Sec k D K U} (hs : s ∈ (O κ ε ι).sections U) (y : U) :
    OStalk κ ε ι y.1 :=
  ⟨s y, U, y.2, s, hs, rfl⟩

/-! ### The sections of an Ideal -/

/-- An Ideal of `𝒪`: a sub-sheaf of modules of `𝒪`. -/
abbrev IdealO := (SheafOfModules.unit (Osheaf κ ε ι)).Submodule

variable {κ ε ι} (𝒥 : IdealO κ ε ι)

/-- The sections of the Ideal `𝒥` over `U`, as functions. -/
def Jsec (U : Opens Xsp) : Set (Sec k D K U) :=
  {s | ∃ a : (Opre κ ε ι).obj (op U), a ∈ 𝒥.obj (op U) ∧ a.1 = s}

theorem Jsec_le_O {U : Opens Xsp} {s : Sec k D K U} (h : s ∈ Jsec 𝒥 U) :
    s ∈ (O κ ε ι).sections U := by
  obtain ⟨a, _, rfl⟩ := h
  exact a.2

theorem Jsec_restrict {U V : Opens Xsp} (hVU : V ≤ U) {s : Sec k D K U} (h : s ∈ Jsec 𝒥 U) :
    (fun y : V => s ⟨y.1, hVU y.2⟩) ∈ Jsec 𝒥 V := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨_, 𝒥.map (homOfLE hVU).op ha, rfl⟩

theorem Jsec_zero (U : Opens Xsp) : (0 : Sec k D K U) ∈ Jsec 𝒥 U :=
  ⟨0, (𝒥.obj (op U)).zero_mem, rfl⟩

theorem Jsec_add {U : Opens Xsp} {s t : Sec k D K U} (hs : s ∈ Jsec 𝒥 U) (ht : t ∈ Jsec 𝒥 U) :
    s + t ∈ Jsec 𝒥 U := by
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb, rfl⟩ := ht
  exact ⟨a + b, (𝒥.obj (op U)).add_mem ha hb, rfl⟩

/-- `𝒥` is an Ideal: stable under multiplication by the sections of `𝒪`. -/
theorem Jsec_mul {U : Opens Xsp} {r s : Sec k D K U} (hr : r ∈ (O κ ε ι).sections U)
    (hs : s ∈ Jsec 𝒥 U) : r * s ∈ Jsec 𝒥 U := by
  obtain ⟨a, ha, rfl⟩ := hs
  exact ⟨_, (𝒥.obj (op U)).smul_mem (⟨r, hr⟩ : (Opre κ ε ι).obj (op U)) ha, rfl⟩

/-! ### The stalks of `𝒥` and of `𝒪/𝒥` -/

/-- **The stalk `𝒥_x`**, an ideal of `𝒪_x`: the values at `x` of the sections of `𝒥` near `x`. -/
def Jst (x : Xsp) : Ideal (OStalk κ ε ι x) where
  carrier := {v | ∃ (U : Opens Xsp) (h : x ∈ U) (s : Sec k D K U), s ∈ Jsec 𝒥 U ∧
    s ⟨x, h⟩ = v.1}
  zero_mem' := ⟨⊤, trivial, 0, Jsec_zero 𝒥 ⊤, rfl⟩
  add_mem' := by
    rintro _ _ ⟨U, hU, s, hs, h1⟩ ⟨V, hV, t, ht, h2⟩
    exact ⟨U ⊓ V, ⟨hU, hV⟩, _, Jsec_add 𝒥 (Jsec_restrict 𝒥 inf_le_left hs)
      (Jsec_restrict 𝒥 inf_le_right ht), by rw [Subring.coe_add, ← h1, ← h2]; rfl⟩
  smul_mem' := by
    rintro ⟨_, U, hU, r, hr, rfl⟩ _ ⟨V, hV, t, ht, h2⟩
    exact ⟨U ⊓ V, ⟨hU, hV⟩, _, Jsec_mul 𝒥 ((O κ ε ι).restrict inf_le_left hr)
      (Jsec_restrict 𝒥 inf_le_right ht), by
        change r ⟨x, hU⟩ * t ⟨x, hV⟩ = _
        rw [h2]; rfl⟩

/-- **The stalk of `𝒪/𝒥` at `x`**: `𝒪_x/𝒥_x`. -/
abbrev Fib (x : Xsp) : Type := OStalk κ ε ι x ⧸ Jst 𝒥 x

/-- The class at `y` of a section of `𝒪`. -/
def cls {U : Opens Xsp} {s : Sec k D K U} (hs : s ∈ (O κ ε ι).sections U) (y : U) :
    Fib 𝒥 y.1 :=
  Ideal.Quotient.mk _ (toStalk κ ε ι hs y)

/-- **The support** `Supp 𝒪/𝒥 = {x | 𝒥_x ≠ 𝒪_x}`. -/
def Supp : Set Xsp := {x | Jst 𝒥 x ≠ ⊤}

theorem mem_Supp {x : Xsp} : x ∈ Supp 𝒥 ↔ Nontrivial (Fib 𝒥 x) :=
  (Ideal.Quotient.nontrivial_iff).symm

/-- Off the support the stalk of `𝒪/𝒥` is zero. -/
theorem subsingleton_of_not_mem_Supp {x : Xsp} (hx : x ∉ Supp 𝒥) : Subsingleton (Fib 𝒥 x) :=
  Ideal.Quotient.subsingleton_iff.2 (not_not.1 hx)

/-! ### The sheaf `𝒪/𝒥` -/

/-- A function with values in the stalks of `𝒪/𝒥` is a section of `𝒪/𝒥` if it is locally the
class of a section of `𝒪`. -/
def IsQ {U : Opens Xsp} (σ : (y : U) → Fib 𝒥 y.1) : Prop :=
  ∀ x : U, ∃ (V : Opens Xsp) (hVU : V ≤ U), x.1 ∈ V ∧ ∃ (s : Sec k D K V)
    (hs : s ∈ (O κ ε ι).sections V), ∀ y : V, σ ⟨y.1, hVU y.2⟩ = cls 𝒥 hs y

theorem isQ_cls {U : Opens Xsp} {s : Sec k D K U} (hs : s ∈ (O κ ε ι).sections U) :
    IsQ 𝒥 (cls 𝒥 hs) :=
  fun x => ⟨U, le_rfl, x.2, s, hs, fun _ => rfl⟩

theorem IsQ.common {U : Opens Xsp} {σ τ : (y : U) → Fib 𝒥 y.1} (hσ : IsQ 𝒥 σ) (hτ : IsQ 𝒥 τ)
    (x : U) : ∃ (V : Opens Xsp) (hVU : V ≤ U), x.1 ∈ V ∧ ∃ (s t : Sec k D K V)
      (hs : s ∈ (O κ ε ι).sections V) (ht : t ∈ (O κ ε ι).sections V),
      ∀ y : V, σ ⟨y.1, hVU y.2⟩ = cls 𝒥 hs y ∧ τ ⟨y.1, hVU y.2⟩ = cls 𝒥 ht y := by
  obtain ⟨V₁, h₁, hx₁, s, hs, hσ'⟩ := hσ x
  obtain ⟨V₂, h₂, hx₂, t, ht, hτ'⟩ := hτ x
  exact ⟨V₁ ⊓ V₂, le_trans inf_le_left h₁, ⟨hx₁, hx₂⟩, _, _,
    (O κ ε ι).restrict inf_le_left hs, (O κ ε ι).restrict inf_le_right ht,
    fun y => ⟨hσ' ⟨y.1, y.2.1⟩, hτ' ⟨y.1, y.2.2⟩⟩⟩

/-- The sections of `𝒪/𝒥` over `U`, a subring of the functions with values in the stalks. -/
def Qsubring (U : Opens Xsp) : Subring ((y : U) → Fib 𝒥 y.1) where
  carrier := {σ | IsQ 𝒥 σ}
  one_mem' := fun x => ⟨U, le_rfl, x.2, 1, O_one_mem κ ε ι U, fun _ =>
    (map_one (Ideal.Quotient.mk _)).symm⟩
  zero_mem' := fun x => ⟨U, le_rfl, x.2, 0, O_zero_mem κ ε ι U, fun y =>
    (map_zero (Ideal.Quotient.mk (Jst 𝒥 y.1))).symm⟩
  add_mem' := by
    intro σ τ hσ hτ x
    obtain ⟨V, hVU, hx, s, t, hs, ht, h⟩ := IsQ.common 𝒥 hσ hτ x
    refine ⟨V, hVU, hx, s + t, O_add_mem κ ε ι hs ht, fun y => ?_⟩
    change σ _ + τ _ = _
    rw [(h y).1, (h y).2]
    exact (map_add (Ideal.Quotient.mk _) _ _).symm
  mul_mem' := by
    intro σ τ hσ hτ x
    obtain ⟨V, hVU, hx, s, t, hs, ht, h⟩ := IsQ.common 𝒥 hσ hτ x
    refine ⟨V, hVU, hx, s * t, O_mul_mem κ ε ι hs ht, fun y => ?_⟩
    change σ _ * τ _ = _
    rw [(h y).1, (h y).2]
    exact (map_mul (Ideal.Quotient.mk _) _ _).symm
  neg_mem' := by
    intro σ hσ x
    obtain ⟨V, hVU, hx, s, hs, h⟩ := hσ x
    refine ⟨V, hVU, hx, -s, O_neg_mem κ ε ι hs, fun y => ?_⟩
    change -σ _ = _
    rw [h y]
    exact (map_neg (Ideal.Quotient.mk _) _).symm

/-- `𝒪/𝒥` as a local predicate on functions with values in the stalks. -/
def Qlp : TopCat.LocalPredicate (fun x : Xsp => Fib 𝒥 x) where
  pred {U} σ := IsQ 𝒥 σ
  res {U V} i σ h x := by
    obtain ⟨W, hWV, hx, s, hs, hrep⟩ := h ⟨x.1, i.le x.2⟩
    exact ⟨W ⊓ U, inf_le_right, ⟨hx, x.2⟩, _, (O κ ε ι).restrict inf_le_left hs,
      fun y => hrep ⟨y.1, y.2.1⟩⟩
  locality {U} σ h x := by
    obtain ⟨V, hxV, i, hV⟩ := h x
    obtain ⟨W, hWV, hx, s, hs, hrep⟩ := hV ⟨x.1, hxV⟩
    exact ⟨W, le_trans hWV i.le, hx, s, hs, hrep⟩

/-- **The sheaf `𝒪/𝒥`, as a presheaf of rings.** -/
def Qpre : TopCat.Presheaf RingCat Xsp where
  obj U := RingCat.of (Qsubring 𝒥 U.unop)
  map i := RingCat.ofHom
    { toFun := fun σ => ⟨fun x => σ.1 ⟨x.1, i.unop.le x.2⟩,
        (Qlp 𝒥).res i.unop σ.1 (show IsQ 𝒥 σ.1 from σ.2)⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

theorem Qpre_isSheaf : (Qpre 𝒥).IsSheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget RingCat) _).2 ?_
  refine TopCat.Presheaf.isSheaf_of_iso ?_ (TopCat.subpresheafToTypes.isSheaf (Qlp 𝒥))
  exact NatIso.ofComponents (fun U => Iso.refl _) (fun _ => rfl)

/-- **The sheaf of rings `𝒪/𝒥`.** -/
def Qsheaf : Sheaf (Opens.grothendieckTopology Xsp) RingCat := ⟨Qpre 𝒥, Qpre_isSheaf 𝒥⟩

/-- **The quotient map `𝒪 → 𝒪/𝒥`.** -/
def quotMap : Opre κ ε ι ⟶ Qpre 𝒥 where
  app _ := RingCat.ofHom
    { toFun := fun a => ⟨cls 𝒥 a.2, show IsQ 𝒥 _ from isQ_cls 𝒥 a.2⟩
      map_one' := Subtype.ext (funext fun y => map_one (Ideal.Quotient.mk (Jst 𝒥 y.1)))
      map_mul' a b := Subtype.ext (funext fun y =>
        map_mul (Ideal.Quotient.mk (Jst 𝒥 y.1)) (toStalk κ ε ι a.2 y) (toStalk κ ε ι b.2 y))
      map_zero' := Subtype.ext (funext fun y => map_zero (Ideal.Quotient.mk (Jst 𝒥 y.1)))
      map_add' a b := Subtype.ext (funext fun y =>
        map_add (Ideal.Quotient.mk (Jst 𝒥 y.1)) (toStalk κ ε ι a.2 y) (toStalk κ ε ι b.2 y)) }
  naturality _ _ _ := rfl

/-- The sections of `𝒪/𝒥` are determined on the support: `𝒪/𝒥` is `𝒪_Y` pushed forward from
`Y = Supp 𝒪/𝒥`. -/
theorem Q_ext_of_eqOn_Supp {U : Opens Xsp} {σ τ : (Qpre 𝒥).obj (op U)}
    (h : ∀ x : U, x.1 ∈ Supp 𝒥 → σ.1 x = τ.1 x) : σ = τ := by
  refine Subtype.ext (funext fun x => ?_)
  by_cases hx : x.1 ∈ Supp 𝒥
  · exact h x hx
  · have := subsingleton_of_not_mem_Supp 𝒥 hx
    exact Subsingleton.elim _ _

theorem quotient_mk_injective_of_eq_bot {R : Type} [CommRing R] {I : Ideal R} (hI : I = ⊥) :
    Function.Injective (Ideal.Quotient.mk I) := by
  intro a b h
  rw [Ideal.Quotient.eq, hI, Ideal.mem_bot] at h
  exact sub_eq_zero.1 h

/-! ### Stalks as values -/

section StalkEval

variable {F : TopCat.Presheaf RingCat Xsp} {x : Xsp} {A : Type} [CommRing A]
  (ev : ∀ (U : Opens Xsp), x ∈ U → F.obj (op U) →+* A)
  (hnat : ∀ {U V : Opens Xsp} (i : V ⟶ U) (hx : x ∈ V) (s : F.obj (op U)),
    ev V hx (F.map i.op s) = ev U (i.le hx) s)

/-- A family of evaluations at `x`, compatible with restriction, induces a map on the stalk. -/
noncomputable def stalkEval : F.stalk x ⟶ RingCat.of A :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ F)
    { pt := RingCat.of A
      ι :=
        { app := fun U => RingCat.ofHom (ev U.unop.1 U.unop.2)
          naturality := fun U V i => by
            ext s
            exact hnat ((OpenNhds.inclusion x).map i.unop) V.unop.2 s } }

theorem stalkEval_germ (U : Opens Xsp) (hx : x ∈ U) (s : F.obj (op U)) :
    stalkEval ev hnat (F.germ U x hx s) = ev U hx s := by
  change (F.germ U x hx ≫ stalkEval ev hnat) s = _
  erw [colimit.ι_desc]
  rfl

/-- If values at `x` determine germs, evaluation is injective on the stalk. -/
theorem stalkEval_injective
    (hval : ∀ (U : Opens Xsp) (hx : x ∈ U) (s : F.obj (op U)), ev U hx s = 0 →
      ∃ (W : Opens Xsp) (i : W ⟶ U), x ∈ W ∧ F.map i.op s = 0) :
    Function.Injective (stalkEval ev hnat) := by
  refine (injective_iff_map_eq_zero (stalkEval ev hnat).hom).2 fun g hg => ?_
  obtain ⟨U, hx, s, rfl⟩ := F.exists_germ_eq g
  rw [stalkEval_germ] at hg
  obtain ⟨W, i, hxW, hW⟩ := hval U hx s hg
  rw [← F.germ_res_apply i x hxW s, hW, map_zero]

end StalkEval

section Stalks

variable (κ ε ι)

theorem evalAt_nat {x : Xsp} {U V : Opens Xsp} (i : V ⟶ U) (hx : x ∈ V)
    (s : (Opre κ ε ι).obj (op U)) :
    evalAt κ ε ι V hx ((Opre κ ε ι).map i.op s) = evalAt κ ε ι U (i.le hx) s := rfl

/-- Evaluation at `x` on the stalk of `𝒪`. -/
noncomputable def stalkEvalO (x : Xsp) : (Opre κ ε ι).stalk x ⟶ RingCat.of (Val k D K x) :=
  stalkEval (fun U hx => evalAt κ ε ι U hx) (evalAt_nat κ ε ι)

theorem stalkEvalO_injective (x : Xsp) : Function.Injective (stalkEvalO κ ε ι x) := by
  refine stalkEval_injective _ _ fun U hx s hs => ?_
  obtain ⟨W, hWU, hxW, h0⟩ := O_eq_zero_near κ ε ι s.2 hx hs
  exact ⟨W, homOfLE hWU, hxW, Subtype.ext (funext h0)⟩

theorem stalkEvalO_germ {x : Xsp} {U : Opens Xsp} (hx : x ∈ U) (a : (Opre κ ε ι).obj (op U)) :
    stalkEvalO κ ε ι x ((Opre κ ε ι).germ U x hx a) = a.1 ⟨x, hx⟩ :=
  stalkEval_germ _ _ U hx a

theorem stalkEvalO_mem (x : Xsp) (g : (Opre κ ε ι).stalk x) :
    stalkEvalO κ ε ι x g ∈ OStalk κ ε ι x := by
  obtain ⟨U, hx, s, rfl⟩ := (Opre κ ε ι).exists_germ_eq g
  rw [stalkEvalO_germ]
  exact ⟨U, hx, s.1, s.2, rfl⟩

/-- **The stalk of `𝒪` at `x` is `OStalk x`**, the ring of values at `x` of the sections near
`x`. -/
noncomputable def stalkEquivO (x : Xsp) : (Opre κ ε ι).stalk x ≃+* OStalk κ ε ι x :=
  RingEquiv.ofBijective ((stalkEvalO κ ε ι x).hom.codRestrict _ (stalkEvalO_mem κ ε ι x))
    ⟨fun _ _ h => stalkEvalO_injective κ ε ι x (congrArg Subtype.val h), by
      rintro ⟨_, U, hx, s, hs, rfl⟩
      exact ⟨(Opre κ ε ι).germ U x hx (⟨s, hs⟩ : (Opre κ ε ι).obj (op U)),
        Subtype.ext (stalkEvalO_germ κ ε ι hx _)⟩⟩

theorem stalkEquivO_germ {x : Xsp} {U : Opens Xsp} (hx : x ∈ U) (s : (Opre κ ε ι).obj (op U)) :
    (stalkEquivO κ ε ι x ((Opre κ ε ι).germ U x hx s)).1 = s.1 ⟨x, hx⟩ :=
  stalkEvalO_germ κ ε ι hx s

variable {κ ε ι} in
/-- **The stalk `𝒥_x` in Mathlib's stalk `𝒪_x`**: the germs of the sections of `𝒥`. -/
noncomputable def Jgerm (x : Xsp) : Ideal ((Opre κ ε ι).stalk x) :=
  (Jst 𝒥 x).comap (stalkEquivO κ ε ι x)

variable {κ ε ι} in
instance (x : Xsp) : (Jgerm 𝒥 x).IsTwoSided :=
  inferInstanceAs ((Jst 𝒥 x).comap (stalkEquivO κ ε ι x)).IsTwoSided

variable {κ ε ι} in
theorem mem_Jgerm {x : Xsp} {g : (Opre κ ε ι).stalk x} :
    g ∈ Jgerm 𝒥 x ↔ ∃ (U : Opens Xsp) (hx : x ∈ U) (a : (Opre κ ε ι).obj (op U)),
      a ∈ 𝒥.obj (op U) ∧ (Opre κ ε ι).germ U x hx a = g := by
  rw [Jgerm, Ideal.mem_comap]
  constructor
  · rintro ⟨U, hx, _, ⟨a, ha, rfl⟩, hv⟩
    refine ⟨U, hx, a, ha, (stalkEquivO κ ε ι x).injective (Subtype.ext ?_)⟩
    rw [stalkEquivO_germ]
    exact hv
  · rintro ⟨U, hx, a, ha, rfl⟩
    exact ⟨U, hx, a.1, ⟨a, ha, rfl⟩, (stalkEquivO_germ κ ε ι hx a).symm⟩

variable {κ ε ι} in
/-- **`Fib x` is `𝒪_x/𝒥_x`**, with Mathlib's stalk `𝒪_x` and the ideal of germs of `𝒥`. -/
noncomputable def fibEquiv (x : Xsp) : Fib 𝒥 x ≃+* (Opre κ ε ι).stalk x ⧸ Jgerm 𝒥 x :=
  (Ideal.quotientEquiv (Jgerm 𝒥 x) (Jst 𝒥 x) (stalkEquivO κ ε ι x)
    (Ideal.map_comap_of_surjective _ (stalkEquivO κ ε ι x).surjective _).symm).symm

variable {κ ε ι}

/-- Evaluation at `x` of the sections of `𝒪/𝒥`. -/
def evQ {x : Xsp} (U : Opens Xsp) (hx : x ∈ U) : (Qpre 𝒥).obj (op U) →+* Fib 𝒥 x where
  toFun σ := σ.1 ⟨x, hx⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evQ_nat {x : Xsp} {U V : Opens Xsp} (i : V ⟶ U) (hx : x ∈ V)
    (σ : (Qpre 𝒥).obj (op U)) : evQ 𝒥 V hx ((Qpre 𝒥).map i.op σ) = evQ 𝒥 U (i.le hx) σ := rfl

/-- Evaluation at `x` on the stalk of `𝒪/𝒥`. -/
noncomputable def stalkEvalQ (x : Xsp) : (Qpre 𝒥).stalk x ⟶ RingCat.of (Fib 𝒥 x) :=
  stalkEval (x := x) (evQ 𝒥) (evQ_nat 𝒥)

theorem stalkEvalQ_germ {x : Xsp} {U : Opens Xsp} (hx : x ∈ U) (σ : (Qpre 𝒥).obj (op U)) :
    stalkEvalQ 𝒥 x ((Qpre 𝒥).germ U x hx σ) = σ.1 ⟨x, hx⟩ :=
  stalkEval_germ (x := x) (evQ 𝒥) (evQ_nat 𝒥) U hx σ

/-- A section of `𝒪/𝒥` vanishing at `x` vanishes near `x`. -/
theorem Q_eq_zero_near {U : Opens Xsp} (σ : (Qpre 𝒥).obj (op U)) {x : Xsp} (hx : x ∈ U)
    (h0 : σ.1 ⟨x, hx⟩ = 0) :
    ∃ (W : Opens Xsp) (hWU : W ≤ U), x ∈ W ∧ ∀ y : W, σ.1 ⟨y.1, hWU y.2⟩ = 0 := by
  obtain ⟨V, hVU, hxV, s, hs, hrep⟩ := (show IsQ 𝒥 σ.1 from σ.2) ⟨x, hx⟩
  rw [hrep ⟨x, hxV⟩] at h0
  have hm : toStalk κ ε ι hs ⟨x, hxV⟩ ∈ Jst 𝒥 x := Ideal.Quotient.eq_zero_iff_mem.1 h0
  obtain ⟨U', hU', j, hj, hjx⟩ := hm
  have hd : (fun y : ↥(V ⊓ U') => s ⟨y.1, y.2.1⟩ + -j ⟨y.1, y.2.2⟩) ∈
      (O κ ε ι).sections (V ⊓ U') :=
    O_add_mem κ ε ι ((O κ ε ι).restrict inf_le_left hs)
      (O_neg_mem κ ε ι ((O κ ε ι).restrict inf_le_right (Jsec_le_O 𝒥 hj)))
  obtain ⟨W, hW, hxW, hz⟩ := O_eq_zero_near κ ε ι hd ⟨hxV, hU'⟩
    (show s ⟨x, hxV⟩ + -j ⟨x, hU'⟩ = 0 by rw [hjx]; exact add_neg_cancel _)
  refine ⟨W, le_trans hW (le_trans inf_le_left hVU), hxW, fun y => ?_⟩
  rw [hrep ⟨y.1, (hW y.2).1⟩]
  refine Ideal.Quotient.eq_zero_iff_mem.2 ⟨U', (hW y.2).2, j, hj, ?_⟩
  exact (add_neg_eq_zero.1 (hz y)).symm

/-- **The stalk of `𝒪/𝒥` at `x` is `Fib x = 𝒪_x/𝒥_x`.** -/
noncomputable def stalkEquivQ (x : Xsp) : (Qpre 𝒥).stalk x ≃+* Fib 𝒥 x :=
  RingEquiv.ofBijective (stalkEvalQ 𝒥 x).hom
    ⟨stalkEval_injective (x := x) (evQ 𝒥) (evQ_nat 𝒥) fun U hx σ h0 => by
      obtain ⟨W, hWU, hxW, hz⟩ := Q_eq_zero_near 𝒥 σ hx h0
      exact ⟨W, homOfLE hWU, hxW, Subtype.ext (funext hz)⟩, by
      intro v
      obtain ⟨⟨_, U, hx, s, hs, rfl⟩, rfl⟩ := Ideal.Quotient.mk_surjective v
      exact ⟨(Qpre 𝒥).germ U x hx ⟨cls 𝒥 hs, isQ_cls 𝒥 hs⟩,
        stalkEvalQ_germ 𝒥 hx ⟨cls 𝒥 hs, isQ_cls 𝒥 hs⟩⟩⟩

/-- **The stalks of `𝒪/𝒥` are the quotients `𝒪_x/𝒥_x` of the stalks of `𝒪`.** -/
@[montpellier "55, 13"]
noncomputable def stalkQuotientEquiv (x : Xsp) :
    (Qpre 𝒥).stalk x ≃+* (Opre κ ε ι).stalk x ⧸ Jgerm 𝒥 x :=
  (stalkEquivQ 𝒥 x).trans (fibEquiv 𝒥 x)

/-- `x ∈ Supp 𝒪/𝒥` if and only if the stalk of the sheaf `𝒪/𝒥` at `x` is not zero. -/
theorem mem_Supp_iff_nontrivial_stalk {x : Xsp} :
    x ∈ Supp 𝒥 ↔ Nontrivial ((Qpre 𝒥).stalk x) := by
  rw [mem_Supp]
  exact ⟨fun _ => (stalkEquivQ 𝒥 x).symm.injective.nontrivial,
    fun _ => (stalkEquivQ 𝒥 x).injective.nontrivial⟩

end Stalks

/-! ### Points with a smallest neighbourhood -/

/-- Every point but `infty` has a smallest open neighbourhood. -/
theorem exists_smallest_nbhd {y : Xsp} (hy : y ≠ infty) :
    ∃ U : Opens Xsp, y ∈ U ∧ ∀ W : Opens Xsp, y ∈ W → U ≤ W := by
  cases y with
  | infty => exact (hy rfl).elim
  | c n => exact ⟨cOpen n, c_mem_cOpen n, fun _ h => cOpen_le h⟩
  | e n => exact ⟨eoOpen n, (rfl : n = n), fun _ h => eoOpen_le h⟩
  | o n => exact ⟨oOpen n, o_mem_oOpen n, fun _ h => oOpen_le h⟩
  | d n => exact ⟨dOpen n, d_mem_dOpen n, fun _ h => dOpen_le h⟩

/-- **(v) at a point with a smallest neighbourhood `U`**, for any Ideal: a section of `𝒪/𝒥`
over `U` vanishing near `y` vanishes on `U`. -/
theorem identity_principle_quotient_of_ne_infty {y : Xsp} (hy : y ≠ infty) :
    ∃ U : Opens Xsp, y ∈ U ∧ ∀ σ : (Qpre 𝒥).obj (op U),
      (∃ W : Opens Xsp, y ∈ W ∧ ∀ x : U, x.1 ∈ W → σ.1 x = 0) → σ = 0 := by
  obtain ⟨U, hyU, hU⟩ := exists_smallest_nbhd hy
  refine ⟨U, hyU, fun σ ⟨W, hyW, h0⟩ => Subtype.ext (funext fun x => ?_)⟩
  exact h0 x (hU W hyW x.2)

/-! ### The point `infty` -/

section Infty

variable {k D K : Type} [Field k] [CommRing D] [CommRing K] {κ : k →+* D} {ε : D →+* k}
  {ι : D →+* K} (𝒥 : IdealO κ ε ι)

/-- If `infty` lies in the support, the sections of `𝒥` vanish at `infty`: `𝒥_infty` is a
proper ideal of the field `k`, hence `0`. -/
theorem Jsec_infty_eq_zero (hy : (infty : Xsp) ∈ Supp 𝒥) {U : Opens Xsp}
    (h : (infty : Xsp) ∈ U) {s : Sec k D K U} (hs : s ∈ Jsec 𝒥 U) : s ⟨infty, h⟩ = 0 := by
  by_contra ha
  apply hy
  refine (Ideal.eq_top_iff_one _).2 ⟨U, h, _, Jsec_mul 𝒥 (constSec κ ε ι U (s ⟨infty, h⟩)⁻¹).2 hs,
    ?_⟩
  change (s ⟨infty, h⟩)⁻¹ * s ⟨infty, h⟩ = 1
  exact inv_mul_cancel₀ ha

/-- **An Ideal of finite type whose sections vanish at `infty` is `0` on some `B_M`.** Its
finitely many local generators near `infty` vanish at `infty`, hence on some `B_M`. -/
theorem Jsec_eq_zero_basic (hft : 𝒥.toSheafOfModules.IsFiniteType)
    (h0 : ∀ {U : Opens Xsp} (h : (infty : Xsp) ∈ U) {s : Sec k D K U}, s ∈ Jsec 𝒥 U →
      s ⟨infty, h⟩ = 0) :
    ∃ M, ∀ (V : Opens Xsp), V ≤ basicOpen M → ∀ s ∈ Jsec 𝒥 V, s = 0 := by
  obtain ⟨I, U, hcov, hgen⟩ :=
    (Stacks.SheafOfModules.isFiniteTypeSections_of_isFiniteType' _ hft).exists_generators
  have hcov' := hcov ⊤
  rw [Opens.mem_grothendieckTopology] at hcov'
  obtain ⟨V₀, g₀, ⟨i, ⟨g⟩⟩, hV₀⟩ := hcov' infty trivial
  have hi : (infty : Xsp) ∈ U i := g.le hV₀
  obtain ⟨n, gens, hgens⟩ := hgen i
  have hz : ∀ l, ∃ N, basicOpen N ≤ U i ∧ ∀ y : U i, InBasic N y.1 →
      (gens l).1.1 y = 0 := fun l => by
    obtain ⟨W, hWU, hW, hz⟩ := O_eq_zero_near κ ε ι (gens l).1.2 hi
      (h0 hi ⟨(gens l).1, (gens l).2, rfl⟩)
    obtain ⟨N, hN⟩ := exists_basicOpen_le hW
    exact ⟨N, le_trans hN hWU, fun y hy => hz ⟨y.1, hN hy⟩⟩
  choose N hNU hN using hz
  obtain ⟨N₀, hN₀⟩ := exists_basicOpen_le hi
  refine ⟨max N₀ (Finset.univ.sup N), fun V hV s hs => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hs
  have hVU : V ≤ U i := le_trans hV (le_trans (basic_anti (le_max_left _ _)) hN₀)
  obtain ⟨S, hS, hSgen⟩ := hgens V (homOfLE hVU)
    (⟨a, ha⟩ : 𝒥.toSheafOfModules.val.obj (op V))
  funext y
  rw [Opens.mem_grothendieckTopology] at hS
  obtain ⟨W, f, hf, hyW⟩ := hS y.1 y.2
  obtain ⟨c, hc⟩ := hSgen W f hf
  let φ : 𝒥.toSheafOfModules.val.obj (op W) →+ Val k D K y.1 :=
    { toFun := fun m => m.1.1 ⟨y.1, hyW⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have key := congrArg φ hc
  rw [map_sum] at key
  refine key.symm.trans (Finset.sum_eq_zero fun l _ => ?_)
  change (c l).1 ⟨y.1, hyW⟩ * (gens l).1.1 ⟨y.1, hVU (f.le hyW)⟩ = 0
  have hyB : InBasic (N l) y.1 := inBasic_anti (le_trans (Finset.le_sup (Finset.mem_univ l))
    (le_max_right _ _)) y.1 (hV y.2)
  rw [hN l _ hyB, mul_zero]

/-- Where `𝒥` is `0`, its stalks are `0`. -/
theorem Jst_eq_bot_of_basic {M : ℕ} (hM : ∀ (V : Opens Xsp), V ≤ basicOpen M →
    ∀ s ∈ Jsec 𝒥 V, s = 0) {x : Xsp} (hx : x ∈ basicOpen M) : Jst 𝒥 x = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 ?_
  rintro v ⟨U, hU, s, hs, hv⟩
  have h := hM (U ⊓ basicOpen M) inf_le_right _ (Jsec_restrict 𝒥 inf_le_left hs)
  apply Subtype.ext
  rw [← hv]
  exact congrFun h ⟨x, ⟨hU, hx⟩⟩

variable (hεκ : ∀ a, ε (κ a) = a) (hι : Function.Injective ι)
include hεκ hι

/-- **(v) at `infty`, for an Ideal of finite type.** If `infty ∈ Supp 𝒪/𝒥`, then `𝒥 = 0` on some
`B_M` (`Jsec_infty_eq_zero`, `Jsec_eq_zero_basic`), so `𝒪/𝒥 = 𝒪` there, and a section of `𝒪/𝒥`
over `B_M` vanishing near `infty` lifts to a section of `𝒪` vanishing near `infty`, which
vanishes on `B_M` (`identity_principle`). -/
theorem identity_principle_quotient_infty (hft : 𝒥.toSheafOfModules.IsFiniteType)
    (hy : (infty : Xsp) ∈ Supp 𝒥) :
    ∃ U : Opens Xsp, (infty : Xsp) ∈ U ∧ ∀ σ : (Qpre 𝒥).obj (op U),
      (∃ W : Opens Xsp, (infty : Xsp) ∈ W ∧ ∀ x : U, x.1 ∈ W → σ.1 x = 0) → σ = 0 := by
  obtain ⟨M, hM⟩ := Jsec_eq_zero_basic 𝒥 hft (fun h _ hs => Jsec_infty_eq_zero 𝒥 hy h hs)
  have hinj : ∀ (x : basicOpen M) {p q : OStalk κ ε ι x.1},
      Ideal.Quotient.mk (Jst 𝒥 x.1) p = Ideal.Quotient.mk _ q → p.1 = q.1 := fun x _ _ h =>
    congrArg Subtype.val (quotient_mk_injective_of_eq_bot (Jst_eq_bot_of_basic 𝒥 hM x.2) h)
  refine ⟨basicOpen M, trivial, fun σ ⟨W, hW, h0⟩ => ?_⟩
  have hσ : IsQ 𝒥 σ.1 := σ.2
  choose V hVU hxV s hs hrep using hσ
  let f : Sec k D K (basicOpen M) := fun x => s x ⟨x.1, hxV x⟩
  have hf : ∀ (x : basicOpen M) (z : V x), f ⟨z.1, hVU x z.2⟩ = s x z := fun x z =>
    hinj ⟨z.1, hVU x z.2⟩ ((hrep ⟨z.1, hVU x z.2⟩ ⟨z.1, hxV ⟨z.1, hVU x z.2⟩⟩).symm.trans
      (hrep x z))
  have hfO : f ∈ (O κ ε ι).sections (basicOpen M) :=
    (O κ ε ι).isLocal _ f fun x hx => ⟨V ⟨x, hx⟩, hVU _, hxV _, by
      have he : (fun z : V ⟨x, hx⟩ => f ⟨z.1, hVU ⟨x, hx⟩ z.2⟩) = s ⟨x, hx⟩ :=
        funext fun z => hf ⟨x, hx⟩ z
      change (fun z : V ⟨x, hx⟩ => f ⟨z.1, hVU ⟨x, hx⟩ z.2⟩) ∈ (O κ ε ι).sections _
      rw [he]
      exact hs ⟨x, hx⟩⟩
  have hf0 : f = 0 := identity_principle κ ε ι hεκ hι M hfO (W := W ⊓ basicOpen M) ⟨hW, trivial⟩
    inf_le_right fun z => hinj (q := 0) ⟨z.1, z.2.2⟩
      ((hrep ⟨z.1, z.2.2⟩ ⟨z.1, hxV ⟨z.1, z.2.2⟩⟩).symm.trans
      ((h0 ⟨z.1, z.2.2⟩ z.2.1).trans (map_zero _).symm))
  refine Subtype.ext (funext fun x => (hrep x ⟨x.1, hxV x⟩).trans ?_)
  have h1 : toStalk κ ε ι (hs x) ⟨x.1, hxV x⟩ = 0 := Subtype.ext (congrFun hf0 x)
  change Ideal.Quotient.mk _ (toStalk κ ε ι (hs x) ⟨x.1, hxV x⟩) = 0
  rw [h1, map_zero]

/-- **Condition (v) of Lemme B, for every Ideal of finite type `𝒥`.** Every point `y` of
`Y = Supp 𝒪/𝒥` has an open neighbourhood `U` on which a section of `𝒪_Y = 𝒪/𝒥` vanishing near `y`
vanishes; the hypothesis of (v) that `𝒪_{Y,y}` be a domain is not needed. -/
@[montpellier "55, 13"]
theorem identity_principle_quotient (hft : 𝒥.toSheafOfModules.IsFiniteType) {y : Xsp}
    (hy : y ∈ Supp 𝒥) :
    ∃ U : Opens Xsp, y ∈ U ∧ ∀ σ : (Qpre 𝒥).obj (op U),
      (∃ W : Opens Xsp, y ∈ W ∧ ∀ x : U, x.1 ∈ W → σ.1 x = 0) → σ = 0 := by
  by_cases h : y = infty
  · subst h
    exact identity_principle_quotient_infty 𝒥 hεκ hι hft hy
  · exact identity_principle_quotient_of_ne_infty 𝒥 h

/-- **Condition (v) of Lemme B, in the language of sheaves**, for every Ideal of finite type
`𝒥`: at every point `y` where the stalk of `𝒪_Y = 𝒪/𝒥` is a domain (in particular `y ∈ Y`),
there is an open neighbourhood `U` of `y` such that a section of `𝒪/𝒥` over `U` whose
restriction to some open neighbourhood of `y` is `0` is `0`. -/
@[montpellier "55, 13"]
theorem identity_principle_quotient' (hft : 𝒥.toSheafOfModules.IsFiniteType) {y : Xsp}
    (hy : IsDomain ((Qpre 𝒥).stalk y)) :
    ∃ U : Opens Xsp, y ∈ U ∧ ∀ σ : (Qpre 𝒥).obj (op U),
      (∃ (W : Opens Xsp) (hWU : W ≤ U), y ∈ W ∧ (Qpre 𝒥).map (homOfLE hWU).op σ = 0) →
        σ = 0 := by
  obtain ⟨U, hyU, hU⟩ := identity_principle_quotient 𝒥 hεκ hι hft
    ((mem_Supp_iff_nontrivial_stalk 𝒥 (x := y)).2 inferInstance)
  refine ⟨U, hyU, fun σ ⟨W, hWU, hyW, h0⟩ => hU σ ⟨W, hyW, fun x hxW => ?_⟩⟩
  exact congrArg (fun τ : (Qpre 𝒥).obj (op W) => τ.1 ⟨x.1, hxW⟩) h0

end Infty

/-! ### The counterexample, with (v) for every coherent Ideal -/

section PowerSeries

variable (k : Type) [Field k]

/-- **Lemme B of folder 55, page 13, is false as stated.** With `k` a field, `D = k⟦X⟧`,
`K = k⸨X⸩`: the space `Xsp` is quasi-compact (i), `𝒪` is coherent (ii) with noetherian stalks
(iv), and (v) holds for every coherent Ideal `𝒥`: at every point `y` of `Y = Supp 𝒪/𝒥` where
`𝒪_{Y,y}` is a domain, some open neighbourhood `U` of `y` has the property that a section of
`𝒪/𝒥` over `U` vanishing near `y` vanishes. Yet the coherent Ideals `𝒢_j` of `𝒪` form an
increasing sequence which is not stationary. -/
@[montpellier "55, 13"]
theorem lemmeB_counterexample_v :
    CompactSpace Xsp ∧
      Stacks.SheafOfModules.IsCoherent (SheafOfModules.unit (Osheaf (κ₀ k) (ε₀ k) (ι₀ k))) ∧
      (∀ x : Xsp, IsNoetherianRing ((Opre (κ₀ k) (ε₀ k) (ι₀ k)).stalk x)) ∧
      (∀ 𝒥 : IdealO (κ₀ k) (ε₀ k) (ι₀ k), Stacks.SheafOfModules.IsCoherent 𝒥.toSheafOfModules →
        ∀ y : Xsp, Nontrivial ((Qpre 𝒥).stalk y) → IsDomain ((Qpre 𝒥).stalk y) →
          ∃ U : Opens Xsp, y ∈ U ∧ ∀ σ : (Qpre 𝒥).obj (op U),
            (∃ (W : Opens Xsp) (hWU : W ≤ U), y ∈ W ∧ (Qpre 𝒥).map (homOfLE hWU).op σ = 0) →
              σ = 0) ∧
      (∀ j, Stacks.SheafOfModules.IsCoherent (Gmod (κ₀ k) (ε₀ k) (ι₀ k) j)) ∧
      Monotone (G (κ₀ k) (ε₀ k) (ι₀ k)) ∧
      ¬ ∃ j₀, ∀ j ≥ j₀, G (κ₀ k) (ε₀ k) (ι₀ k) j = G (κ₀ k) (ε₀ k) (ι₀ k) j₀ := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ := lemmeB_counterexample k
  exact ⟨h1, h2, h3, fun 𝒥 h𝒥 _ _ hd =>
    identity_principle_quotient' 𝒥 (ε₀_κ₀ k) (ι₀_injective k) h𝒥.isFiniteType hd, h4, h6, h7⟩

end PowerSeries

end Grothendieck.Folder55LemmaB
