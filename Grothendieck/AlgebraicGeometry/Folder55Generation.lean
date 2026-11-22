module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSiteSections
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Local generation on the slice site of a topological space, checked point by point

On the site `Opens X` sliced over `U`, local generation of a presheaf of modules by a finite
family (`Stacks.SheafOfModules.GeneratesLocally`) and finite type in the sectionwise sense
(`Stacks.SheafOfModules.IsFiniteTypeSections`) can be checked at each point: these are the
forms used for the coherence of the structure sheaf in
`Grothendieck/AlgebraicGeometry/Folder55Coherent.lean`.
-/

open CategoryTheory TopologicalSpace Opposite Stacks.SheafOfModules

namespace Grothendieck.Folder55Generation

variable {X : TopCat.{0}} {R : (Opens X)ᵒᵖ ⥤ RingCat.{0}} {U : Opens X}

/-- **Local generation, point by point.** A finite family of sections over `U'` generates a
presheaf of modules on `Opens X` sliced over `U` if, for every section `t` over `V → U'` and every
point `x ∈ V`, `t` is a linear combination of the family on some `W → V` containing `x`. -/
theorem generatesLocally_of_forall_mem (M : PresheafOfModules.{0} ((Over.forget U).op ⋙ R))
    {U' : Over U} {ι : Type} [Fintype ι] (s : ι → M.obj (op U'))
    (h : ∀ (V : Over U) (f : V ⟶ U') (t : M.obj (op V)) (x : X), x ∈ V.left →
      ∃ (W : Over U) (g : W ⟶ V), x ∈ W.left ∧
        ∃ a : ι → ((Over.forget U).op ⋙ R).obj (op W),
          ∑ i, a i • M.restrictₛₗ (g ≫ f).op (s i) = M.restrictₛₗ g.op t) :
    GeneratesLocally ((Opens.grothendieckTopology X).over U) M s := by
  intro V f t
  let S : Sieve V :=
    { arrows := fun W g => ∃ a : ι → ((Over.forget U).op ⋙ R).obj (op W),
        ∑ i, a i • M.restrictₛₗ (g ≫ f).op (s i) = M.restrictₛₗ g.op t
      downward_closed := by
        rintro W W' g ⟨a, ha⟩ e
        refine ⟨fun i => ((Over.forget U).op ⋙ R).map e.op (a i), ?_⟩
        have key : ∀ {A B : Over U} (e : W' ⟶ A) (g : A ⟶ B) (m : M.obj (op B)),
            M.restrictₛₗ e.op (M.restrictₛₗ g.op m) = M.restrictₛₗ (e ≫ g).op m :=
          fun e g m => (M.map_comp_apply g.op e.op m).symm
        have := congrArg (M.restrictₛₗ e.op) ha
        rw [map_sum] at this
        simp only [map_smulₛₗ, key] at this
        rw [Category.assoc]
        exact this }
  refine ⟨S, ?_, fun W g hg => hg⟩
  rw [GrothendieckTopology.mem_over_iff, Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨W, g, hxW, a, ha⟩ := h V f t x hx
  refine ⟨W.left, g.left, ?_, hxW⟩
  rw [Sieve.overEquiv_iff]
  have hS : S g := ⟨a, ha⟩
  have := S.downward_closed hS (Over.homMk (𝟙 W.left) (Subsingleton.elim _ _) :
    Over.mk (g.left ≫ V.hom) ⟶ W)
  convert this using 1
  ext
  simp

/-- **Finite type on the slice site, point by point.** A presheaf of modules on `Opens X` sliced
over `U` is of finite type if every point of `U` has an open neighbourhood `U' ≤ U` carrying a
finite family of sections which generates it. -/
theorem isFiniteTypeSections_of_forall_mem (M : PresheafOfModules.{0} ((Over.forget U).op ⋙ R))
    (h : ∀ x ∈ U, ∃ (U' : Opens X) (hU' : U' ≤ U), x ∈ U' ∧ ∃ (n : ℕ)
      (s : Fin n → M.obj (op (Over.mk (homOfLE hU')))),
        GeneratesLocally ((Opens.grothendieckTopology X).over U) M s) :
    IsFiniteTypeSections ((Opens.grothendieckTopology X).over U) M := by
  choose U' hU' hx n s hs using h
  refine ⟨{x // x ∈ U}, fun x => Over.mk (homOfLE (hU' x.1 x.2)), ?_,
    fun x => ⟨n x.1 x.2, s x.1 x.2, hs x.1 x.2⟩⟩
  intro V
  rw [GrothendieckTopology.mem_over_iff, Opens.mem_grothendieckTopology]
  intro x hxV
  have hxU : x ∈ U := V.hom.le hxV
  refine ⟨V.left ⊓ U' x hxU, homOfLE inf_le_left, ?_, ⟨hxV, hx x hxU⟩⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨⟨x, hxU⟩, ⟨Over.homMk (homOfLE inf_le_right) (Subsingleton.elim _ _)⟩⟩

/-! ### Relations among sections of the structure sheaf -/

section Relations

variable {n : ℕ} (s : Fin n → (PresheafOfModules.unit R).obj (op U))

/-- Restrictions in a presheaf on `Opens X` compose along any path. -/
theorem map_map {A B C : Opens X} (a : B ⟶ A) (b : C ⟶ B) (c : C ⟶ A) (x : R.obj (op A)) :
    R.map b.op (R.map a.op x) = R.map c.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- A relation, from a tuple of coefficients and the proof that it is one. -/
def mkRel {V : Over U} (a : Fin n → R.obj (op V.left))
    (h : ∑ i, a i * R.map V.hom.op (s i) = 0) :
    (relationsPresheaf (PresheafOfModules.unit R) s).obj (op V) :=
  ⟨a, by
    simp only [LinearMap.mem_ker, Fintype.linearCombination_apply]
    exact h⟩

theorem rel_sum {V : Over U} (a : (relationsPresheaf (PresheafOfModules.unit R) s).obj (op V)) :
    ∑ i, (a.1 i) * R.map V.hom.op (s i) = 0 := by
  have := a.2
  simp only [LinearMap.mem_ker, Fintype.linearCombination_apply] at this
  exact this

theorem rel_ext {V : Over U} {a b : (relationsPresheaf (PresheafOfModules.unit R) s).obj (op V)}
    (h : ∀ i, a.1 i = b.1 i) : a = b := Subtype.ext (funext h)

theorem rel_restrict_apply {V W : Over U} (g : W ⟶ V)
    (a : (relationsPresheaf (PresheafOfModules.unit R) s).obj (op V)) (i : Fin n) :
    ((relationsPresheaf (PresheafOfModules.unit R) s).restrictₛₗ g.op a).1 i =
      R.map g.left.op (a.1 i) := rfl

theorem rel_sum_smul_apply {V : Over U} {ι : Type} [Fintype ι] (c : ι → R.obj (op V.left))
    (a : ι → (relationsPresheaf (PresheafOfModules.unit R) s).obj (op V)) (i : Fin n) :
    (∑ l, c l • a l).1 i = ∑ l, c l * (a l).1 i := by
  let φ : (relationsPresheaf (PresheafOfModules.unit R) s).obj (op V) →+ R.obj (op V.left) :=
    { toFun := fun a => a.1 i, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum φ _ _

/-- **Relations where some section is a unit.** If the restriction of `s j` to `U'` is a unit,
the relations `s j • eᵢ - s i • eⱼ` generate all relations among the `s i` over `U'`. -/
theorem exists_generatesLocally_of_isUnit
    (hcomm : ∀ (W : Opens X) (a b : R.obj (op W)), a * b = b * a) (U' : Over U) (j : Fin n)
    (hj : IsUnit (R.map U'.hom.op (s j))) :
    ∃ v : Fin n → (relationsPresheaf (PresheafOfModules.unit R) s).obj (op U'),
      GeneratesLocally ((Opens.grothendieckTopology X).over U)
        (relationsPresheaf (PresheafOfModules.unit R) s) v := by
  classical
  let σ : Fin n → R.obj (op U'.left) := fun i => R.map U'.hom.op (s i)
  refine ⟨fun i => mkRel s (Pi.single i (σ j) - Pi.single j (σ i)) ?_, ?_⟩
  · simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact sub_eq_zero.2 (hcomm _ _ _)
  intro V f t
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun W g _ => ?_⟩
  have hu : IsUnit (R.map W.hom.op (s j)) := by
    have h := hj.map (R.map (g ≫ f).left.op).hom
    convert h using 1
    exact (map_map (R := R) U'.hom (g ≫ f).left W.hom (s j)).symm
  let t' := (relationsPresheaf (PresheafOfModules.unit R) s).restrictₛₗ g.op t
  refine ⟨fun i => hu.unit⁻¹.1 * t'.1 i, ?_⟩
  refine rel_ext s fun k => ?_
  rw [rel_sum_smul_apply]
  have hρ : ∀ i, R.map (g ≫ f).left.op (σ i) = R.map W.hom.op (s i) := fun i =>
    map_map (R := R) U'.hom (g ≫ f).left W.hom (s i)
  have ht' := rel_sum s t'
  let ρ : Fin n → R.obj (op W.left) := fun i => R.map W.hom.op (s i)
  change ∑ i, t'.1 i * ρ i = 0 at ht'
  let u := hu.unit
  change ∑ l, ((u⁻¹ : (R.obj (op W.left))ˣ) * t'.1 l) *
    R.map (g ≫ f).left.op ((Pi.single l (σ j) - Pi.single j (σ l) : Fin n → _) k) = t'.1 k
  simp only [Pi.sub_apply, map_sub, Pi.single_apply, apply_ite (R.map (g ≫ f).left.op),
    map_zero, hρ]
  change ∑ l, ((u⁻¹ : (R.obj (op W.left))ˣ) * t'.1 l) *
    ((if k = l then ρ j else 0) - (if k = j then ρ l else 0)) = t'.1 k
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  have h0 : ∑ l, ((u⁻¹ : (R.obj (op W.left))ˣ) * t'.1 l) * ρ l = 0 := by
    simp only [mul_assoc, ← Finset.mul_sum, ht', mul_zero]
  rw [Finset.sum_ite_irrel, h0, Finset.sum_const_zero, ite_self, sub_zero, mul_assoc,
    hcomm _ (t'.1 k) (ρ j)]
  exact Units.inv_mul_cancel_left u _

/-- **Relations among sections vanishing on `U'`**: every tuple is one, and the basis tuples
generate them. -/
theorem exists_generatesLocally_of_eq_zero (U' : Over U)
    (h0 : ∀ i, R.map U'.hom.op (s i) = 0) :
    ∃ v : Fin n → (relationsPresheaf (PresheafOfModules.unit R) s).obj (op U'),
      GeneratesLocally ((Opens.grothendieckTopology X).over U)
        (relationsPresheaf (PresheafOfModules.unit R) s) v := by
  classical
  refine ⟨fun i => mkRel s (Pi.single i 1) ?_, ?_⟩
  · simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    exact h0 i
  intro V f t
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun W g _ => ?_⟩
  let t' := (relationsPresheaf (PresheafOfModules.unit R) s).restrictₛₗ g.op t
  refine ⟨fun i => t'.1 i, ?_⟩
  refine rel_ext s fun k => ?_
  rw [rel_sum_smul_apply]
  change ∑ l, t'.1 l * R.map (g ≫ f).left.op ((Pi.single l 1 : Fin n → R.obj (op U'.left)) k) =
    t'.1 k
  simp only [Pi.single_apply, apply_ite (R.map (g ≫ f).left.op), map_one, map_zero, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **Relations among sections coming from a field.** If over `U'` every `s i` is the image of an
element of a field `F` under a ring map `F → R(U')`, finitely many relations generate all
relations among the `s i` over `U'`. -/
theorem exists_generatesLocally_of_field
    (hcomm : ∀ (W : Opens X) (a b : R.obj (op W)), a * b = b * a) (U' : Over U)
    {F : Type} [Field F] (φ : F →+* R.obj (op U'.left))
    (hs : ∀ i, ∃ a, R.map U'.hom.op (s i) = φ a) :
    ∃ v : Fin n → (relationsPresheaf (PresheafOfModules.unit R) s).obj (op U'),
      GeneratesLocally ((Opens.grothendieckTopology X).over U)
        (relationsPresheaf (PresheafOfModules.unit R) s) v := by
  choose a ha using hs
  by_cases h : ∀ i, a i = 0
  · exact exists_generatesLocally_of_eq_zero s U' fun i => by rw [ha i, h i, map_zero]
  · push Not at h
    obtain ⟨j, hj⟩ := h
    refine exists_generatesLocally_of_isUnit s hcomm U' j ?_
    rw [ha j]
    exact (isUnit_iff_ne_zero.2 hj).map φ

/-- **Relations after a localisation.** Let `e : W → U'` be such that restriction along `e` is,
up to the first powers of `τ`, a localisation at `τ`: `τ` becomes a unit, every section over `W`
times a power of `τ` comes from `U'`, and `τ` kills what restriction kills. Then a family
generating the relations among the `s i` over `U'` generates, after restriction, the relations
over `W`. -/
theorem exists_sum_eq_of_localization
    (hcomm : ∀ (W : Opens X) (a b : R.obj (op W)), a * b = b * a) {U' W : Over U} (e : W ⟶ U')
    {m : ℕ} (gens : Fin m → (relationsPresheaf (PresheafOfModules.unit R) s).obj (op U'))
    (hgen : ∀ r, ∃ c : Fin m → R.obj (op U'.left), ∑ l, c l • gens l = r)
    (τ : R.obj (op U'.left)) (hτ : IsUnit (R.map e.left.op τ))
    (hden : ∀ b : R.obj (op W.left), ∃ (a : R.obj (op U'.left)) (N : ℕ),
      R.map e.left.op a = b * R.map e.left.op τ ^ N)
    (hker : ∀ a : R.obj (op U'.left), R.map e.left.op a = 0 → τ * a = 0)
    (t : (relationsPresheaf (PresheafOfModules.unit R) s).obj (op W)) :
    ∃ d : Fin m → R.obj (op W.left),
      ∑ l, d l • (relationsPresheaf (PresheafOfModules.unit R) s).restrictₛₗ e.op (gens l) = t := by
  classical
  let ρ := (R.map e.left.op).hom
  choose a N ha using fun i => hden (t.1 i)
  let N₀ := ∑ i, N i
  have hN : ∀ i, N i ≤ N₀ := fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  let a' : Fin n → R.obj (op U'.left) := fun i => a i * τ ^ (N₀ - N i)
  have ha' : ∀ i, ρ (a' i) = t.1 i * ρ τ ^ N₀ := fun i => by
    simp only [a', map_mul, map_pow]
    rw [ha i, mul_assoc, ← pow_add, Nat.add_sub_cancel' (hN i)]
  let σ : Fin n → R.obj (op U'.left) := fun i => R.map U'.hom.op (s i)
  have hρσ : ∀ i, ρ (σ i) = R.map W.hom.op (s i) := fun i =>
    map_map (R := R) U'.hom e.left W.hom (s i)
  have hrel : ∑ i, (τ * a' i) * σ i = 0 := by
    have h1 : ρ (∑ i, a' i * σ i) = 0 := by
      simp only [map_sum, map_mul, ha', hρσ]
      have := rel_sum s t
      calc ∑ i, t.1 i * ρ τ ^ N₀ * R.map W.hom.op (s i)
          = ρ τ ^ N₀ * ∑ i, t.1 i * R.map W.hom.op (s i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_assoc, hcomm _ _ (R.map W.hom.op (s i)), ← mul_assoc, hcomm _ (ρ τ ^ N₀)]
        _ = 0 := by rw [this, mul_zero]
    have := hker _ h1
    rw [Finset.mul_sum] at this
    simpa only [mul_assoc] using this
  obtain ⟨c, hc⟩ := hgen (mkRel s _ hrel)
  let u := hτ.unit
  refine ⟨fun l => ((u⁻¹ : (R.obj (op W.left))ˣ) : R.obj (op W.left)) ^ (N₀ + 1) * ρ (c l), ?_⟩
  refine rel_ext s fun k => ?_
  rw [rel_sum_smul_apply]
  have hk := congrArg (fun r : (relationsPresheaf (PresheafOfModules.unit R) s).obj (op U') =>
    ρ (r.1 k)) hc
  simp only [rel_sum_smul_apply, map_sum, map_mul] at hk
  change ∑ l, ρ (c l) * ρ ((gens l).1 k) = ρ (τ * a' k) at hk
  rw [map_mul, ha'] at hk
  change ∑ l, (((u⁻¹ : (R.obj (op W.left))ˣ) : R.obj (op W.left)) ^ (N₀ + 1) * ρ (c l)) *
    ρ ((gens l).1 k) = t.1 k
  simp only [mul_assoc, ← Finset.mul_sum, hk]
  have hu : (u : R.obj (op W.left)) = ρ τ := rfl
  rw [← hu, hcomm _ (t.1 k), ← mul_assoc (u : R.obj (op W.left)), ← pow_succ', ← mul_assoc,
    ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, inv_pow, Units.inv_mul, one_mul]
end Relations


/-! ### The same on the site of opens itself -/

section Base

variable {R' : (Opens X)ᵒᵖ ⥤ RingCat.{0}}

/-- **Local generation on `Opens X`, point by point.** -/
theorem generatesLocally_of_forall_mem' (M : PresheafOfModules.{0} R') {U' : Opens X}
    {ι : Type} [Fintype ι] (s : ι → M.obj (op U'))
    (h : ∀ (V : Opens X) (f : V ⟶ U') (t : M.obj (op V)) (x : X), x ∈ V →
      ∃ (W : Opens X) (g : W ⟶ V), x ∈ W ∧ ∃ a : ι → R'.obj (op W),
        ∑ i, a i • M.restrictₛₗ (g ≫ f).op (s i) = M.restrictₛₗ g.op t) :
    GeneratesLocally (Opens.grothendieckTopology X) M s := by
  intro V f t
  let S : Sieve V :=
    { arrows := fun W g => ∃ a : ι → R'.obj (op W),
        ∑ i, a i • M.restrictₛₗ (g ≫ f).op (s i) = M.restrictₛₗ g.op t
      downward_closed := by
        rintro W W' g ⟨a, ha⟩ e
        refine ⟨fun i => R'.map e.op (a i), ?_⟩
        have key : ∀ {A B : Opens X} (e : W' ⟶ A) (g : A ⟶ B) (m : M.obj (op B)),
            M.restrictₛₗ e.op (M.restrictₛₗ g.op m) = M.restrictₛₗ (e ≫ g).op m :=
          fun e g m => (M.map_comp_apply g.op e.op m).symm
        have := congrArg (M.restrictₛₗ e.op) ha
        rw [map_sum] at this
        simp only [map_smulₛₗ, key] at this
        rw [Category.assoc]
        exact this }
  refine ⟨S, ?_, fun W g hg => hg⟩
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨W, g, hxW, a, ha⟩ := h V f t x hx
  exact ⟨W, g, ⟨a, ha⟩, hxW⟩

/-- **Finite type on `Opens X`, point by point.** -/
theorem isFiniteTypeSections_of_forall_mem' (M : PresheafOfModules.{0} R')
    (h : ∀ x : X, ∃ (U' : Opens X), x ∈ U' ∧ ∃ (n : ℕ) (s : Fin n → M.obj (op U')),
        GeneratesLocally (Opens.grothendieckTopology X) M s) :
    IsFiniteTypeSections (Opens.grothendieckTopology X) M := by
  choose U' hx n s hs using h
  refine ⟨X, U', ?_, fun x => ⟨n x, s x, hs x⟩⟩
  intro V
  rw [Opens.mem_grothendieckTopology]
  intro x hxV
  exact ⟨V ⊓ U' x, homOfLE inf_le_left, ⟨x, ⟨homOfLE inf_le_right⟩⟩, ⟨hxV, hx x⟩⟩

end Base

end Grothendieck.Folder55Generation
