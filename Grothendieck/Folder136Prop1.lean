import Grothendieck.Folder136
import StacksFrontier.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# Folder 136, page 226, Proposition 1: `Φ_* ≃ 0`, and `C^{p,q}_*` is contractible for `p ≥ 1`

The reading (« La cohomologie », after « Le cas universel `S = k{T}` ») uses Proposition 1 of
page 226: the simplicial `k`-module `Φ_* : [n] ↦ k^{n+1}` of functions on the vertices is homotopic
to `0`, hence so is `C^{p,q}_* = Γ^p Φ_* ⊗ Λ^q Ψ_*` for `p ≠ 0` (Corollary 1.1, `F(Φ_*) ≃ F(0)` for
every functor `F`), hence `C^{p,q}_*` is acyclic. This is the second step of finding
`136-pd-de-rham-shadows`; the first step, the exactness of the rows, is in
`Grothendieck/Folder136.lean`.

**What is proved.** In the model of `Grothendieck/Folder136.lean` (`Φ_[n] = Fin (n+1) → k`,
`θ^* = LinearMap.funLeft θ`, `Ψ_[n] = PsiM k n`, `Γ = DividedPowerAlgebra`), over any commutative
ring `k`:
* `phiSimplicial`: the simplicial `k`-module `Φ_*`.
* `phi_htpyRel`, `phiHomotopy`: **Proposition 1**, a simplicial homotopy from the identity of `Φ_*`
  to `0`.
* `dpGrade`: `Γ^p M ⊆ Γ(M)`, the span of the products `x₁^{(n₁)} ⋯ x_r^{(n_r)}` with
  `n₁ + ⋯ + n_r = p`; it is carried into `Γ^p N` by `Γ(f)` (`map_mem_dpGrade`) and killed by
  `Γ(0)` for `p ≠ 0` (`map_zero_of_mem_dpGrade`); `T^{(p)} ∈ Γ^p` (`dp_mem_dpGrade`).
* `pdGradeSimplicial p q`: the simplicial `k`-module `C^{p,q}_* = Γ^p Φ_* ⊗ Λ^q Ψ_*`.
* `pdGrade_htpyRel`, `pdGradeHomotopy`: for `p ≠ 0`, a simplicial homotopy from the identity of
  `C^{p,q}_*` to `0`.
* `phi_chainHomotopy`, `pdGrade_chainHomotopy`: the alternating face map complexes of `Φ_*` and of
  `C^{p,q}_*`, `p ≠ 0`, are chain contractible;
  `phi_exactAt`, `pdGrade_exactAt`: they are acyclic in every degree.

**How.** The homotopy is indexed by the `n`-simplices `αⁿᵢ : [n] → [1]` of `Δ[1]`, `αⁿᵢ(x) = 0`
exactly for `x < i`, `0 ≤ i ≤ n + 1`. Its component at `αⁿᵢ` is the cut-off `cutoff i`,
`f ↦ (x ↦ f x if x < i, 0 otherwise)`: at `i = n + 1` it is the identity, at `i = 0` it is `0`,
and `θ^* ∘ cutoff i = cutoff i' ∘ θ^*` as soon as `θ(x) < i ↔ x < i'`, which is what the
face and degeneracy relations of Stacks 019L (`CategoryTheory.SimplicialObject.HtpyRel`) ask.
This is, on functions instead of free generators, the contracting homotopy of Stacks 07L7
(`Crystalline.simplexVertexModuleContractingHomotopy`, which sends `e_x` to `e_x` if `x < i` and
to `0` otherwise); Stacks states it for the cosimplicial module free on the vertices, the dual of
`Φ_*`, so it is not reused, the formula is. On `C^{p,q}_*` the components are
`Γ^p(cutoff i) ⊗ id`, natural by functoriality of `Γ` as in Stacks 07KQ
(`Crystalline.homotopic_exteriorPower_map`, written there for `Λ^i`), and at `i = 0` the map
`Γ^p(0)` vanishes for `p ≥ 1`. Stacks' `HtpyRel.toHomotopy` turns the family into Mathlib's
`SimplicialObject.Homotopy`, and Mathlib's `Homotopy.toChainHomotopy` into a chain homotopy.

**Not formalised.** The page's route (Dold–Puppe: the normalised complex of `Φ_*` is
`k → k` in degrees `1, 0`), replaced by the explicit homotopy. Corollaries 1.2 to 1.4
(`Ψ_*` is a `K(k, 1)`, `Λ^i Ψ_*` a `K(k, i)`, `π_ℓ(A_* ⊗ Λ^iΨ_*) ≅ π_{ℓ−i}(A_*)`). The
identification of `dpGrade p` with the weight-`p` part of the basis `dpBasis` of
`Grothendieck/Folder136.lean`, and the inclusion `C^{p,q}_* ⊆ pdSimplicial q`. The passage to
cohomology of a simplicial set `X` with coefficients in `C^{p,q}_*`, hence
`H^{p,q}_DRpd(X, k) ≅ H^q(X, k)`.
-/

namespace Grothendieck.Folder136Prop1

open CategoryTheory Opposite Simplicial Grothendieck.Folder136

universe u

section Cutoff

variable (k : Type u) [CommRing k]

/-- The cut-off `f ↦ (x ↦ f x if x < i, 0 otherwise)` on `Φ_[n] = k^{n+1}`: the component of the
contracting homotopy at the simplex of `Δ[1]` that is `0` exactly below `i`. -/
def cutoff {n : ℕ} (i : ℕ) : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k) where
  toFun f x := if (x : ℕ) < i then f x else 0
  map_add' f g := by ext x; split_ifs <;> simp [*]
  map_smul' r f := by ext x; split_ifs <;> simp [*]

variable {k}

theorem cutoff_apply {n : ℕ} (i : ℕ) (f : Fin (n + 1) → k) (x : Fin (n + 1)) :
    cutoff k i f x = if (x : ℕ) < i then f x else 0 := rfl

theorem cutoff_zero {n : ℕ} : cutoff k (n := n) 0 = 0 := by
  ext f x; simp [cutoff_apply]

theorem cutoff_of_le {n i : ℕ} (h : n + 1 ≤ i) : cutoff k (n := n) i = LinearMap.id := by
  ext f x; simp [cutoff_apply, show (x : ℕ) < i by omega]

/-- `θ^* ∘ cutoff i = cutoff i' ∘ θ^*` when `θ(x) < i ↔ x < i'` for every vertex `x`. -/
theorem funLeft_comp_cutoff {n m : ℕ} (θ : Fin (n + 1) → Fin (m + 1)) (i i' : ℕ)
    (h : ∀ x, (θ x : ℕ) < i ↔ (x : ℕ) < i') :
    LinearMap.funLeft k k θ ∘ₗ cutoff k i = cutoff k i' ∘ₗ LinearMap.funLeft k k θ := by
  ext f x
  simp [cutoff_apply, LinearMap.funLeft_apply, h x]

theorem succAbove_lt_iff_of_lt {n : ℕ} (j : Fin (n + 2)) (x : Fin (n + 1)) (i : ℕ)
    (hji : (j : ℕ) < i) : ((j.succAbove x : Fin (n + 2)) : ℕ) < i ↔ (x : ℕ) < i - 1 := by
  unfold Fin.succAbove
  split_ifs with h <;> simp [Fin.lt_def] at h ⊢ <;> omega

theorem succAbove_lt_iff_of_le {n : ℕ} (j : Fin (n + 2)) (x : Fin (n + 1)) (i : ℕ)
    (hij : i ≤ (j : ℕ)) : ((j.succAbove x : Fin (n + 2)) : ℕ) < i ↔ (x : ℕ) < i := by
  unfold Fin.succAbove
  split_ifs with h
  · simp [Fin.lt_def] at h ⊢
  · simp [Fin.lt_def] at h ⊢; omega

theorem predAbove_lt_iff_of_lt {n : ℕ} (j : Fin (n + 1)) (x : Fin (n + 2)) (i : ℕ)
    (hji : (j : ℕ) < i) : ((j.predAbove x : Fin (n + 1)) : ℕ) < i ↔ (x : ℕ) < i + 1 := by
  unfold Fin.predAbove
  split_ifs with h <;> simp [Fin.lt_def] at h ⊢ <;> omega

theorem predAbove_lt_iff_of_le {n : ℕ} (j : Fin (n + 1)) (x : Fin (n + 2)) (i : ℕ)
    (hij : i ≤ (j : ℕ)) : ((j.predAbove x : Fin (n + 1)) : ℕ) < i ↔ (x : ℕ) < i := by
  unfold Fin.predAbove
  split_ifs with h
  · simp [Fin.lt_def] at h ⊢; omega
  · simp [Fin.lt_def] at h ⊢

end Cutoff

section Phi

variable (k : Type u) [CommRing k]

/-- **The simplicial `k`-module `Φ_* : [n] ↦ k^{n+1}`** of functions on the vertices, with
`θ^* f = f ∘ θ` (page 226, `𝔏_*`). -/
noncomputable def phiSimplicial : SimplicialObject (ModuleCat.{u} k) where
  obj n := ModuleCat.of k (Fin (n.unop.len + 1) → k)
  map θ := ModuleCat.ofHom (LinearMap.funLeft k k θ.unop.toOrderHom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The components `h_{n,i} = cutoff i` of the contracting homotopy of `Φ_*`. -/
noncomputable def phiCutoff (n : ℕ) (i : Fin (n + 2)) :
    (phiSimplicial k).obj (op ⦋n⦌) ⟶ (phiSimplicial k).obj (op ⦋n⦌) :=
  ModuleCat.ofHom (cutoff k (n := n) (i : ℕ))

/-- **Proposition 1 (page 226), the homotopy.** The cut-offs satisfy the relations of
Stacks 019L for a homotopy from the identity of `Φ_*` to `0`. -/
theorem phi_htpyRel :
    SimplicialObject.HtpyRel (𝟙 (phiSimplicial k)) 0 (phiCutoff k) where
  bdry₀ n := by
    ext1
    exact cutoff_zero
  bdry₁ n := by
    ext1
    exact cutoff_of_le (by simp)
  face_gt n j i hij := by
    ext1
    exact funLeft_comp_cutoff _ _ _ fun x =>
      (succAbove_lt_iff_of_lt j x i hij).trans (by simp)
  face_le n j i hij := by
    ext1
    exact funLeft_comp_cutoff _ _ _ fun x =>
      (succAbove_lt_iff_of_le j x i hij).trans (by simp)
  degen_gt n j i hji := by
    ext1
    exact funLeft_comp_cutoff _ _ _ fun x =>
      (predAbove_lt_iff_of_lt j x i hji).trans (by simp)
  degen_le n j i hij := by
    ext1
    exact funLeft_comp_cutoff _ _ _ fun x =>
      (predAbove_lt_iff_of_le j x i hij).trans (by simp)

/-- **Proposition 1 (page 226): `Φ_*` is homotopic to `0`**, as a simplicial homotopy from the
identity to the zero map. -/
noncomputable def phiHomotopy :
    SimplicialObject.Homotopy (𝟙 (phiSimplicial k)) 0 :=
  (phi_htpyRel k).toHomotopy

end Phi

section Grade

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- `Γ^p M`: the span in `Γ(M)` of the products `x₁^{(n₁)} ⋯ x_r^{(n_r)}`, `∑ nᵢ = p`. -/
noncomputable def dpGrade (p : ℕ) : Submodule R (DividedPowerAlgebra R M) :=
  Submodule.span R {x | ∃ l : List (ℕ × M), (l.map Prod.fst).sum = p ∧
    x = (l.map fun a => DividedPowerAlgebra.dp R a.1 a.2).prod}

variable {R M}

theorem dp_mem_dpGrade (p : ℕ) (x : M) : DividedPowerAlgebra.dp R p x ∈ dpGrade R M p :=
  Submodule.subset_span ⟨[(p, x)], by simp, by simp⟩

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- `Γ(f)` carries `Γ^p M` into `Γ^p N`. -/
theorem map_mem_dpGrade (f : M →ₗ[R] N) {p : ℕ} {x : DividedPowerAlgebra R M}
    (hx : x ∈ dpGrade R M p) : DividedPowerAlgebra.map R f x ∈ dpGrade R N p := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine Submodule.subset_span
      ⟨l.map fun a => (a.1, f a.2), by simpa [Function.comp_def] using hl, ?_⟩
    rw [map_list_prod]
    simp [Function.comp_def]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- `Γ(0)` kills `Γ^p M` for `p ≠ 0`: `Γ^p(0) = 0`. -/
theorem map_zero_of_mem_dpGrade {p : ℕ} (hp : p ≠ 0) {x : DividedPowerAlgebra R M}
    (hx : x ∈ dpGrade R M p) : DividedPowerAlgebra.map R (0 : M →ₗ[R] N) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨a, ha, ha0⟩ : ∃ a ∈ l, a.1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hp (hl ▸ List.sum_eq_zero (by simpa using h))
    rw [map_list_prod]
    refine List.prod_eq_zero ?_
    simp only [List.map_map, List.mem_map, Function.comp_apply]
    exact ⟨a, ha, by simp [DividedPowerAlgebra.dp_null_of_ne_zero ha0]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

variable (p : ℕ)

/-- `Γ^p(f) : Γ^p M → Γ^p N`. -/
noncomputable def dpGradeMap (f : M →ₗ[R] N) : dpGrade R M p →ₗ[R] dpGrade R N p :=
  (DividedPowerAlgebra.map R f).toLinearMap.restrict fun _ hx => map_mem_dpGrade f hx

theorem dpGradeMap_id : dpGradeMap p (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext x
  simp [dpGradeMap, LinearMap.restrict_apply]

theorem dpGradeMap_comp {P : Type*} [AddCommGroup P] [Module R P] (f : M →ₗ[R] N)
    (g : N →ₗ[R] P) : dpGradeMap p (g ∘ₗ f) = dpGradeMap p g ∘ₗ dpGradeMap p f := by
  ext x
  change DividedPowerAlgebra.map R (g ∘ₗ f) x =
    DividedPowerAlgebra.map R g (DividedPowerAlgebra.map R f x)
  rw [DividedPowerAlgebra.map_comp]
  rfl

theorem dpGradeMap_zero (hp : p ≠ 0) : dpGradeMap p (0 : M →ₗ[R] N) = 0 := by
  ext x
  exact map_zero_of_mem_dpGrade hp x.2

end Grade

section PDGrade

variable (k : Type u) [CommRing k]

/-- `C^{p,q}_{[m]} = Γ^p Φ_[m] ⊗ Λ^q Ψ_[m]`. -/
abbrev PDGrade (m p q : ℕ) :=
  TensorProduct k (dpGrade k (Fin (m + 1) → k) p) (⋀[k]^q (PsiM k m))

/-- `C^{p,q}_{[m]}` is a `k`-module: the additive group of the tensor product, written with the
additive group of the submodule `Γ^p` (the instance search does not find it through `dpGrade`). -/
noncomputable instance pdGradeAddCommGroup (m p q : ℕ) : AddCommGroup (PDGrade k m p q) :=
  @TensorProduct.addCommGroup k _ _ _ (Submodule.addCommGroup _) _ _ _

variable {k}

theorem psiMap_id' {m : ℕ} : psiMap (k := k) (id : Fin (m + 1) → Fin (m + 1)) = LinearMap.id := by
  rw [psiMap, ← Submodule.mapQ_id]; rfl

theorem psiMap_comp' {m n l : ℕ} (θ : Fin (n + 1) → Fin (m + 1))
    (θ' : Fin (l + 1) → Fin (n + 1)) :
    psiMap (k := k) (θ ∘ θ') = psiMap θ' ∘ₗ psiMap θ := by
  rw [psiMap, psiMap, psiMap, ← Submodule.mapQ_comp]; rfl

/-- The simplicial operator `θ^* = Γ^p(Φ(θ)) ⊗ Λ^q(Ψ(θ))` on `C^{p,q}`. -/
noncomputable def pdGradeMap (p q : ℕ) {m n : ℕ} (θ : Fin (n + 1) → Fin (m + 1)) :
    PDGrade k m p q →ₗ[k] PDGrade k n p q :=
  TensorProduct.map (dpGradeMap p (LinearMap.funLeft k k θ)) (exteriorPower.map q (psiMap θ))

variable (k) in
/-- **The simplicial `k`-module `C^{p,q}_* = Γ^p Φ_* ⊗ Λ^q Ψ_*`** (pages 5–7). -/
noncomputable def pdGradeSimplicial (p q : ℕ) : SimplicialObject (ModuleCat.{u} k) where
  obj n := ModuleCat.of k (PDGrade k n.unop.len p q)
  map θ := ModuleCat.ofHom (pdGradeMap p q θ.unop.toOrderHom)
  map_id n := by
    ext1
    change pdGradeMap p q (id : Fin (n.unop.len + 1) → Fin (n.unop.len + 1)) = LinearMap.id
    rw [pdGradeMap, psiMap_id', exteriorPower.map_id]
    have : LinearMap.funLeft k k (id : Fin (n.unop.len + 1) → Fin (n.unop.len + 1)) =
      LinearMap.id := rfl
    rw [this, dpGradeMap_id]
    exact TensorProduct.map_id
  map_comp θ θ' := by
    ext1
    change pdGradeMap p q (θ.unop.toOrderHom ∘ θ'.unop.toOrderHom) =
      pdGradeMap p q θ'.unop.toOrderHom ∘ₗ pdGradeMap p q θ.unop.toOrderHom
    rw [pdGradeMap, pdGradeMap, pdGradeMap, psiMap_comp', exteriorPower.map_comp,
      ← TensorProduct.map_comp]
    have : LinearMap.funLeft k k (θ.unop.toOrderHom ∘ θ'.unop.toOrderHom) =
      LinearMap.funLeft k k θ'.unop.toOrderHom ∘ₗ LinearMap.funLeft k k θ.unop.toOrderHom :=
      rfl
    rw [this, dpGradeMap_comp]

/-- The component `Γ^p(cutoff i) ⊗ id` of the homotopy on `C^{p,q}_{[m]}`. -/
noncomputable def pdGradeCutoffMap (p q : ℕ) {m : ℕ} (i : ℕ) :
    PDGrade k m p q →ₗ[k] PDGrade k m p q :=
  TensorProduct.map (dpGradeMap p (cutoff k i)) LinearMap.id

theorem pdGradeMap_comp_cutoff (p q : ℕ) {n m : ℕ} (θ : Fin (n + 1) → Fin (m + 1)) (i i' : ℕ)
    (h : ∀ x, (θ x : ℕ) < i ↔ (x : ℕ) < i') :
    pdGradeMap p q θ ∘ₗ pdGradeCutoffMap (k := k) p q i =
      pdGradeCutoffMap p q i' ∘ₗ pdGradeMap p q θ := by
  rw [pdGradeMap, pdGradeCutoffMap, pdGradeCutoffMap, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, ← dpGradeMap_comp, ← dpGradeMap_comp, funLeft_comp_cutoff θ i i' h,
    LinearMap.comp_id, LinearMap.id_comp]

variable (k) in
/-- The components `h_{n,i} = Γ^p(cutoff i) ⊗ id` of the contracting homotopy of `C^{p,q}_*`. -/
noncomputable def pdGradeCutoff (p q n : ℕ) (i : Fin (n + 2)) :
    (pdGradeSimplicial k p q).obj (op ⦋n⦌) ⟶ (pdGradeSimplicial k p q).obj (op ⦋n⦌) :=
  ModuleCat.ofHom (pdGradeCutoffMap (k := k) (m := n) p q (i : ℕ))

variable (k) in
/-- **Corollary 1.1 for `Γ^p`, `p ≥ 1`: the homotopy.** The components `Γ^p(cutoff i) ⊗ id`
satisfy the relations of Stacks 019L for a homotopy from the identity of `C^{p,q}_*` to `0`. -/
theorem pdGrade_htpyRel {p : ℕ} (hp : p ≠ 0) (q : ℕ) :
    SimplicialObject.HtpyRel (𝟙 (pdGradeSimplicial k p q)) 0 (pdGradeCutoff k p q) where
  bdry₀ n := by
    ext1
    change pdGradeCutoffMap p q 0 = 0
    rw [pdGradeCutoffMap, cutoff_zero, dpGradeMap_zero p hp]
    exact TensorProduct.map_zero_left _
  bdry₁ n := by
    ext1
    change pdGradeCutoffMap p q (n + 1) = LinearMap.id
    rw [pdGradeCutoffMap, cutoff_of_le le_rfl, dpGradeMap_id]
    exact TensorProduct.map_id
  face_gt n j i hij := by
    ext1
    exact pdGradeMap_comp_cutoff p q _ _ _ fun x =>
      (succAbove_lt_iff_of_lt j x i hij).trans (by simp)
  face_le n j i hij := by
    ext1
    exact pdGradeMap_comp_cutoff p q _ _ _ fun x =>
      (succAbove_lt_iff_of_le j x i hij).trans (by simp)
  degen_gt n j i hji := by
    ext1
    exact pdGradeMap_comp_cutoff p q _ _ _ fun x =>
      (predAbove_lt_iff_of_lt j x i hji).trans (by simp)
  degen_le n j i hij := by
    ext1
    exact pdGradeMap_comp_cutoff p q _ _ _ fun x =>
      (predAbove_lt_iff_of_le j x i hij).trans (by simp)

variable (k) in
/-- **`C^{p,q}_* = Γ^p Φ_* ⊗ Λ^q Ψ_*` is homotopic to `0` for `p ≥ 1`** (page 226,
Corollary 1.1, as used on page 9). -/
noncomputable def pdGradeHomotopy {p : ℕ} (hp : p ≠ 0) (q : ℕ) :
    SimplicialObject.Homotopy (𝟙 (pdGradeSimplicial k p q)) 0 :=
  (pdGrade_htpyRel k hp q).toHomotopy

end PDGrade

section Acyclic

open AlgebraicTopology

variable (k : Type u) [CommRing k]

/-- A simplicial homotopy from the identity to `0` makes the alternating face map complex chain
contractible. -/
noncomputable def chainContraction {X : SimplicialObject (ModuleCat.{u} k)}
    (H : SimplicialObject.Homotopy (𝟙 X) 0) :
    Homotopy (𝟙 ((alternatingFaceMapComplex (ModuleCat.{u} k)).obj X)) 0 :=
  (Homotopy.ofEq ((alternatingFaceMapComplex (ModuleCat.{u} k)).map_id X).symm).trans
    (H.toChainHomotopy.trans
      (Homotopy.ofEq ((alternatingFaceMapComplex (ModuleCat.{u} k)).map_zero X X)))

/-- A chain contractible complex is exact in every degree. -/
theorem exactAt_of_contraction {K : ChainComplex (ModuleCat.{u} k) ℕ} (h : Homotopy (𝟙 K) 0)
    (n : ℕ) : K.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine (Limits.IsZero.iff_id_eq_zero _).2 ?_
  have := h.homologyMap_eq n
  rwa [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at this

/-- **`Φ_* ≃ 0` on chains**: the alternating face map complex of `Φ_*` is chain contractible. -/
noncomputable def phi_chainHomotopy :
    Homotopy (𝟙 ((alternatingFaceMapComplex (ModuleCat.{u} k)).obj (phiSimplicial k))) 0 :=
  chainContraction k (phiHomotopy k)

/-- **`Φ_*` is acyclic.** -/
theorem phi_exactAt (n : ℕ) :
    ((alternatingFaceMapComplex (ModuleCat.{u} k)).obj (phiSimplicial k)).ExactAt n :=
  exactAt_of_contraction k (phi_chainHomotopy k) n

/-- **`C^{p,q}_*`, `p ≥ 1`, on chains**: its alternating face map complex is chain
contractible. -/
noncomputable def pdGrade_chainHomotopy {p : ℕ} (hp : p ≠ 0) (q : ℕ) :
    Homotopy (𝟙 ((alternatingFaceMapComplex (ModuleCat.{u} k)).obj
      (pdGradeSimplicial k p q))) 0 :=
  chainContraction k (pdGradeHomotopy k hp q)

/-- **`C^{p,q}_* = Γ^p Φ_* ⊗ Λ^q Ψ_*` is acyclic for `p ≥ 1`** (page 9, from Proposition 1 of
page 226). -/
theorem pdGrade_exactAt {p : ℕ} (hp : p ≠ 0) (q n : ℕ) :
    ((alternatingFaceMapComplex (ModuleCat.{u} k)).obj (pdGradeSimplicial k p q)).ExactAt n :=
  exactAt_of_contraction k (pdGrade_chainHomotopy k hp q) n

end Acyclic

end Grothendieck.Folder136Prop1
