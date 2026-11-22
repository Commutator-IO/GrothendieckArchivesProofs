module

public import Grothendieck.Folder126NilpotentQuotient
public import StacksFrontier.RingTheory.Descent.AmitsurComplex
public import StacksFrontier.RingTheory.Descent.NilpotentEqualizerLift
public import StacksFrontier.RingTheory.Descent.CechSquareZeroGenerators

@[expose] public section

/-!
# Folder 126, pages 5 to 7: the invariant ring of a thickened flat equivalence relation

Finding `126-nilpotent-deformation-quotient`, continued from `Folder126NilpotentQuotient`, which
proves the two closing steps of page 7 for a given `Y = Spec A'` and assumes the descent of
`𝒥_X`. Here, in the affine case, `A'` is constructed as the ring of invariant functions
`Ker(𝒪_X ⇉ 𝒪_R)`, the sequence `0 → 𝒥_Y → 𝒪_Y → 𝒪_{Y₀} → 0` is proved exact, and the
hypothesis of `Folder126NilpotentQuotient` on `𝒥_Y ⊗ 𝒪_{X₀} → 𝒥_X` is derived by faithfully
flat descent.

The affine situation is `IsThickenedNerve`: `X = Spec B'`, the relation `R = Spec C'` with its two
projections `s, t : B' → C'` and diagonal `μ`, the triple overlap `R ×_X R = Spec D'` with its
three projections, and the reductions modulo `J = 𝒥_X` onto the Čech nerve
`B ⇉ B ⊗_A B ⇉ B ⊗_A B ⊗_A B` of a faithfully flat `A → B` (`X₀ = Spec B → Y₀ = Spec A`,
`R₀ ≅ X₀ ×_{Y₀} X₀`); the kernels on `C'`, `D'` are the extensions of `J`, and `t`, `f₂₃` are
flat.

**What is proved.**
* `injective_amitsurAug`, `exact_amitsur_zero`, `exact_amitsur_one`: the concrete Amitsur complex
  `0 → M → B ⊗_A M ⇉ B ⊗_A B ⊗_A M → B ⊗_A B ⊗_A B ⊗_A M` of a faithfully flat `A → B` is exact
  in degrees `-1`, `0` and `1` (Stacks 023M), on the tensor products themselves;
  `mem_range_of_tmul_one_eq` is degree zero for `M = A`.
* `exists_isBaseChange_invariant_ideal`: faithfully flat descent (Stacks 023N) of a square-zero
  ideal `N` of a thickened nerve: `N` is the base change of its submodule of invariant elements.
* `IsThickenedNerve.toBase`: the map `𝒪_Y → 𝒪_{Y₀}`, from the equaliser `A' = Ker(B' ⇉ C')` to
  `A`; `algebraMap_toBase` says it lifts the reduction `B' → B`.
* `IsThickenedNerve.ker_toBase_eq_and_surjective`: **the exact sequence
  `0 → 𝒥_Y → 𝒪_Y → 𝒪_{Y₀} → 0`** for a nilpotent `J`: `toBase` is surjective
  (`surjective_toBase`, pages 5 to 7) and its kernel is `J ∩ A'` (`mem_ker_toBase_iff`).
* `IsThickenedNerve.bijective_fibreTensorSMulHomToKer`: for `J² = 0`, the canonical map
  `I ⊗_{A'} B → J` is bijective, `I = J ∩ A'` (`𝒥_X ≅ 𝒥_Y ⊗ 𝒪_{X₀}`, page 5): the hypothesis
  `hJ` of `Folder126NilpotentQuotient.flat_and_bijective_of_thickening`, derived.
* `IsThickenedNerve.flat_eqLocus`: for `J² = 0`, `B'` is flat over `A'` (`X → Y` flat), and
  `IsThickenedNerve.flat_and_bijective`, page 7 with `Y` constructed: a map
  `B' ⊗_{A'} B' → C''` into a flat `B'`-algebra which is bijective modulo `I` is bijective.

**How.** The Amitsur statements are `Module.Descent.exact_amitsur_degree_zero` and
`Module.Descent.exact_amitsur_degree_one` of the vendored Stacks files (a contracting homotopy
after base change to `B`, then faithful flatness), and `Algebra.IsEffective.of_faithfullyFlat` of
Mathlib for the ring. The lift of an invariant function is
`Module.Descent.exists_eq_of_isNilpotent_ker`: lift `a ∈ A` to `B'`, then correct the lift one
graded piece `J^k ⧸ J^(k+1)` at a time with the vanishing of the first Čech cohomology
(degree-one exactness of the Amitsur complex), so the nilpotent case needs no separate reduction
to `J² = 0`. The descent of `J` builds, from the restriction maps of `J`, `J C'`, `J D'`, the
Čech comparison data `Module.Descent.IsCechModule` (following the proof of
`Module.Descent.exists_fin_invariant_span_ideal`, which concludes with finite generation instead)
and applies effectivity of flat descent, `Module.Descent.Datum.isBaseChange`. The invariant
elements of `J` are the elements of `I = J ∩ A'`, so the descended module is `I` with its
`A ≅ A' ⧸ I`-module structure, and `I ⊗_{A'} B → J` factors as a surjection
`I ⊗_{A'} B ← B ⊗_A I` followed by the descent isomorphism. Flatness is then
`Ideal.bijective_fibreTensorSMulHomToKer_iff` (Stacks 063Y, affine case).

**Not formalised.**
* The scheme level: `Y₀` quasi-separated but not affine, the vanishing
  `Ȟ⁰(X₀/Y₀, ℋ¹(𝒥_Y)) = 0` of Remark 2 (page 3), the gluing of the affine pieces of
  `(Y₀, Ker(𝒪_X ⇉ 𝒪_R))` into a scheme, and the effectivity of `R` as an equivalence relation.
* The construction of the nerve from `R ⇉ X`: `R ×_X R`, its three projections, and the
  identifications `R₀ = R ×_X X₀ ≅ X₀ ×_{Y₀} X₀` are the hypotheses of `IsThickenedNerve`.
* Here, for a nilpotent `J`, only the exact sequence is proved; the descent of `J` and the
  flatness of `X → Y` are proved for `J² = 0`. The nilpotent case of the flatness, by induction
  along `X₀ = X_1 ⊂ X_2 ⊂ ⋯ ⊂ X`, `X_k = Spec (B' ⧸ J^k)`, is `Folder126NilpotentFlat`.
* In `flat_and_bijective` the map `φ : B' ⊗_{A'} B' → C''` and its bijectivity modulo `I` are
  hypotheses: identifying `(A' ⧸ I) ⊗_{A'} φ` with `B ⊗_A B ≅ C' ⧸ J C'` (that is
  `R₀ ≅ X₀ ×_{Y₀} X₀`) is not done.
-/

namespace Grothendieck.Folder126NilpotentDescent

open TensorProduct

universe u

section Amitsur

variable (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
  [Module.FaithfullyFlat A B] (M : Type*) [AddCommGroup M] [Module A M]

/-- **The Amitsur complex is exact in degree `-1`**: `M → B ⊗_A M` is injective. -/
theorem injective_amitsurAug : Function.Injective (Module.Descent.amitsurAug A B M) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective M

/-- **The Amitsur complex is exact in degree `0`**: `M → B ⊗_A M ⇉ B ⊗_A B ⊗_A M`. -/
theorem exact_amitsur_zero :
    Function.Exact (Module.Descent.amitsurAug A B M) (Module.Descent.amitsurDiff₀ A B M) :=
  Module.Descent.exact_amitsur_degree_zero A B M

/-- **The Amitsur complex is exact in degree `1`**: every `1`-cocycle of
`B ⊗_A M → B ⊗_A B ⊗_A M → B ⊗_A B ⊗_A B ⊗_A M` is a coboundary. -/
theorem exact_amitsur_one :
    Function.Exact (Module.Descent.amitsurDiff₀ A B M) (Module.Descent.amitsurDiff₁ A B M) :=
  Module.Descent.exact_amitsur_degree_one A B M

/-- Degree zero for the ring itself: an element `b` of `B` with `b ⊗ 1 = 1 ⊗ b` in `B ⊗_A B`
comes from `A`. -/
theorem mem_range_of_tmul_one_eq (b : B)
    (h : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) : b ∈ Set.range (algebraMap A B) := by
  rw [← (Algebra.IsEffective.of_faithfullyFlat A B).eqLocus_includeLeft_includeRight]
  exact h

end Amitsur

section Descent

open Module.Descent

variable {B C D A₁ B₁ : Type*} [CommRing B] [CommRing C] [CommRing D] [CommRing A₁]
  [CommRing B₁] [Algebra A₁ B₁]
  {πB : B →+* B₁} {πC : C →+* B₁ ⊗[A₁] B₁} {πD : D →+* B₁ ⊗[A₁] (B₁ ⊗[A₁] B₁)}
  {N : Ideal B} [Module B₁ N] [Module A₁ N] [IsScalarTower A₁ B₁ N]
  {J : Ideal C} [Module (B₁ ⊗[A₁] B₁) J] [Module A₁ J] [IsScalarTower A₁ (B₁ ⊗[A₁] B₁) J]
  {L : Ideal D} [Module (B₁ ⊗[A₁] (B₁ ⊗[A₁] B₁)) L] [Module A₁ L]
  [IsScalarTower A₁ (B₁ ⊗[A₁] (B₁ ⊗[A₁] B₁)) L]

omit [Module (B₁ ⊗[A₁] B₁) J] [IsScalarTower A₁ (B₁ ⊗[A₁] B₁) J] in
/-- If `J` is the extension of `N` along `p` and `f ∘ p` maps `N` into `K`, then `f` maps `J`
into `K`. -/
theorem mem_of_map_eq' {X Y Z : Type*} [CommRing X] [CommRing Y] [CommRing Z] (p : X →+* Y)
    (f : Y →+* Z) {N : Ideal X} {J : Ideal Y} {K : Ideal Z} (hJ : J = N.map p)
    (h : ∀ x ∈ N, f (p x) ∈ K) : ∀ y ∈ J, f y ∈ K := by
  subst hJ
  exact fun _ hy => (Ideal.map_le_iff_le_comap (K := K.comap f)).2 h hy

/-- **Faithfully flat descent of a square-zero ideal of a thickened nerve** (Stacks 023N in the
form page 5 uses: `𝒥_X ≅ 𝒥_Y ⊗ 𝒪_{X₀}`). The ideal `N` of `B`, read as a module over `B₁`, with
its extensions `J`, `L` to `C`, `D`, is the base change along the flat `A₁ → B₁` of its
submodule of invariant elements, those `n` with `p₁ n = p₂ n`. The comparison maps are those of
`Module.Descent.exists_fin_invariant_span_ideal`, whose proof this follows up to the descent
datum; the conclusion is effectivity of descent (`Module.Descent.Datum.isBaseChange`) instead of
finite generation. -/
theorem exists_isBaseChange_invariant_ideal [Module.Flat A₁ B₁]
    {p₁ p₂ : B →+* C} {δ : C →+* B} {e₁₂ e₁₃ e₂₃ : C →+* D}
    (hδ₁ : ∀ β, δ (p₁ β) = β) (hδ₂ : ∀ β, δ (p₂ β) = β)
    (h₁₂₁₃ : ∀ β, e₁₂ (p₁ β) = e₁₃ (p₁ β)) (h₁₂₂₃ : ∀ β, e₁₂ (p₂ β) = e₂₃ (p₁ β))
    (h₁₃₂₃ : ∀ β, e₁₃ (p₂ β) = e₂₃ (p₂ β))
    (hp₂ : p₂.Flat) (hg : (e₂₃.comp p₂).Flat)
    (hJ₁ : J = N.map p₁) (hJ₂ : J = N.map p₂) (hL₁ : L = N.map (e₁₂.comp p₁))
    (hL₃ : L = N.map (e₂₃.comp p₂))
    (hsB : Function.Surjective πB) (hsC : Function.Surjective πC)
    (sB : ∀ (β : B) (n : N), πB β • n = β • n) (sC : ∀ (γ : C) (y : J), πC γ • y = γ • y)
    (sD : ∀ (d : D) (z : L), πD d • z = d • z)
    (hC₁ : ∀ β, πC (p₁ β) = πB β ⊗ₜ[A₁] (1 : B₁))
    (hC₂ : ∀ β, πC (p₂ β) = (1 : B₁) ⊗ₜ[A₁] πB β)
    (hD₁₂ : ∀ γ, πD (e₁₂ γ) = Algebra.TensorProduct.map (AlgHom.id A₁ B₁)
      (Algebra.TensorProduct.includeLeft : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁) (πC γ))
    (hD₁₃ : ∀ γ, πD (e₁₃ γ) = Algebra.TensorProduct.map (AlgHom.id A₁ B₁)
      (Algebra.TensorProduct.includeRight : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁) (πC γ))
    (hD₂₃ : ∀ γ, πD (e₂₃ γ) = (Algebra.TensorProduct.includeRight :
      B₁ ⊗[A₁] B₁ →ₐ[A₁] B₁ ⊗[A₁] (B₁ ⊗[A₁] B₁)) (πC γ)) :
    ∃ M : Submodule A₁ N, (∀ n : N, n ∈ M ↔ p₁ n = p₂ n) ∧ IsBaseChange B₁ M.subtype := by
  classical
  have mJ₁ : ∀ x ∈ N, p₁ x ∈ J := fun x hx => hJ₁ ▸ Ideal.mem_map_of_mem p₁ hx
  have mJ₂ : ∀ x ∈ N, p₂ x ∈ J := fun x hx => hJ₂ ▸ Ideal.mem_map_of_mem p₂ hx
  have mN : ∀ y ∈ J, δ y ∈ N := mem_of_map_eq' p₁ δ hJ₁ fun x hx => by rw [hδ₁]; exact hx
  have mL₁₂ : ∀ y ∈ J, e₁₂ y ∈ L := mem_of_map_eq' p₁ e₁₂ hJ₁ fun x hx => by
    rw [hL₁]; exact Ideal.mem_map_of_mem (e₁₂.comp p₁) hx
  have mL₁₃ : ∀ y ∈ J, e₁₃ y ∈ L := mem_of_map_eq' p₁ e₁₃ hJ₁ fun x hx => by
    rw [← h₁₂₁₃, hL₁]; exact Ideal.mem_map_of_mem (e₁₂.comp p₁) hx
  have mL₂₃ : ∀ y ∈ J, e₂₃ y ∈ L := mem_of_map_eq' p₂ e₂₃ hJ₂ fun x hx => by
    rw [hL₃]; exact Ideal.mem_map_of_mem (e₂₃.comp p₂) hx
  let τ₁ : B₁ →+* B₁ ⊗[A₁] B₁ :=
    (Algebra.TensorProduct.includeLeft : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁).toRingHom
  let τ₂ : B₁ →+* B₁ ⊗[A₁] B₁ :=
    (Algebra.TensorProduct.includeRight : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁).toRingHom
  let τ₁₂ : B₁ ⊗[A₁] B₁ →+* B₁ ⊗[A₁] (B₁ ⊗[A₁] B₁) := (Algebra.TensorProduct.map (AlgHom.id A₁ B₁)
      (Algebra.TensorProduct.includeLeft : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁)).toRingHom
  let τ₁₃ : B₁ ⊗[A₁] B₁ →+* B₁ ⊗[A₁] (B₁ ⊗[A₁] B₁) := (Algebra.TensorProduct.map (AlgHom.id A₁ B₁)
      (Algebra.TensorProduct.includeRight : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁)).toRingHom
  let τ₂₃ : B₁ ⊗[A₁] B₁ →+* B₁ ⊗[A₁] (B₁ ⊗[A₁] B₁) := (Algebra.TensorProduct.includeRight :
      B₁ ⊗[A₁] B₁ →ₐ[A₁] B₁ ⊗[A₁] (B₁ ⊗[A₁] B₁)).toRingHom
  have sφ₁ := map_smul_of_lift πB πC hsB sB sC p₁ τ₁ hC₁ _ (idealMap_smul p₁ N J mJ₁)
  have sφ₂ := map_smul_of_lift πB πC hsB sB sC p₂ τ₂ hC₂ _ (idealMap_smul p₂ N J mJ₂)
  have sχ₁₂ := map_smul_of_lift πC πD hsC sC sD e₁₂ τ₁₂ hD₁₂ _ (idealMap_smul e₁₂ J L mL₁₂)
  have sχ₁₃ := map_smul_of_lift πC πD hsC sC sD e₁₃ τ₁₃ hD₁₃ _ (idealMap_smul e₁₃ J L mL₁₃)
  have sχ₂₃ := map_smul_of_lift πC πD hsC sC sD e₂₃ τ₂₃ hD₂₃ _ (idealMap_smul e₂₃ J L mL₂₃)
  let φ₁ : N →ₗ[A₁] J := linearOfSemilinear
    (Algebra.TensorProduct.includeLeft : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁) (idealMap p₁ N J mJ₁) sφ₁
  let φ₂ : N →ₗ[A₁] J := linearOfSemilinear
    (Algebra.TensorProduct.includeRight : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁) (idealMap p₂ N J mJ₂) sφ₂
  have hθ : ∀ (b : B₁) (y : J), idealMap δ J N mN
      ((Algebra.TensorProduct.includeLeft : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁) b • y) =
        b • idealMap δ J N mN y := by
    intro b y
    obtain ⟨β, rfl⟩ := hsB b
    rw [Algebra.TensorProduct.includeLeft_apply, ← hC₁, sC, idealMap_smul, hδ₁, sB]
  let θ : J →ₗ[A₁] N := linearOfSemilinear'
    (Algebra.TensorProduct.includeLeft : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁) (idealMap δ J N mN) hθ
  let χ₁₂ : J →ₗ[A₁] L := linearOfSemilinear
    (Algebra.TensorProduct.map (AlgHom.id A₁ B₁)
      (Algebra.TensorProduct.includeLeft : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁)) (idealMap e₁₂ J L mL₁₂) sχ₁₂
  let χ₁₃ : J →ₗ[A₁] L := linearOfSemilinear
    (Algebra.TensorProduct.map (AlgHom.id A₁ B₁)
      (Algebra.TensorProduct.includeRight : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁)) (idealMap e₁₃ J L mL₁₃) sχ₁₃
  let χ₂₃ : J →ₗ[A₁] L := linearOfSemilinear
    (Algebra.TensorProduct.includeRight : B₁ ⊗[A₁] B₁ →ₐ[A₁] B₁ ⊗[A₁] (B₁ ⊗[A₁] B₁))
    (idealMap e₂₃ J L mL₂₃) sχ₂₃
  have hπ₁₂ : ∀ β, πD (e₁₂ (p₁ β)) = πB β ⊗ₜ[A₁] ((1 : B₁) ⊗ₜ[A₁] (1 : B₁)) := fun β => by
    rw [hD₁₂, hC₁, Algebra.TensorProduct.map_tmul, map_one]; rfl
  have hπ₂₃ : ∀ β, πD (e₂₃ (p₁ β)) = (1 : B₁) ⊗ₜ[A₁] (πB β ⊗ₜ[A₁] (1 : B₁)) := fun β => by
    rw [hD₂₃, hC₁]; rfl
  have hπ₂₃' : ∀ β, πD (e₂₃ (p₂ β)) = (1 : B₁) ⊗ₜ[A₁] ((1 : B₁) ⊗ₜ[A₁] πB β) := fun β => by
    rw [hD₂₃, hC₂]; rfl
  have hτ : ∀ (i : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁) (b : B₁), Algebra.TensorProduct.map (AlgHom.id A₁ B₁) i
      (b ⊗ₜ[A₁] (1 : B₁)) = b ⊗ₜ[A₁] ((1 : B₁) ⊗ₜ[A₁] (1 : B₁)) := fun i b =>
    (Algebra.TensorProduct.map_tmul _ _ _ _).trans (by rw [map_one]; rfl)
  have H : IsCechModule (B₀ := B₁) φ₁ φ₂ θ χ₁₂ χ₁₃ χ₂₃ :=
    { φ₁_smul := fun b n => sφ₁ b n
      φ₂_smul := fun b n => sφ₂ b n
      θ_smul := hθ
      θ_φ₁ := fun n => Subtype.ext (hδ₁ n)
      θ_φ₂ := fun n => Subtype.ext (hδ₂ n)
      χ₁₂_smul := fun b y => by
        have := sχ₁₂ (b ⊗ₜ[A₁] (1 : B₁)) y
        rwa [show τ₁₂ (b ⊗ₜ[A₁] (1 : B₁)) = _ from hτ _ b] at this
      χ₁₃_smul := fun b y => by
        have := sχ₁₃ (b ⊗ₜ[A₁] (1 : B₁)) y
        rwa [show τ₁₃ (b ⊗ₜ[A₁] (1 : B₁)) = _ from hτ _ b] at this
      χ₂₃_smul := fun b y => sχ₂₃ (b ⊗ₜ[A₁] (1 : B₁)) y
      χ₁₂_φ₁ := fun n => Subtype.ext (h₁₂₁₃ n)
      χ₁₂_φ₂ := fun n => Subtype.ext (h₁₂₂₃ n)
      χ₁₃_φ₂ := fun n => Subtype.ext (h₁₃₂₃ n)
      bijective_comparison := bijective_cechComparison_ideal hp₂ hJ₂ hsB sB sC hC₁ hC₂ φ₂
        (fun _ => rfl)
      injective_comparison₃ := injective_cechComparison₃_ideal hg hL₃ hsB sB sD hπ₁₂ hπ₂₃
        hπ₂₃' φ₂ (fun _ => rfl) χ₂₃ (fun _ => rfl) }
  refine ⟨H.datum.descended, fun n => ?_, H.datum.isBaseChange⟩
  rw [H.mem_descended_datum_iff n]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end Descent

section Nerve

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {B' C' D' : Type u} [CommRing B'] [CommRing C'] [CommRing D']

/-- **A thickened flat equivalence relation over an affine quotient of its reduction.** `X =
Spec B'` with the equivalence relation `R = Spec C'` (projections `s, t : B' → C'`, diagonal
`μ : C' → B'`) and `R ×_X R = Spec D'` (projections `f₁₂, f₁₃, f₂₃ : C' → D'`); the reductions
`πB`, `πC`, `πD` modulo the ideal `J = Ker πB` of `X₀ ⊂ X` identify `X₀ = Spec B`,
`R₀ = X₀ ×_{Y₀} X₀` and `R₀ ×_{X₀} R₀` with `Y₀ = Spec A`. The kernels on `C'` and `D'` are the
extensions of `J` (`R₀ = R ×_X X₀` along either projection), and `t` and `f₂₃` are flat (`R`
flat over `X`). -/
structure IsThickenedNerve (πB : B' →+* B) (πC : C' →+* B ⊗[A] B)
    (πD : D' →+* B ⊗[A] (B ⊗[A] B)) (s t : B' →+* C') (μ : C' →+* B')
    (f₁₂ f₁₃ f₂₃ : C' →+* D') : Prop where
  surjective_B : Function.Surjective πB
  surjective_C : Function.Surjective πC
  surjective_D : Function.Surjective πD
  comp_s : πC.comp s = Algebra.TensorProduct.includeLeftRingHom.comp πB
  comp_t : πC.comp t = (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom.comp πB
  comp_f₁₂ : πD.comp f₁₂ = (Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom.comp πC
  comp_f₁₃ : πD.comp f₁₃ = (Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom.comp πC
  comp_f₂₃ : πD.comp f₂₃ =
    (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom.comp πC
  μ_s : μ.comp s = RingHom.id B'
  μ_t : μ.comp t = RingHom.id B'
  f₁₂_s : f₁₂.comp s = f₁₃.comp s
  f₁₂_t : f₁₂.comp t = f₂₃.comp s
  f₁₃_t : f₁₃.comp t = f₂₃.comp t
  ker_C_s : RingHom.ker πC = (RingHom.ker πB).map s
  ker_C_t : RingHom.ker πC = (RingHom.ker πB).map t
  ker_D : RingHom.ker πD = (RingHom.ker πC).map f₂₃
  flat_t : t.Flat
  flat_f₂₃ : f₂₃.Flat

variable {πB : B' →+* B} {πC : C' →+* B ⊗[A] B} {πD : D' →+* B ⊗[A] (B ⊗[A] B)}
  {s t : B' →+* C'} {μ : C' →+* B'} {f₁₂ f₁₃ f₂₃ : C' →+* D'}

namespace IsThickenedNerve

variable (H : IsThickenedNerve πB πC πD s t μ f₁₂ f₁₃ f₂₃)
include H

/-- The reduction of an invariant function on `X` is an invariant function on `X₀`, hence comes
from `Y₀` (degree zero of the Amitsur complex of `A → B`). -/
theorem mem_range_of_mem_eqLocus [Module.FaithfullyFlat A B] {b : B'}
    (hb : b ∈ RingHom.eqLocus s t) : πB b ∈ Set.range (algebraMap A B) := by
  refine mem_range_of_tmul_one_eq A B (πB b) ?_
  have h1 := RingHom.congr_fun H.comp_s b
  have h2 := RingHom.congr_fun H.comp_t b
  simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2
  rw [RingHom.mem_eqLocus] at hb
  rw [hb] at h1
  exact h1.symm.trans h2

/-- **Lifting invariant functions** (pages 5 to 7, the surjectivity of `𝒪_Y → 𝒪_{Y₀}`): when `J`
is nilpotent every `a ∈ A` is the reduction of an invariant function on `X`. -/
theorem exists_mem_eqLocus [Module.FaithfullyFlat A B] (hnil : IsNilpotent (RingHom.ker πB))
    (a : A) : ∃ b ∈ RingHom.eqLocus s t, πB b = algebraMap A B a := by
  have e1 : (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B).comp (algebraMap A B) =
      algebraMap A (B ⊗[A] B) := RingHom.ext fun a => rfl
  have e2 : (Algebra.TensorProduct.map (AlgHom.id A B)
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] (B ⊗[A] B)) := by
    refine RingHom.ext fun b => ?_
    simp
  have P2 := CommRingCat.isPushout_tensorProduct A B (B ⊗[A] B)
  rw [← e1, ← e2] at P2
  obtain ⟨b, hst, hb⟩ := Module.Descent.exists_eq_of_isNilpotent_ker s t μ f₁₂ f₁₃ f₂₃
    H.surjective_B H.surjective_C H.surjective_D _ _ _ _ H.comp_s H.comp_t H.comp_f₁₂
    H.comp_f₂₃ H.μ_s H.μ_t H.f₁₂_s H.f₁₂_t H.f₁₃_t H.ker_C_s H.ker_C_t H.ker_D H.flat_t
    H.flat_f₂₃ hnil (CommRingCat.isPushout_tensorProduct A B B) P2 a
  exact ⟨b, hst, hb⟩

/-- `A` is isomorphic to its image in `B`, `A → B` being faithfully flat. -/
noncomputable def equivRange (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] : A ≃+* (algebraMap A B).range :=
  RingEquiv.ofBijective (algebraMap A B).rangeRestrict
    ⟨fun _ _ h => FaithfulSMul.algebraMap_injective A B (congrArg Subtype.val h),
      (algebraMap A B).rangeRestrict_surjective⟩

/-- **The map `𝒪_Y → 𝒪_{Y₀}`** on global sections: an invariant function on `X`, that is an
element of the equaliser `A' = Ker(B' ⇉ C')`, reduces to an invariant function on `X₀`, which is
an element of `A`. -/
noncomputable def toBase [Module.FaithfullyFlat A B] : RingHom.eqLocus s t →+* A :=
  (equivRange A B).symm.toRingHom.comp
    ((πB.comp (RingHom.eqLocus s t).subtype).codRestrict (algebraMap A B).range
      fun b => H.mem_range_of_mem_eqLocus b.2)

/-- The map `toBase` followed by `A → B` is the reduction `B' → B`. -/
theorem algebraMap_toBase [Module.FaithfullyFlat A B] (b : RingHom.eqLocus s t) :
    algebraMap A B (H.toBase b) = πB b := by
  have h := congrArg Subtype.val ((equivRange A B).apply_symm_apply
    ((πB.comp (RingHom.eqLocus s t).subtype).codRestrict (algebraMap A B).range
      (fun b => H.mem_range_of_mem_eqLocus b.2) b))
  exact h

/-- **Pages 5 to 7: `𝒪_Y → 𝒪_{Y₀}` is surjective** when `J` is nilpotent. -/
theorem surjective_toBase [Module.FaithfullyFlat A B] (hnil : IsNilpotent (RingHom.ker πB)) :
    Function.Surjective H.toBase := by
  intro a
  obtain ⟨b, hb, hba⟩ := H.exists_mem_eqLocus hnil a
  refine ⟨⟨b, hb⟩, FaithfulSMul.algebraMap_injective A B ?_⟩
  rw [H.algebraMap_toBase]
  exact hba

/-- **The kernel of `𝒪_Y → 𝒪_{Y₀}` is `𝒥_Y = 𝒥_X ∩ 𝒪_Y`**: an invariant function reduces to
zero on `Y₀` exactly when it lies in `J`. -/
theorem mem_ker_toBase_iff [Module.FaithfullyFlat A B] (b : RingHom.eqLocus s t) :
    b ∈ RingHom.ker H.toBase ↔ (b : B') ∈ RingHom.ker πB := by
  rw [RingHom.mem_ker, RingHom.mem_ker, ← H.algebraMap_toBase,
    ← (algebraMap A B).map_zero]
  exact (FaithfulSMul.algebraMap_injective A B).eq_iff.symm

/-- **The exact sequence `0 → 𝒥_Y → 𝒪_Y → 𝒪_{Y₀} → 0`** on the affine `Y₀`, for a nilpotent
`J`: the kernel of the surjection `toBase : A' → A` is the ideal `J ∩ A'`. -/
theorem ker_toBase_eq_and_surjective [Module.FaithfullyFlat A B]
    (hnil : IsNilpotent (RingHom.ker πB)) :
    RingHom.ker H.toBase = (RingHom.ker πB).comap (RingHom.eqLocus s t).subtype ∧
      Function.Surjective H.toBase :=
  ⟨Ideal.ext fun b => H.mem_ker_toBase_iff b, H.surjective_toBase hnil⟩

/-- **Page 5: the descent of `𝒥_X` to `𝒥_Y`**, for `J² = 0`: the canonical map
`I ⊗_{A'} B → J`, `i ⊗ πB b ↦ i b`, is bijective, where `A' = Ker(B' ⇉ C')` is the ring of
invariant functions on `X`, `I = J ∩ A'` the kernel of `toBase : A' → A`, and `B` an algebra over
`A' ⧸ I ≅ A`. This is the hypothesis `hJ` of `Folder126NilpotentQuotient`, derived. -/
theorem bijective_fibreTensorSMulHomToKer [Module.FaithfullyFlat A B]
    (hJ2 : RingHom.ker πB ^ 2 = ⊥) :
    letI : Algebra B' B := πB.toAlgebra
    letI : Algebra (RingHom.eqLocus s t) B := (πB.comp (RingHom.eqLocus s t).subtype).toAlgebra
    letI : Algebra (RingHom.eqLocus s t ⧸ RingHom.ker H.toBase) B :=
      ((algebraMap A B).comp
        (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)).toRingHom).toAlgebra
    haveI : IsScalarTower (RingHom.eqLocus s t) B' B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (RingHom.eqLocus s t) (RingHom.eqLocus s t ⧸ RingHom.ker H.toBase) B :=
      ⟨fun x y z => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        change algebraMap A B (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)
            (Ideal.Quotient.mk _ (x * y))) * z = πB x * (algebraMap A B
              (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)
                (Ideal.Quotient.mk _ y)) * z)
        rw [RingHom.quotientKerEquivOfSurjective_apply_mk,
          RingHom.quotientKerEquivOfSurjective_apply_mk, H.algebraMap_toBase,
          H.algebraMap_toBase, Subring.coe_mul, map_mul, mul_assoc]⟩
    Function.Bijective ((RingHom.ker H.toBase).fibreTensorSMulHomToKer B' B hJ2
      H.surjective_B) := by
  let : Algebra B' B := πB.toAlgebra
  let : Algebra (RingHom.eqLocus s t) B := (πB.comp (RingHom.eqLocus s t).subtype).toAlgebra
  let : Algebra (RingHom.eqLocus s t ⧸ RingHom.ker H.toBase) B :=
    ((algebraMap A B).comp
      (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)).toRingHom).toAlgebra
  have : IsScalarTower (RingHom.eqLocus s t) B' B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (RingHom.eqLocus s t) (RingHom.eqLocus s t ⧸ RingHom.ker H.toBase) B :=
    ⟨fun x y z => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      change algebraMap A B (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)
          (Ideal.Quotient.mk _ (x * y))) * z = πB x * (algebraMap A B
            (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)
              (Ideal.Quotient.mk _ y)) * z)
      rw [RingHom.quotientKerEquivOfSurjective_apply_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk, H.algebraMap_toBase,
        H.algebraMap_toBase, Subring.coe_mul, map_mul, mul_assoc]⟩
  have hJJ : RingHom.ker πB * RingHom.ker πB = ⊥ := by rw [← pow_two]; exact hJ2
  have hCC : RingHom.ker πC * RingHom.ker πC = ⊥ := by
    rw [H.ker_C_s]; exact Module.Descent.map_mul_self_eq_bot s _ hJJ
  have hDD : RingHom.ker πD * RingHom.ker πD = ⊥ := by
    rw [H.ker_D]; exact Module.Descent.map_mul_self_eq_bot f₂₃ _ hCC
  let : Module B (RingHom.ker πB) := Module.Descent.moduleOfSurjective πB H.surjective_B
    (Module.Descent.isTorsionBySet_self _ hJJ)
  let : Module A (RingHom.ker πB) := Module.compHom _ (algebraMap A B)
  have : IsScalarTower A B (RingHom.ker πB) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module (B ⊗[A] B) (RingHom.ker πC) := Module.Descent.moduleOfSurjective πC
    H.surjective_C (Module.Descent.isTorsionBySet_self _ hCC)
  let : Module A (RingHom.ker πC) := Module.compHom _ (algebraMap A (B ⊗[A] B))
  have : IsScalarTower A (B ⊗[A] B) (RingHom.ker πC) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module (B ⊗[A] (B ⊗[A] B)) (RingHom.ker πD) := Module.Descent.moduleOfSurjective πD
    H.surjective_D (Module.Descent.isTorsionBySet_self _ hDD)
  let : Module A (RingHom.ker πD) := Module.compHom _ (algebraMap A (B ⊗[A] (B ⊗[A] B)))
  have : IsScalarTower A (B ⊗[A] (B ⊗[A] B)) (RingHom.ker πD) := ⟨fun a x z => by
    change _ = algebraMap A (B ⊗[A] (B ⊗[A] B)) a • (x • z)
    rw [← mul_smul]
    congr 1
    exact Algebra.smul_def a x⟩
  have sB : ∀ (β : B') (n : RingHom.ker πB), πB β • n = β • n := fun β n =>
    Module.Descent.moduleOfSurjective_smul πB H.surjective_B _ β n
  have hL₃ : RingHom.ker πD = (RingHom.ker πB).map (f₂₃.comp t) := by
    rw [H.ker_D, H.ker_C_t, Ideal.map_map]
  have hL₁ : RingHom.ker πD = (RingHom.ker πB).map (f₁₂.comp s) := by
    rw [← Ideal.map_map, ← H.ker_C_s, H.ker_C_t, Ideal.map_map, H.f₁₂_t, ← Ideal.map_map,
      ← H.ker_C_s, H.ker_D]
  obtain ⟨M, hM, hbc⟩ := exists_isBaseChange_invariant_ideal (A₁ := A) (B₁ := B)
    (N := RingHom.ker πB) (J := RingHom.ker πC) (L := RingHom.ker πD) (p₁ := s) (p₂ := t)
    (δ := μ) (e₁₂ := f₁₂) (e₁₃ := f₁₃) (e₂₃ := f₂₃)
    (fun β => RingHom.congr_fun H.μ_s β) (fun β => RingHom.congr_fun H.μ_t β)
    (fun β => RingHom.congr_fun H.f₁₂_s β) (fun β => RingHom.congr_fun H.f₁₂_t β)
    (fun β => RingHom.congr_fun H.f₁₃_t β) H.flat_t (RingHom.Flat.comp H.flat_t H.flat_f₂₃)
    H.ker_C_s H.ker_C_t hL₁ hL₃ H.surjective_B H.surjective_C sB
    (fun γ y => Module.Descent.moduleOfSurjective_smul πC H.surjective_C _ γ y)
    (fun d z => Module.Descent.moduleOfSurjective_smul πD H.surjective_D _ d z)
    (fun β => RingHom.congr_fun H.comp_s β) (fun β => RingHom.congr_fun H.comp_t β)
    (fun γ => RingHom.congr_fun H.comp_f₁₂ γ) (fun γ => RingHom.congr_fun H.comp_f₁₃ γ)
    (fun γ => RingHom.congr_fun H.comp_f₂₃ γ)
  -- the invariant elements of `J` are the elements of `I = J ∩ A'`
  let toI : M →+ RingHom.ker H.toBase :=
    { toFun := fun m => ⟨⟨((m : RingHom.ker πB) : B'), (hM m).1 m.2⟩,
        (H.mem_ker_toBase_iff _).2 (m : RingHom.ker πB).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hsmul : ∀ (a' : RingHom.eqLocus s t) (m : M), toI (H.toBase a' • m) = a' • toI m := by
    intro a' m
    apply Subtype.ext
    apply Subtype.ext
    change (((H.toBase a' • (m : RingHom.ker πB) : RingHom.ker πB)) : B') =
      (a' : B') * ((m : RingHom.ker πB) : B')
    rw [← algebraMap_smul B (H.toBase a') (m : RingHom.ker πB), H.algebraMap_toBase, sB]
    rfl
  let g : B ⊗[A] M →+ RingHom.ker H.toBase ⊗[RingHom.eqLocus s t] B :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun m => toI m ⊗ₜ b)
        (fun m m' => by rw [map_add, TensorProduct.add_tmul]))
        (fun b b' => AddMonoidHom.ext fun m => TensorProduct.tmul_add _ _ _))
      (fun a b m => by
        obtain ⟨a', rfl⟩ := H.surjective_toBase ⟨2, hJ2⟩ a
        simp only [AddMonoidHom.mk'_apply]
        rw [hsmul, TensorProduct.smul_tmul]
        congr 1
        rw [Algebra.smul_def, Algebra.smul_def, H.algebraMap_toBase]
        rfl)
  have hg : ∀ (b : B) (m : M), g (b ⊗ₜ m) = toI m ⊗ₜ b := fun _ _ => rfl
  have hfg : ∀ z, (((RingHom.ker H.toBase).fibreTensorSMulHomToKer B' B hJ2 H.surjective_B
      (g z) : _) : B') = ((hbc.equiv z : RingHom.ker πB) : B') := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
      obtain ⟨b', rfl⟩ := H.surjective_B b
      rw [hg, IsBaseChange.equiv_tmul, Ideal.coe_fibreTensorSMulHomToKer_apply]
      erw [Ideal.fibreTensorSMulHom_tmul]
      rw [sB, Submodule.coe_smul, smul_eq_mul, mul_comm]
      rfl
    | add x y hx hy => rw [map_add, map_add, Submodule.coe_add, hx, hy, map_add,
        Submodule.coe_add]
  have hgs : Function.Surjective g := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul i b =>
      have hi : ((i : RingHom.eqLocus s t) : B') ∈ RingHom.ker πB :=
        (H.mem_ker_toBase_iff _).1 i.2
      refine ⟨b ⊗ₜ ⟨⟨_, hi⟩, (hM ⟨_, hi⟩).2 (i : RingHom.eqLocus s t).2⟩, ?_⟩
      rw [hg]
      rfl
    | add x y hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, map_add g u v⟩
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · obtain ⟨u, rfl⟩ := hgs x
    obtain ⟨v, rfl⟩ := hgs y
    have huv : u = v := by
      apply hbc.equiv.injective
      apply Subtype.ext
      rw [← hfg, ← hfg, hxy]
    rw [huv]
  · obtain ⟨z, hz⟩ := hbc.equiv.surjective ⟨(y : B'), y.2⟩
    refine ⟨g z, Subtype.ext ?_⟩
    rw [hfg, hz]

/-- `𝒥_Y² = 0`: the kernel `I = J ∩ A'` of `toBase` is square-zero when `J` is. -/
theorem ker_toBase_pow_two [Module.FaithfullyFlat A B] (hJ2 : RingHom.ker πB ^ 2 = ⊥) :
    RingHom.ker H.toBase ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  rw [Ideal.mem_bot]
  apply Subtype.ext
  have h := Ideal.mul_mem_mul ((H.mem_ker_toBase_iff x).1 hx) ((H.mem_ker_toBase_iff y).1 hy)
  rw [← pow_two, hJ2, Ideal.mem_bot] at h
  exact h

/-- `X₀` is flat over `Y₀ = Spec (A' ⧸ I)`, since `A' ⧸ I ≅ A` (`ker_toBase_eq_and_surjective`)
and `B` is flat over `A`. -/
theorem flat_quotient_ker_toBase [Module.FaithfullyFlat A B] (hJ2 : RingHom.ker πB ^ 2 = ⊥) :
    letI : Algebra (RingHom.eqLocus s t ⧸ RingHom.ker H.toBase) B :=
      ((algebraMap A B).comp
        (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)).toRingHom).toAlgebra
    Module.Flat (RingHom.eqLocus s t ⧸ RingHom.ker H.toBase) B := by
  let : Algebra (RingHom.eqLocus s t ⧸ RingHom.ker H.toBase) B :=
    ((algebraMap A B).comp
      (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)).toRingHom).toAlgebra
  exact RingHom.flat_algebraMap_iff.mp (RingHom.Flat.comp
    (RingHom.Flat.of_bijective
      (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)).bijective)
    (RingHom.flat_algebraMap_iff.mpr inferInstance))

/-- **Page 7, `X → Y` is flat**, with `Y = Spec A'` constructed as the ring of invariant
functions `A' = Ker(B' ⇉ C')`, for `J² = 0`. -/
theorem flat_eqLocus [Module.FaithfullyFlat A B] (hJ2 : RingHom.ker πB ^ 2 = ⊥) :
    Module.Flat (RingHom.eqLocus s t) B' := by
  let : Algebra B' B := πB.toAlgebra
  let : Algebra (RingHom.eqLocus s t) B := (πB.comp (RingHom.eqLocus s t).subtype).toAlgebra
  let : Algebra (RingHom.eqLocus s t ⧸ RingHom.ker H.toBase) B :=
    ((algebraMap A B).comp
      (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)).toRingHom).toAlgebra
  have : IsScalarTower (RingHom.eqLocus s t) B' B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (RingHom.eqLocus s t) (RingHom.eqLocus s t ⧸ RingHom.ker H.toBase) B :=
    ⟨fun x y z => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      change algebraMap A B (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)
          (Ideal.Quotient.mk _ (x * y))) * z = πB x * (algebraMap A B
            (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)
              (Ideal.Quotient.mk _ y)) * z)
      rw [RingHom.quotientKerEquivOfSurjective_apply_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk, H.algebraMap_toBase,
        H.algebraMap_toBase, Subring.coe_mul, map_mul, mul_assoc]⟩
  exact ((Ideal.bijective_fibreTensorSMulHomToKer_iff (RingHom.ker H.toBase) B' B
    (H.ker_toBase_pow_two hJ2) hJ2 H.surjective_B (H.flat_quotient_ker_toBase hJ2)).mp
      (H.bijective_fibreTensorSMulHomToKer hJ2)).1

/-- **Page 7, affine case, with `Y` constructed.** `Folder126NilpotentQuotient`'s
`flat_and_bijective_of_thickening` with its hypothesis on `I ⊗_{A'} B → J` discharged by
descent: for `A' = Ker(B' ⇉ C')`, `I = J ∩ A'` and a flat `B'`-algebra `C''` with an
`A'`-algebra map `φ : B' ⊗_{A'} B' → C''` bijective modulo `I`, the ring `B'` is flat over `A'`
and `φ` is bijective. -/
theorem flat_and_bijective [Module.FaithfullyFlat A B] (hJ2 : RingHom.ker πB ^ 2 = ⊥)
    {C'' : Type u} [CommRing C''] [Algebra (RingHom.eqLocus s t) C''] [Algebra B' C'']
    [IsScalarTower (RingHom.eqLocus s t) B' C''] [Module.Flat B' C'']
    (φ : B' ⊗[RingHom.eqLocus s t] B' →ₐ[RingHom.eqLocus s t] C'')
    (hφ : Function.Bijective
      (LinearMap.lTensor (RingHom.eqLocus s t ⧸ RingHom.ker H.toBase) φ.toLinearMap)) :
    Module.Flat (RingHom.eqLocus s t) B' ∧ Function.Bijective φ := by
  let : Algebra B' B := πB.toAlgebra
  let : Algebra (RingHom.eqLocus s t) B := (πB.comp (RingHom.eqLocus s t).subtype).toAlgebra
  let : Algebra (RingHom.eqLocus s t ⧸ RingHom.ker H.toBase) B :=
    ((algebraMap A B).comp
      (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)).toRingHom).toAlgebra
  have : IsScalarTower (RingHom.eqLocus s t) B' B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (RingHom.eqLocus s t) (RingHom.eqLocus s t ⧸ RingHom.ker H.toBase) B :=
    ⟨fun x y z => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      change algebraMap A B (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)
          (Ideal.Quotient.mk _ (x * y))) * z = πB x * (algebraMap A B
            (RingHom.quotientKerEquivOfSurjective (H.surjective_toBase ⟨2, hJ2⟩)
              (Ideal.Quotient.mk _ y)) * z)
      rw [RingHom.quotientKerEquivOfSurjective_apply_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk, H.algebraMap_toBase,
        H.algebraMap_toBase, Subring.coe_mul, map_mul, mul_assoc]⟩
  exact Folder126NilpotentQuotient.flat_and_bijective_of_thickening (RingHom.ker H.toBase)
    (H.ker_toBase_pow_two hJ2) hJ2 H.surjective_B (H.flat_quotient_ker_toBase hJ2)
    (H.bijective_fibreTensorSMulHomToKer hJ2) φ hφ

end IsThickenedNerve

end Nerve

end Grothendieck.Folder126NilpotentDescent

#print axioms Grothendieck.Folder126NilpotentDescent.exact_amitsur_one
#print axioms Grothendieck.Folder126NilpotentDescent.exists_isBaseChange_invariant_ideal
#print axioms Grothendieck.Folder126NilpotentDescent.IsThickenedNerve.ker_toBase_eq_and_surjective
#print axioms Grothendieck.Folder126NilpotentDescent.IsThickenedNerve.flat_and_bijective
