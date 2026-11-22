module

public import Grothendieck.AlgebraicGeometry.Folder126GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaDescent

@[expose] public noncomputable section

/-!
# Folder 126, pages 17–22: a split finite morphism is radicial followed by trivial étale

Finding `126-radicial-etale-factorisation`, existence of `X^ét`, the counting step. Let
`b : T ⟶ O` be finite with exactly `n` geometric points in every geometric fibre, and let `T` be
the disjoint union of open *sheets* `W k` (`k` in a finite type `κ`), each finite and surjective
over `O`. If at one geometric point `p₀` of `O` every sheet has at most one geometric point, then
every sheet has exactly one geometric point over every geometric point of `O`, so `|κ| = n`, and
`b` factors as a universal homeomorphism `T ⟶ ∐_κ O` followed by the trivial finite étale cover
`∐_κ O ⟶ O`. This is the shape of pages 17–22 after an étale base change: there the sheets are
the pieces `Spec Bᵢ` of the local splitting.

**Results.**
* `sigmaGeomFibreEquiv`: the geometric points of `T` over `p` are the disjoint union, over the
  sheets, of the geometric points of the sheets (a field has one point, so a geometric point of
  `T` lies in exactly one sheet).
* `hasGeomDegree_one_of_sheets`: the counting argument.
* `exists_factorisation_of_sheets`: the factorisation, with the first arrow glued from the sheets
  (`Scheme.Cover.glueMorphisms`), a universal homeomorphism by
  `universalHomeomorphism_of_hasGeomDegree_one`, and the second the fold map
  `Sigma.desc (fun _ => 𝟙 O)`, finite (Stacks 0CYI, `isFinite_sigmaDesc`) and étale
  (`etale_sigmaDesc`).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Grothendieck.Folder126GeometricPoints

universe u

namespace Grothendieck.Folder126Sheets

/-- A type with at most one and at least one element is in bijection with `Fin 1`. -/
theorem nonempty_equiv_fin_one {α : Type*} [Subsingleton α] (a : α) : Nonempty (α ≃ Fin 1) :=
  ⟨Equiv.ofBijective (fun _ => (0 : Fin 1))
    ⟨fun a b _ => Subsingleton.elim a b, fun _ => ⟨a, Subsingleton.elim _ _⟩⟩⟩

variable {T O : Scheme.{u}} (b : T ⟶ O) {κ : Type} (W : κ → T.Opens)

/-- A morphism from the spectrum of a field factors through every open containing its point. -/
theorem exists_lift_of_mem {K : Type u} [Field K] (q : Spec (.of K) ⟶ T) (V : T.Opens)
    (hq : q (IsLocalRing.closedPoint K) ∈ V) : ∃ q₁ : Spec (.of K) ⟶ V, q₁ ≫ V.ι = q := by
  have hsub : Set.range q.base ⊆ Set.range V.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim z (IsLocalRing.closedPoint K)]
    exact hq
  exact ⟨IsOpenImmersion.lift V.ι q hsub, IsOpenImmersion.lift_fac _ _ _⟩

theorem ι_mem {K : Type u} [Field K] (V : T.Opens) (q : Spec (.of K) ⟶ V) :
    (q ≫ V.ι) (IsLocalRing.closedPoint K) ∈ V := by
  have : (q ≫ V.ι) (IsLocalRing.closedPoint K) ∈ Set.range V.ι.base := ⟨_, rfl⟩
  rwa [Scheme.Opens.range_ι] at this

variable {W}

/-- **The geometric points of `T` are the disjoint union of those of the sheets.** -/
def sigmaGeomFibreEquiv (hdisj : ∀ k l, k ≠ l → Disjoint (W k) (W l))
    (hcov : ∀ x : T, ∃ k, x ∈ W k) {K : Type u} [Field K] (p : Spec (.of K) ⟶ O) :
    (Σ k, GeomFibre ((W k).ι ≫ b) p) ≃ GeomFibre b p :=
  Equiv.ofBijective (fun x => ⟨x.2.1 ≫ (W x.1).ι, by rw [Category.assoc]; exact x.2.2⟩) <| by
    refine ⟨?_, fun q => ?_⟩
    · rintro ⟨k, q₁⟩ ⟨l, q₂⟩ h
      have h : q₁.1 ≫ (W k).ι = q₂.1 ≫ (W l).ι := congrArg Subtype.val h
      obtain rfl : k = l := by
        by_contra hkl
        have hk := ι_mem (W k) q₁.1
        have hl := ι_mem (W l) q₂.1
        rw [← h] at hl
        exact Set.disjoint_iff.1 (by simpa using (hdisj k l hkl)) ⟨hk, hl⟩
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext ((cancel_mono _).1 h)))
    · obtain ⟨k, hk⟩ := hcov (q.1 (IsLocalRing.closedPoint K))
      obtain ⟨q₁, hq₁⟩ := exists_lift_of_mem q.1 (W k) hk
      exact ⟨⟨k, ⟨q₁, by rw [← Category.assoc, hq₁]; exact q.2⟩⟩, Subtype.ext hq₁⟩

/-- **The counting argument.** If `b` has exactly `n` geometric points over every geometric point,
every sheet is finite and surjective, and at one geometric point `p₀` every sheet has at most one
geometric point, then every sheet has exactly one geometric point over every geometric point. -/
theorem hasGeomDegree_one_of_sheets [Fintype κ] (hdisj : ∀ k l, k ≠ l → Disjoint (W k) (W l))
    (hcov : ∀ x : T, ∃ k, x ∈ W k) {n : ℕ} (hn : HasGeomDegree b n)
    [hfin : ∀ k, IsFinite ((W k).ι ≫ b)] [hsurj : ∀ k, Surjective ((W k).ι ≫ b)]
    {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] (p₀ : Spec (.of K₀) ⟶ O)
    (hp₀ : ∀ k, Subsingleton (GeomFibre ((W k).ι ≫ b) p₀)) (k : κ) :
    HasGeomDegree ((W k).ι ≫ b) 1 := by
  -- The number of geometric points of `b` is the sum of those of the sheets.
  have hsum : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ O),
      (∀ k, Finite (GeomFibre ((W k).ι ≫ b) p)) ∧
        ∑ k, Nat.card (GeomFibre ((W k).ι ≫ b) p) = n := by
    intro K _ _ p
    obtain ⟨e⟩ := hn K p
    let E := (sigmaGeomFibreEquiv b hdisj hcov p).trans e
    have : Finite (Σ k, GeomFibre ((W k).ι ≫ b) p) := Finite.of_equiv _ E.symm
    have hfk : ∀ k, Finite (GeomFibre ((W k).ι ≫ b) p) := fun k =>
      Finite.of_injective (Sigma.mk (β := fun k => GeomFibre ((W k).ι ≫ b) p) k) sigma_mk_injective
    refine ⟨hfk, ?_⟩
    rw [← Nat.card_sigma, Nat.card_congr E, Nat.card_fin]
  have hpos : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ O) (k : κ),
      1 ≤ Nat.card (GeomFibre ((W k).ι ≫ b) p) := fun K _ _ p k =>
    have := (hsum K p).1 k
    Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨nonempty_geomFibre_of_surjective _ p, this⟩)
  -- At `p₀` every sheet has exactly one point, so there are `n` sheets.
  have hcard : Fintype.card κ = n := by
    rw [← (hsum K₀ p₀).2, Fintype.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (Nat.card_eq_one_iff_unique.2 ⟨hp₀ k, nonempty_geomFibre_of_surjective _ p₀⟩).symm
  intro K _ _ p
  obtain ⟨hfk, hs⟩ := hsum K p
  have hle : ∀ l ∈ Finset.univ, 1 ≤ Nat.card (GeomFibre ((W l).ι ≫ b) p) :=
    fun l _ => hpos K p l
  have heq : ∑ l, Nat.card (GeomFibre ((W l).ι ≫ b) p) = ∑ _l : κ, 1 := by
    rw [hs, ← hcard, Fintype.card_eq_sum_ones]
  have hk : Nat.card (GeomFibre ((W k).ι ≫ b) p) = 1 :=
    ((Finset.sum_eq_sum_iff_of_le hle).1 heq.symm k (Finset.mem_univ _)).symm
  exact ⟨(Finite.equivFin _).trans (finCongr hk)⟩

/-- The trivial finite étale cover `∐_κ O ⟶ O`. -/
abbrev fold (O : Scheme.{u}) (κ : Type) : (∐ fun _ : κ => O) ⟶ O :=
  Sigma.desc fun _ => 𝟙 O

/-- Two morphisms from the spectrum of a field into different components of `∐_κ O` differ. -/
theorem eq_of_comp_sigmaι_eq {K : Type u} [Field K] {k l : κ} (a c : Spec (.of K) ⟶ O)
    (h : a ≫ Sigma.ι (fun _ : κ => O) l = c ≫ Sigma.ι (fun _ : κ => O) k) : l = k := by
  have := congrArg (fun φ : Spec (.of K) ⟶ ∐ fun _ : κ => O => φ (IsLocalRing.closedPoint K)) h
  simp only at this
  exact congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 this)

/-- **The factorisation of a split finite morphism.** Under the hypotheses of the counting
argument, `b` factors as a universal homeomorphism followed by the fold map `∐_κ O ⟶ O`, which
is finite and étale. -/
theorem exists_factorisation_of_sheets [Fintype κ] (hdisj : ∀ k l, k ≠ l → Disjoint (W k) (W l))
    (hcov : ∀ x : T, ∃ k, x ∈ W k) {n : ℕ} (hn : HasGeomDegree b n) [IsFinite b]
    [hfin : ∀ k, IsFinite ((W k).ι ≫ b)] [hsurj : ∀ k, Surjective ((W k).ι ≫ b)]
    {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] (p₀ : Spec (.of K₀) ⟶ O)
    (hp₀ : ∀ k, Subsingleton (GeomFibre ((W k).ι ≫ b) p₀)) :
    ∃ g : T ⟶ ∐ fun _ : κ => O, UniversalHomeomorphism g ∧ g ≫ fold O κ = b := by
  have hone := hasGeomDegree_one_of_sheets b hdisj hcov hn p₀ hp₀
  have hW : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨k, hk⟩ := hcov x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩
  let 𝒰 := T.openCoverOfIsOpenCover W hW
  let φ : ∀ k, 𝒰.X k ⟶ ∐ fun _ : κ => O := fun k => (W k).ι ≫ b ≫ Sigma.ι (fun _ : κ => O) k
  have hφ : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ φ k = pullback.snd (𝒰.f k) (𝒰.f l) ≫ φ l := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      have : pullback.fst (𝒰.f k) (𝒰.f k) = pullback.snd (𝒰.f k) (𝒰.f k) :=
        (cancel_mono (𝒰.f k)).1 pullback.condition
      rw [this]
    · have : IsEmpty ↥(pullback (𝒰.f k) (𝒰.f l)) := by
        refine ⟨fun z => ?_⟩
        have h₁ : (pullback.fst (𝒰.f k) (𝒰.f l) ≫ (W k).ι) z ∈ W k := by
          have : (pullback.fst (𝒰.f k) (𝒰.f l) ≫ (W k).ι) z ∈ Set.range (W k).ι.base :=
            ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
          rwa [Scheme.Opens.range_ι] at this
        have h₂ : (pullback.snd (𝒰.f k) (𝒰.f l) ≫ (W l).ι) z ∈ W l := by
          have : (pullback.snd (𝒰.f k) (𝒰.f l) ≫ (W l).ι) z ∈ Set.range (W l).ι.base :=
            ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
          rwa [Scheme.Opens.range_ι] at this
        have hc : pullback.fst (𝒰.f k) (𝒰.f l) ≫ (W k).ι =
            pullback.snd (𝒰.f k) (𝒰.f l) ≫ (W l).ι := pullback.condition
        rw [← hc] at h₂
        exact Set.disjoint_iff.1 (by simpa using hdisj k l hkl) ⟨h₁, h₂⟩
      exact (isInitialOfIsEmpty).hom_ext _ _
  let g : T ⟶ ∐ fun _ : κ => O := 𝒰.glueMorphisms φ hφ
  have hιg : ∀ k, (W k).ι ≫ g = (W k).ι ≫ b ≫ Sigma.ι (fun _ : κ => O) k := fun k =>
    𝒰.ι_glueMorphisms φ hφ k
  have hgh : g ≫ fold O κ = b := by
    refine 𝒰.hom_ext _ _ fun (k : κ) => ?_
    change (W k).ι ≫ g ≫ fold O κ = (W k).ι ≫ b
    rw [← Category.assoc, hιg]
    simp [fold]
  refine ⟨g, ?_, hgh⟩
  have : IsIntegralHom (g ≫ fold O κ) := by rw [hgh]; infer_instance
  have : IsIntegralHom g := IsIntegralHom.of_comp g (fold O κ)
  refine universalHomeomorphism_of_hasGeomDegree_one g fun K _ _ p => ?_
  -- `p` lands in one component `k` of `∐_κ O`.
  obtain ⟨k, o, ho⟩ : ∃ (k : κ) (o : O),
      Sigma.ι (fun _ : κ => O) k o = p (IsLocalRing.closedPoint K) :=
    (sigmaOpenCover fun _ : κ => O).exists_eq _
  have hsub : Set.range p.base ⊆ Set.range (Sigma.ι (fun _ : κ => O) k).base := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
    exact ⟨o, ho⟩
  let p' : Spec (.of K) ⟶ O := IsOpenImmersion.lift (Sigma.ι (fun _ : κ => O) k) p hsub
  have hp' : p' ≫ Sigma.ι (fun _ : κ => O) k = p := IsOpenImmersion.lift_fac _ _ _
  -- Every geometric point of `T` over `p` is a geometric point of the sheet `k` over `p'`.
  have hdesc : ∀ q : GeomFibre g p, ∃ q₁ : GeomFibre ((W k).ι ≫ b) p', q₁.1 ≫ (W k).ι = q.1 := by
    intro q
    obtain ⟨l, hl⟩ := hcov (q.1 (IsLocalRing.closedPoint K))
    obtain ⟨q₁, hq₁⟩ := exists_lift_of_mem q.1 (W l) hl
    have h₁ : (q₁ ≫ (W l).ι ≫ b) ≫ Sigma.ι (fun _ : κ => O) l =
        p' ≫ Sigma.ι (fun _ : κ => O) k := by
      rw [hp', ← q.2, ← hq₁]
      simp only [Category.assoc, hιg]
    obtain rfl := eq_of_comp_sigmaι_eq _ _ h₁
    exact ⟨⟨q₁, (cancel_mono _).1 h₁⟩, hq₁⟩
  have hsub' := (hone k K p').elim fun e => e.subsingleton
  have : Subsingleton (GeomFibre g p) := ⟨fun q q' => by
    obtain ⟨q₁, hq₁⟩ := hdesc q
    obtain ⟨q₁', hq₁'⟩ := hdesc q'
    exact Subtype.ext (by rw [← hq₁, ← hq₁', Subsingleton.elim q₁ q₁'])⟩
  obtain ⟨e⟩ := hone k K p'
  let q₁ := e.symm 0
  refine nonempty_equiv_fin_one ⟨q₁.1 ≫ (W k).ι, ?_⟩
  rw [Category.assoc, hιg, ← Category.assoc ((W k).ι) b, ← Category.assoc, q₁.2, hp']

end Grothendieck.Folder126Sheets
