module

public import Grothendieck.Folder126Sheets
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.PurelyInseparableDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SingletonFibreGeometricPoint

@[expose] public noncomputable section

/-!
# Folder 126, pages 17–22: the radicial–étale factorisation exists étale-locally

Finding `126-radicial-etale-factorisation`, existence of `X^ét`, step 2. Let `f : X ⟶ Y` be finite
and universally open with exactly `n` geometric points in every geometric fibre (page 17's
hypotheses). Then every point `y` of `Y` has an étale neighbourhood `u : U ⟶ Y` over which the base
change of `f` factors as a universal homeomorphism followed by a finite étale morphism:
`exists_etale_local_factorisation`. Over `U` the second arrow is even the trivial cover
`∐_κ U ⟶ U`, with `|κ| = n`.

**The proof.** The fibre of `f` over `y` is finite and discrete. Stacks 02LO
(`exists_etaleNeighborhood_purelyInseparable_decomposition`) gives an étale neighbourhood `(E, e)`
of `y` over which `X ×_Y E` is the disjoint union of open-and-closed pieces: finite pieces `D k`,
each meeting the fibre over `e` in one point `v k` with purely inseparable residue extension, and
a residual piece with no point over `e` (because the pieces exhaust the fibre over `y`). The base
is then shrunk to the open neighbourhood `O` of `e` that misses the image of the residual piece
(closed, since a finite morphism is closed) and lies in the image of every `D k` (open, since `f`
is universally open; this is where universal openness enters). Over `O` the sheets `D k ∩ X_O`
are clopen, finite and surjective, and over the geometric point at `e` each has at most one
geometric point (`subsingleton_lift_of_preimage_singleton_of_isPurelyInseparable`). The counting
lemma of `Grothendieck.Folder126Sheets` then gives the factorisation.

The noetherian hypothesis of page 17 is not used.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Grothendieck.Folder126GeometricPoints Grothendieck.Folder126Sheets

universe u

namespace Grothendieck.Folder126EtaleSplitting

variable {X Y : Scheme.{u}}

/-- The geometric points of `T` over `p`, for a pullback square `T = X ×_Y U`, are those of `X`
over the image of `p`. -/
def geomFibreEquivOfIsPullback {T U : Scheme.{u}} {a : T ⟶ X} {b : T ⟶ U} {f : X ⟶ Y}
    {u : U ⟶ Y} (H : IsPullback a b f u) {K : Type u} [Field K] (p : Spec (.of K) ⟶ U) :
    GeomFibre b p ≃ GeomFibre f (p ≫ u) where
  toFun q := ⟨q.1 ≫ a, by rw [Category.assoc, H.w, ← Category.assoc, q.2]⟩
  invFun q := ⟨H.lift q.1 p q.2, H.lift_snd _ _ _⟩
  left_inv q := Subtype.ext (H.hom_ext (H.lift_fst _ _ _) ((H.lift_snd _ _ _).trans q.2.symm))
  right_inv q := Subtype.ext (H.lift_fst _ _ _)

/-- The degree of the geometric fibres is stable under base change, along any pullback square. -/
theorem hasGeomDegree_of_isPullback {T U : Scheme.{u}} {a : T ⟶ X} {b : T ⟶ U} {f : X ⟶ Y}
    {u : U ⟶ Y} (H : IsPullback a b f u) {n : ℕ} (hf : HasGeomDegree f n) : HasGeomDegree b n :=
  fun K _ _ p => (hf K _).map fun e => (geomFibreEquivOfIsPullback H p).trans e

/-- A point of an open subscheme lies in the open. -/
theorem ι_apply_mem {S : Scheme.{u}} (V : S.Opens) (w : V) : V.ι w ∈ V := w.2

/-- Pure inseparability of a residue extension, read without the transport along an equality of
points. -/
theorem isPurelyInseparable_of_residueFieldCongr {E V : Scheme.{u}} (g : E ⟶ V) (z : E) (v : V)
    (h : g z = v)
    (hp : ((V.residueFieldCongr h).inv ≫ g.residueFieldMap z).hom.IsPurelyInseparable) :
    (g.residueFieldMap z).hom.IsPurelyInseparable := by
  subst h
  simpa using hp

/-- **Folder 126, the factorisation exists étale-locally.** Let `f : X ⟶ Y` be finite and
universally open, with exactly `n` geometric points in every geometric fibre. Every point `y` of
`Y` has an affine étale neighbourhood `u : U ⟶ Y` such that the base change `T = X ×_Y U ⟶ U` (any
pullback square) factors as a universal homeomorphism `T ⟶ Z` followed by a finite étale
`Z ⟶ U`. -/
theorem exists_etale_local_factorisation (f : X ⟶ Y) [IsFinite f] [UniversallyOpen f] {n : ℕ}
    (hn : HasGeomDegree f n) (y : Y) :
    ∃ (U : Scheme.{u}) (u : U ⟶ Y), Etale u ∧ IsAffine U ∧ y ∈ Set.range u ∧
      ∃ (T : Scheme.{u}) (a : T ⟶ X) (b : T ⟶ U), IsPullback a b f u ∧
        ∃ (Z : Scheme.{u}) (g : T ⟶ Z) (h : Z ⟶ U),
          UniversalHomeomorphism g ∧ IsFinite h ∧ Etale h ∧ g ≫ h = b := by
  classical
  -- The fibre over `y` is finite and discrete.
  have : Finite (f.fiber y) := by
    have : Finite (f ⁻¹' {y}) := (f.finite_preimage_singleton y).to_subtype
    exact Finite.of_equiv _ (f.fiberHomeo y).symm.toEquiv
  let N := Nat.card (f.fiber y)
  let x : Fin N → f.fiber y := (Finite.equivFin (f.fiber y)).symm
  have hx : Function.Injective x := (Finite.equivFin _).symm.injective
  have hxs : Function.Surjective x := (Finite.equivFin _).symm.surjective
  have hiso : ∀ i, IsIsolatedPoint (x i) := fun i => isOpen_discrete _
  -- Stacks 02LO.
  obtain ⟨E, m, D, v, hdisj, hcover, hclopen, hpieces, hnone⟩ :=
    exists_etaleNeighborhood_purelyInseparable_decomposition f N y x hx hiso
  let P : Scheme.{u} := pullback f E.toBase
  let p : P ⟶ E.scheme := pullback.snd f E.toBase
  -- The residual piece has no point over the distinguished point.
  have hnone' : ∀ w ∈ D none, p w ≠ E.point := by
    intro w hw hwp
    have hc : (pullback.fst f E.toBase ≫ f) w = (pullback.snd f E.toBase ≫ E.toBase) w := by
      rw [pullback.condition]
    simp only [Scheme.Hom.comp_apply] at hc
    have hfy : f (pullback.fst f E.toBase w) = y := by
      rw [hc]
      change E.toBase (p w) = y
      rw [hwp, E.map_point]
    obtain ⟨z, hz⟩ : pullback.fst f E.toBase w ∈ Set.range (f.fiberι y) := by
      rw [Scheme.Hom.range_fiberι]; exact hfy
    obtain ⟨i, rfl⟩ := hxs z
    exact hnone ⟨w, hw⟩ hwp i hz.symm
  -- Shrinking the base.
  let κ := Σ i, Fin (m i)
  let C : Set E.scheme := p '' (D none : Set P)
  have hC : IsClosed C := p.isClosedMap _ (hclopen none).isClosed
  have hpC : E.point ∉ C := by
    rintro ⟨w, hw, hwp⟩
    exact hnone' w hw hwp
  let I : κ → Set E.scheme := fun k => p '' (D (some k) : Set P)
  have hI : ∀ k, IsOpen (I k) := fun k => p.isOpenMap _ (D (some k)).isOpen
  have hpI : ∀ k, E.point ∈ I k := fun k =>
    ⟨(D (some k)).ι (v k.1 k.2), ι_apply_mem _ _,
      (Scheme.Hom.comp_apply _ _ _).symm.trans (hpieces k.1 k.2).2.2.2.choose⟩
  let O₀ : E.scheme.Opens := ⟨Cᶜ ∩ ⋂ k, I k, hC.isOpen_compl.inter (isOpen_iInter_of_finite hI)⟩
  have hO₀ : E.point ∈ O₀ := ⟨hpC, Set.mem_iInter.2 hpI⟩
  -- An affine open neighbourhood inside it.
  obtain ⟨O, hOaff, hO, hOle⟩ : ∃ O : E.scheme.Opens, O ∈ E.scheme.affineOpens ∧ E.point ∈ O ∧
      O ≤ O₀ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp E.scheme.isBasis_affineOpens hO₀
  have : IsAffine (O : Scheme.{u}) := hOaff
  -- The new base, its base change and the pullback square.
  let u : (O : Scheme.{u}) ⟶ Y := O.ι ≫ E.toBase
  let b : (p ⁻¹ᵁ O : Scheme.{u}) ⟶ O := p ∣_ O
  have H : IsPullback ((p ⁻¹ᵁ O).ι ≫ pullback.fst f E.toBase) b f u :=
    (isPullback_morphismRestrict p O).flip.paste_horiz (IsPullback.of_hasPullback f E.toBase)
  have hb : IsFinite b := inferInstance
  have hbn : HasGeomDegree b n := hasGeomDegree_of_isPullback H hn
  have hbι : b ≫ O.ι = (p ⁻¹ᵁ O).ι ≫ p := morphismRestrict_ι p O
  -- The sheets over `O`.
  let W : κ → (p ⁻¹ᵁ O : Scheme.{u}).Opens := fun k => (p ⁻¹ᵁ O).ι ⁻¹ᵁ D (some k)
  have hWdisj : ∀ k l, k ≠ l → Disjoint (W k) (W l) := by
    intro k l hkl
    have hs : Disjoint (D (some k) : Set P) (D (some l)) :=
      hdisj (Set.mem_univ _) (Set.mem_univ _) fun h => hkl (Option.some_injective _ h)
    rw [disjoint_iff, eq_bot_iff]
    rintro t ⟨htk, htl⟩
    exact (Set.disjoint_iff.1 hs ⟨htk, htl⟩).elim
  have hWcov : ∀ t, ∃ k, t ∈ W k := by
    intro t
    have hmem : (p ⁻¹ᵁ O).ι t ∈ ⋃ k, (D k).1 := by
      rw [hcover]; trivial
    obtain ⟨k', hk'⟩ := Set.mem_iUnion.1 hmem
    cases k' with
    | none =>
      exact ((hOle ((ι_apply_mem (p ⁻¹ᵁ O) t) : p ((p ⁻¹ᵁ O).ι t) ∈ O)).1 ⟨_, hk', rfl⟩).elim
    | some k => exact ⟨k, hk'⟩
  have hWclosed : ∀ k, IsClosed (W k : Set (p ⁻¹ᵁ O : Scheme.{u})) := fun k =>
    (hclopen (some k)).isClosed.preimage (p ⁻¹ᵁ O).ι.continuous
  have : ∀ k, IsClosedImmersion (W k).ι := fun k =>
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hWclosed k)
  have hfin : ∀ k, IsFinite ((W k).ι ≫ b) := fun k => inferInstance
  have hsurj : ∀ k, Surjective ((W k).ι ≫ b) := by
    intro k
    refine ⟨fun o => ?_⟩
    obtain ⟨w, hw, hwo⟩ := Set.mem_iInter.1 (hOle o.2).2 k
    have hwO : w ∈ p ⁻¹ᵁ O := by
      change p w ∈ O
      rw [hwo]; exact o.2
    refine ⟨⟨⟨w, hwO⟩, hw⟩, ?_⟩
    apply O.ι.isOpenEmbedding.injective
    have e : ((W k).ι ≫ b ≫ O.ι) ⟨⟨w, hwO⟩, hw⟩ =
        ((W k).ι ≫ (p ⁻¹ᵁ O).ι ≫ p) ⟨⟨w, hwO⟩, hw⟩ := by rw [hbι]
    exact e.trans hwo
  -- The geometric point at the distinguished point.
  let o₀ : (O : Scheme.{u}) := ⟨E.point, hO⟩
  let L := AlgebraicClosure ((O : Scheme.{u}).residueField o₀)
  let φ : (O : Scheme.{u}).residueField o₀ ⟶ CommRingCat.of L :=
    CommRingCat.ofHom (algebraMap ((O : Scheme.{u}).residueField o₀) L)
  let p₀ : Spec (.of L) ⟶ O := Spec.map φ ≫ (O : Scheme.{u}).fromSpecResidueField o₀
  have hp₀pt : (p₀ ≫ O.ι) (IsLocalRing.closedPoint L) = E.point := by
    have h1 : p₀ (IsLocalRing.closedPoint L) = o₀ :=
      Scheme.fromSpecResidueField_apply o₀ ((Spec.map φ) (IsLocalRing.closedPoint L))
    change O.ι (p₀ (IsLocalRing.closedPoint L)) = E.point
    rw [h1]
    rfl
  have hp₀ : ∀ k, Subsingleton (GeomFibre ((W k).ι ≫ b) p₀) := by
    intro k
    let g := (D (some k)).ι ≫ p
    obtain ⟨hgfin, hfib, -, hvu, hpure⟩ := hpieces k.1 k.2
    have hpure' := isPurelyInseparable_of_residueFieldCongr g _ _ hvu hpure
    have hfib' : g.base ⁻¹' {g.base (v k.1 k.2)} = {v k.1 k.2} := by
      rw [show g.base (v k.1 k.2) = E.point from hvu]; exact hfib
    have hsub := subsingleton_lift_of_preimage_singleton_of_isPurelyInseparable g (v k.1 k.2)
      hfib' (p₀ ≫ O.ι) (hp₀pt.trans hvu.symm) hpure'
    -- Each geometric point of the sheet `W k` is one of `D (some k)`.
    have hlift : ∀ q : GeomFibre ((W k).ι ≫ b) p₀, ∃ q' : Spec (.of L) ⟶ D (some k),
        q' ≫ (D (some k)).ι = q.1 ≫ (W k).ι ≫ (p ⁻¹ᵁ O).ι := fun q =>
      exists_lift_of_mem (q.1 ≫ (W k).ι ≫ (p ⁻¹ᵁ O).ι) (D (some k)) (ι_mem (W k) q.1)
    refine ⟨fun q₁ q₂ => Subtype.ext ?_⟩
    obtain ⟨q₁', h₁⟩ := hlift q₁
    obtain ⟨q₂', h₂⟩ := hlift q₂
    have hq : ∀ (q : GeomFibre ((W k).ι ≫ b) p₀) (q' : Spec (.of L) ⟶ D (some k)),
        q' ≫ (D (some k)).ι = q.1 ≫ (W k).ι ≫ (p ⁻¹ᵁ O).ι → q' ≫ g = p₀ ≫ O.ι := by
      intro q q' hq'
      change q' ≫ (D (some k)).ι ≫ p = p₀ ≫ O.ι
      rw [← Category.assoc, hq', Category.assoc, Category.assoc, ← hbι,
        ← Category.assoc ((W k).ι), ← Category.assoc, q.2]
    have := congrArg Subtype.val (hsub.elim ⟨q₁', hq q₁ q₁' h₁⟩ ⟨q₂', hq q₂ q₂' h₂⟩)
    have h12 : q₁.1 ≫ (W k).ι ≫ (p ⁻¹ᵁ O).ι = q₂.1 ≫ (W k).ι ≫ (p ⁻¹ᵁ O).ι := by
      rw [← h₁, ← h₂]; exact congrArg (· ≫ (D (some k)).ι) this
    simp only [← Category.assoc] at h12
    exact (cancel_mono _).1 ((cancel_mono _).1 h12)
  -- The counting lemma.
  obtain ⟨g, hg, hgh⟩ := exists_factorisation_of_sheets b hWdisj hWcov hbn p₀ hp₀
  exact ⟨O, u, inferInstance, inferInstance, ⟨o₀, E.map_point⟩, _, _, b, H, _, g, fold O κ, hg,
    inferInstance, etale_sigmaDesc _ fun _ => inferInstance, hgh⟩

end Grothendieck.Folder126EtaleSplitting
