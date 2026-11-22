module

public import Grothendieck.AlgebraicGeometry.Folder126Descent
public import Grothendieck.AlgebraicGeometry.Folder126RadicialEtaleGlobal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridgeRelation
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal

@[expose] public noncomputable section

/-!
# Folder 126, pages 17–22: existence of the radicial–étale factorisation

Finding `126-radicial-etale-factorisation`, existence of `X^ét`, steps 3b and 3c. Let `Y` be
quasi-compact and quasi-separated (for instance affine) and `f : X ⟶ Y` finite and universally open
with exactly `n` geometric points in every geometric fibre. Then `f` factors as a universal
homeomorphism `X ⟶ X^ét` followed by a finite étale `X^ét ⟶ Y`
(`exists_radicial_etale_factorisation`). With the uniqueness of
`Grothendieck.Folder126RadicialEtaleGlobal`, this is the statement of pages 17–23 over a
quasi-compact and quasi-separated base; the noetherian hypothesis of page 17 is not used.

**The descent.** Step 3a gives an étale surjective `w : W ⟶ Y` with `W` affine and a factorisation
`T = X ×_Y W ⟶ Z ⟶ W`. Over `W ×_Y W` the two pullbacks `Z ×_Y W` and `W ×_Y Z` are both étale
targets of universal homeomorphisms from `X ×_Y W ×_Y W`, so the uniqueness of the
factorisation gives the gluing isomorphism `Θ`. Its cocycle condition is
`exists_transition_of_pullbackIso_of_rel` for the relation `SheetRel`, « the two points of `Z`
cut out the same sheet of `X` »: it is compatible with the gluing (`sheetRel_gluing`) and, with
the structure map to `W`, determines a point of `Z` (`eq_of_sheetRel`, through Stacks 0BTY's
`hom_ext_of_surjective`). The datum is effective by Stacks 02W8, `Z ⟶ W` being separated and
quasi-finite. The descended `X^ét ⟶ Y` is finite and étale by fpqc descent of both properties;
`X ⟶ X^ét` is descended along the effective epimorphism `T ⟶ X`, and it is a universal
homeomorphism by the criterion of `Grothendieck.Folder126GeometricPoints`, its geometric fibres
being those of `T ⟶ Z`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Grothendieck.Folder126GeometricPoints Grothendieck.Folder126EtaleSplitting

universe u

namespace Grothendieck.Folder126Existence

variable {X Y W T Z : Scheme.{u}}

/-- Two points `z₁, z₂ : S ⟶ Z` *cut out the same sheet*: they have the same image in `Y`, and a
point of `X` lifts to a point of `T` over `z₁` exactly when it lifts to one over `z₂`. -/
def SheetRel (a : T ⟶ X) (g : T ⟶ Z) (h : Z ⟶ W) (w : W ⟶ Y) {S : Scheme.{u}}
    (z₁ z₂ : S ⟶ Z) : Prop :=
  z₁ ≫ h ≫ w = z₂ ≫ h ≫ w ∧ ∀ {S' : Scheme.{u}} (s : S' ⟶ S) (x : S' ⟶ X),
    (∃ t : S' ⟶ T, t ≫ a = x ∧ t ≫ g = s ≫ z₁) ↔ (∃ t : S' ⟶ T, t ≫ a = x ∧ t ≫ g = s ≫ z₂)

section SheetRel

variable {a : T ⟶ X} {g : T ⟶ Z} {h : Z ⟶ W} {w : W ⟶ Y}

theorem SheetRel.comp {S S' : Scheme.{u}} (k : S' ⟶ S) {z₁ z₂ : S ⟶ Z}
    (hR : SheetRel a g h w z₁ z₂) : SheetRel a g h w (k ≫ z₁) (k ≫ z₂) := by
  refine ⟨by simp only [Category.assoc, hR.1], fun s x => ?_⟩
  simpa only [Category.assoc] using hR.2 (s ≫ k) x

theorem SheetRel.symm {S : Scheme.{u}} {z₁ z₂ : S ⟶ Z} (hR : SheetRel a g h w z₁ z₂) :
    SheetRel a g h w z₂ z₁ :=
  ⟨hR.1.symm, fun s x => (hR.2 s x).symm⟩

theorem SheetRel.trans {S : Scheme.{u}} {z₁ z₂ z₃ : S ⟶ Z} (h₁ : SheetRel a g h w z₁ z₂)
    (h₂ : SheetRel a g h w z₂ z₃) : SheetRel a g h w z₁ z₃ :=
  ⟨h₁.1.trans h₂.1, fun s x => (h₁.2 s x).trans (h₂.2 s x)⟩

variable {f : X ⟶ Y} {b : T ⟶ W}

/-- **A sheet and the structure map determine a point.** Two points of `Z` cutting out the same
sheet and with the same image in `W` are equal. -/
theorem eq_of_sheetRel (H : IsPullback a b f w) (hgh : g ≫ h = b) [UniversalHomeomorphism g]
    [Etale h] {S : Scheme.{u}} {z₁ z₂ : S ⟶ Z} (hR : SheetRel a g h w z₁ z₂)
    (hh : z₁ ≫ h = z₂ ≫ h) : z₁ = z₂ := by
  have : Surjective g := Stacks.Etale.surjective_of_universalHomeomorphism' g
  obtain ⟨t, ht₁, ht₂⟩ := (hR.2 (pullback.snd g z₁) (pullback.fst g z₁ ≫ a)).1
    ⟨pullback.fst g z₁, rfl, pullback.condition⟩
  have ht : t = pullback.fst g z₁ := by
    refine H.hom_ext ht₁ ?_
    rw [← hgh, ← Category.assoc, ht₂, Category.assoc, ← hh, ← Category.assoc,
      ← pullback.condition, Category.assoc]
  have hs : pullback.snd g z₁ ≫ z₁ = pullback.snd g z₁ ≫ z₂ := by
    rw [← pullback.condition, ← ht, ht₂]
  exact Stacks.Etale.hom_ext_of_surjective (pullback.snd g z₁)
    (pullback.snd g z₁).surjective h z₁ z₂ hh hs

end SheetRel

section Gluing

variable {f : X ⟶ Y} {w : W ⟶ Y} {a : T ⟶ X} {b : T ⟶ W} {g : T ⟶ Z} {h : Z ⟶ W}

/-- **The gluing isomorphism.** Over `W ×_Y W`, `Z ×_Y W` and `W ×_Y Z` are both étale targets of
universal homeomorphisms from `T ×_Y W`, so by the uniqueness of the factorisation they are
isomorphic over `W ×_Y W`; the isomorphism respects the sheets. -/
theorem exists_gluing (H : IsPullback a b f w) (hgh : g ≫ h = b) [UniversalHomeomorphism g]
    [Etale h] :
    ∃ Θ : pullback (h ≫ w) w ≅ pullback w (h ≫ w),
      Θ.hom ≫ pullback.fst w (h ≫ w) = pullback.fst (h ≫ w) w ≫ h ∧
      Θ.hom ≫ pullback.snd w (h ≫ w) ≫ h = pullback.snd (h ≫ w) w ∧
      SheetRel a g h w (Θ.hom ≫ pullback.snd w (h ≫ w)) (pullback.fst (h ≫ w) w) := by
  -- The second point of `T` over a point of `T ×_Y W`.
  have hT2 : (pullback.fst (b ≫ w) w ≫ a) ≫ f = pullback.snd (b ≫ w) w ≫ w := by
    rw [Category.assoc, H.w]; exact pullback.condition
  let t₂ : pullback (b ≫ w) w ⟶ T :=
    H.lift (pullback.fst (b ≫ w) w ≫ a) (pullback.snd (b ≫ w) w) hT2
  have ht₂a : t₂ ≫ a = pullback.fst (b ≫ w) w ≫ a := H.lift_fst _ _ _
  have ht₂b : t₂ ≫ b = pullback.snd (b ≫ w) w := H.lift_snd _ _ _
  -- The involution of `T ×_Y W` exchanging the two points of `W`.
  have hσ : t₂ ≫ b ≫ w = (pullback.fst (b ≫ w) w ≫ b) ≫ w := by
    rw [← Category.assoc, ht₂b, Category.assoc, ← pullback.condition]
  let σ : pullback (b ≫ w) w ⟶ pullback (b ≫ w) w :=
    pullback.lift t₂ (pullback.fst (b ≫ w) w ≫ b) hσ
  have hσf : σ ≫ pullback.fst (b ≫ w) w = t₂ := pullback.lift_fst _ _ _
  have hσs : σ ≫ pullback.snd (b ≫ w) w = pullback.fst (b ≫ w) w ≫ b := pullback.lift_snd _ _ _
  have hσσ : σ ≫ σ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hσf, Category.id_comp]
      refine H.hom_ext ?_ ?_
      · rw [Category.assoc, ht₂a, ← Category.assoc, hσf, ht₂a]
      · rw [Category.assoc, ht₂b, hσs]
    · rw [Category.assoc, hσs, ← Category.assoc, hσf, ht₂b, Category.id_comp]
  have : IsIso σ := ⟨⟨σ, hσσ, hσσ⟩⟩
  -- The two universal homeomorphisms and the two étale maps to `W ×_Y W`.
  have hGA : (pullback.fst (b ≫ w) w ≫ g) ≫ h ≫ w = pullback.snd (b ≫ w) w ≫ w := by
    rw [Category.assoc, ← Category.assoc g, hgh]; exact pullback.condition
  let GA : pullback (b ≫ w) w ⟶ pullback (h ≫ w) w :=
    pullback.lift (pullback.fst (b ≫ w) w ≫ g) (pullback.snd (b ≫ w) w) hGA
  have hGAf : GA ≫ pullback.fst (h ≫ w) w = pullback.fst (b ≫ w) w ≫ g := pullback.lift_fst _ _ _
  have hGAs : GA ≫ pullback.snd (h ≫ w) w = pullback.snd (b ≫ w) w := pullback.lift_snd _ _ _
  let GB : pullback (b ≫ w) w ⟶ pullback w (h ≫ w) := σ ≫ GA ≫ (pullbackSymmetry (h ≫ w) w).hom
  have hGBf : GB ≫ pullback.fst w (h ≫ w) = pullback.fst (b ≫ w) w ≫ b := by
    simp only [GB, Category.assoc, pullbackSymmetry_hom_comp_fst, hGAs, hσs]
  have hGBs : GB ≫ pullback.snd w (h ≫ w) = t₂ ≫ g := by
    simp only [GB, Category.assoc, pullbackSymmetry_hom_comp_snd]
    rw [hGAf, ← Category.assoc, hσf]
  let πA : pullback (h ≫ w) w ⟶ pullback w w :=
    pullback.lift (pullback.fst (h ≫ w) w ≫ h) (pullback.snd (h ≫ w) w)
      (by rw [Category.assoc]; exact pullback.condition)
  let πB : pullback w (h ≫ w) ⟶ pullback w w :=
    pullback.lift (pullback.fst w (h ≫ w)) (pullback.snd w (h ≫ w) ≫ h)
      (by rw [Category.assoc]; exact pullback.condition)
  have sqA : IsPullback GA (pullback.fst (b ≫ w) w) (pullback.fst (h ≫ w) w) g := by
    refine IsPullback.of_right ?_ hGAf (IsPullback.of_hasPullback (h ≫ w) w).flip
    rw [hGAs, ← Category.assoc, hgh]
    exact (IsPullback.of_hasPullback (b ≫ w) w).flip
  have sqπA : IsPullback πA (pullback.fst (h ≫ w) w) (pullback.fst w w) h := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback w w).flip
    rw [show πA ≫ pullback.snd w w = pullback.snd (h ≫ w) w from pullback.lift_snd _ _ _]
    exact (IsPullback.of_hasPullback (h ≫ w) w).flip
  have sqπB : IsPullback πB (pullback.snd w (h ≫ w)) (pullback.snd w w) h := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback w w)
    rw [show πB ≫ pullback.fst w w = pullback.fst w (h ≫ w) from pullback.lift_fst _ _ _]
    exact IsPullback.of_hasPullback w (h ≫ w)
  have : UniversalHomeomorphism GA := MorphismProperty.of_isPullback sqA.flip inferInstance
  have : Etale πA := MorphismProperty.of_isPullback sqπA.flip inferInstance
  have : Etale πB := MorphismProperty.of_isPullback sqπB.flip inferInstance
  have : UniversalHomeomorphism GB :=
    (MorphismProperty.cancel_left_of_respectsIso _ σ _).2
      ((MorphismProperty.cancel_right_of_respectsIso _ GA _).2 inferInstance)
  have hfac : GA ≫ πA = GB ≫ πB := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc,
        show πA ≫ pullback.fst w w = pullback.fst (h ≫ w) w ≫ h from pullback.lift_fst _ _ _,
        show πB ≫ pullback.fst w w = pullback.fst w (h ≫ w) from pullback.lift_fst _ _ _,
        ← Category.assoc, hGAf, hGBf, Category.assoc, hgh]
    · rw [Category.assoc, Category.assoc,
        show πA ≫ pullback.snd w w = pullback.snd (h ≫ w) w from pullback.lift_snd _ _ _,
        show πB ≫ pullback.snd w w = pullback.snd w (h ≫ w) ≫ h from pullback.lift_snd _ _ _,
        hGAs, ← Category.assoc, hGBs, Category.assoc, hgh, ht₂b]
  obtain ⟨Θ, ⟨hΘG, hΘπ⟩, -⟩ :=
    Grothendieck.Folder126RadicialEtaleGlobal.existsUnique_iso_of_factorisations GA πA GB πB hfac
  have hΘ1 : Θ.hom ≫ pullback.fst w (h ≫ w) = pullback.fst (h ≫ w) w ≫ h := by
    have := congrArg (· ≫ pullback.fst w w) hΘπ
    simpa [πA, πB] using this
  have hΘ2 : Θ.hom ≫ pullback.snd w (h ≫ w) ≫ h = pullback.snd (h ≫ w) w := by
    have := congrArg (· ≫ pullback.snd w w) hΘπ
    simpa [πA, πB] using this
  have hΘ2w : Θ.hom ≫ pullback.snd w (h ≫ w) ≫ h ≫ w = pullback.fst (h ≫ w) w ≫ h ≫ w :=
    ((reassoc_of% hΘ2) w).trans pullback.condition.symm
  refine ⟨Θ, hΘ1, hΘ2, ?_, fun {S'} s x => ⟨?_, ?_⟩⟩
  · simpa only [Category.assoc] using hΘ2w
  · rintro ⟨t₁, ht₁a, ht₁g⟩
    have hx : x ≫ f = (s ≫ pullback.fst (h ≫ w) w ≫ h) ≫ w := by
      calc x ≫ f = t₁ ≫ a ≫ f := by rw [← ht₁a, Category.assoc]
        _ = t₁ ≫ g ≫ h ≫ w := by rw [H.w, ← hgh, Category.assoc]
        _ = s ≫ Θ.hom ≫ pullback.snd w (h ≫ w) ≫ h ≫ w := by
          rw [← Category.assoc t₁ g, ht₁g]; simp only [Category.assoc]
        _ = (s ≫ pullback.fst (h ≫ w) w ≫ h) ≫ w := by rw [hΘ2w]; simp only [Category.assoc]
    let t₂' : S' ⟶ T := H.lift x (s ≫ pullback.fst (h ≫ w) w ≫ h) hx
    have hq : t₂' ≫ b ≫ w = (s ≫ pullback.snd (h ≫ w) w) ≫ w := by
      rw [← Category.assoc, H.lift_snd]; simp only [Category.assoc]; rw [pullback.condition]
    let q : S' ⟶ pullback (b ≫ w) w := pullback.lift t₂' (s ≫ pullback.snd (h ≫ w) w) hq
    have hqt : q ≫ t₂ = t₁ := by
      refine H.hom_ext ?_ ?_
      · rw [Category.assoc, ht₂a, ← Category.assoc, pullback.lift_fst, H.lift_fst, ht₁a]
      · rw [Category.assoc, ht₂b, pullback.lift_snd, ← hgh, ← Category.assoc, ht₁g,
          Category.assoc, Category.assoc, hΘ2]
    have hqB : q ≫ GB = s ≫ Θ.hom := by
      apply pullback.hom_ext
      · rw [Category.assoc, hGBf, ← Category.assoc, pullback.lift_fst, H.lift_snd,
          Category.assoc, hΘ1]
      · rw [Category.assoc, hGBs, ← Category.assoc, hqt, ht₁g, Category.assoc]
    have hqA : q ≫ GA = s := by
      rw [← cancel_mono Θ.hom, Category.assoc, hΘG, hqB]
    refine ⟨t₂', H.lift_fst _ _ _, ?_⟩
    rw [← hqA, Category.assoc, hGAf, ← Category.assoc, pullback.lift_fst]
  · rintro ⟨t₂', ht₂'a, ht₂'g⟩
    have hq : t₂' ≫ b ≫ w = (s ≫ pullback.snd (h ≫ w) w) ≫ w := by
      rw [← hgh, Category.assoc, ← Category.assoc t₂', ht₂'g, Category.assoc, Category.assoc,
        pullback.condition]
    let q : S' ⟶ pullback (b ≫ w) w := pullback.lift t₂' (s ≫ pullback.snd (h ≫ w) w) hq
    have hqA : q ≫ GA = s := by
      apply pullback.hom_ext
      · rw [Category.assoc, hGAf, ← Category.assoc, pullback.lift_fst, ht₂'g]
      · rw [Category.assoc, hGAs, pullback.lift_snd]
    refine ⟨q ≫ t₂, ?_, ?_⟩
    · rw [Category.assoc, ht₂a, ← Category.assoc, pullback.lift_fst, ht₂'a]
    · rw [Category.assoc, ← hGBs, ← hΘG, ← Category.assoc, ← Category.assoc, hqA,
        Category.assoc]

end Gluing

/-- A surjective, locally of finite type and quasi-compact morphism has a geometric point over
every geometric point. -/
theorem nonempty_geomFibre_of_surjective_of_locallyOfFiniteType (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [Surjective f] {K : Type u} [Field K]
    [IsAlgClosed K] (p : Spec (.of K) ⟶ Y) : Nonempty (GeomFibre f p) := by
  have : Surjective (pullback.snd f p) := inferInstance
  have : CompactSpace ↥(pullback f p) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f p)
  obtain ⟨z, -⟩ := (pullback.snd f p).surjective (IsLocalRing.closedPoint K)
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton isClosed_univ ⟨z, Set.mem_univ _⟩
  refine ⟨⟨pointOfClosedPoint (pullback.snd f p) x hx ≫ pullback.fst f p, ?_⟩⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
    Category.id_comp]

/-- **Folder 126, pages 17–22: the radicial–étale factorisation exists (qcqs base).** Let `Y` be
quasi-compact and quasi-separated and `f : X ⟶ Y` finite and universally open, with exactly `n`
geometric points in every geometric fibre. Then `f` factors as a universal homeomorphism `X ⟶ X^ét`
followed by a finite étale morphism `X^ét ⟶ Y`. -/
theorem exists_radicial_etale_factorisation [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsFinite f]
    [UniversallyOpen f] {n : ℕ} (hn : HasGeomDegree f n) :
    ∃ (E : Scheme.{u}) (g₀ : X ⟶ E) (h₀ : E ⟶ Y),
      UniversalHomeomorphism g₀ ∧ IsFinite h₀ ∧ Etale h₀ ∧ g₀ ≫ h₀ = f := by
  obtain ⟨W, w, hw, hws, hWa, T, a, b, H, Z, g, h, hg, hh, hhe, hgh⟩ :=
    Folder126Descent.exists_etale_cover_factorisation f hn
  obtain ⟨Θ, hΘ1, hΘ2, hΘ3⟩ := exists_gluing H hgh
  -- The descent datum and its effectivity (Stacks 02W8).
  obtain ⟨φ, hcoc, hact⟩ := exists_transition_of_pullbackIso_of_rel w h
    (fun {_} z₁ z₂ => SheetRel a g h w z₁ z₂) (fun k _ _ hR => hR.comp k)
    (fun _ _ hR => hR.symm) (fun _ _ _ h₁ h₂ => h₁.trans h₂) Θ hΘ1 hΘ2 hΘ3
    (fun _ _ hR hh' => Over.OverMorphism.ext (eq_of_sheetRel H hgh hR hh'))
  set D : DescentDatum w := DescentDatum.mk' (Over.mk h) φ hcoc
  have hactD : ∀ {Z₀ : Over Y} (v : Z₀ ⟶ (Over.map w).obj D.over) (x : Z₀ ⟶ Over.mk w),
      SheetRel a g h w (D.act v x).left v.left := hact
  obtain ⟨Q⟩ := DescentDatum.nonempty_descended_of_isEffective
    (DescentDatum.isEffective_of_isSeparated_of_locallyQuasiFinite D
      (show IsSeparated h from inferInstance) (show LocallyQuasiFinite h from inferInstance)
      (show LocallyOfFiniteType h from inferInstance))
  have hQ : IsPullback h Q.proj w Q.base.hom := Q.isPullback
  -- The descended morphism is finite étale.
  have hEt : Etale Q.base.hom :=
    Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.of_isPullback
      hQ ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have hFin : IsFinite Q.base.hom :=
    Space.isFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact.of_isPullback
      hQ ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  -- `X ⟶ X^ét`, descended along the effective epimorphism `a : T ⟶ X`.
  have : Flat a := MorphismProperty.of_isPullback H.flip inferInstance
  have : Surjective a := MorphismProperty.of_isPullback H.flip inferInstance
  have : QuasiCompact a := MorphismProperty.of_isPullback H.flip inferInstance
  have hcompat : ∀ {S : Scheme.{u}} (k₁ k₂ : S ⟶ T), k₁ ≫ a = k₂ ≫ a →
      k₁ ≫ g ≫ Q.proj = k₂ ≫ g ≫ Q.proj := by
    intro S k₁ k₂ hk
    have hY : (k₂ ≫ b) ≫ w = (k₁ ≫ g) ≫ h ≫ w := by
      rw [Category.assoc, ← H.w, ← Category.assoc, ← hk, Category.assoc, H.w, ← hgh]
      simp only [Category.assoc]
    let Z₀ : Over Y := Over.mk ((k₁ ≫ g) ≫ h ≫ w)
    let v : Z₀ ⟶ (Over.map w).obj D.over := Over.homMk (k₁ ≫ g) rfl
    let x : Z₀ ⟶ Over.mk w := Over.homMk (k₂ ≫ b) hY
    have hact1 : (D.act v x).left ≫ h = k₂ ≫ b := by
      have h1 := congrArg (fun m ↦ CommaMorphism.left m) (D.act_comp_structureMap v x)
      simp only [Over.comp_left] at h1
      exact h1
    obtain ⟨t', ht'a, ht'g⟩ :=
      ((hactD v x).2 (𝟙 _) (k₁ ≫ a)).2 ⟨k₁, rfl, (Category.id_comp _).symm⟩
    have ht' : t' = k₂ :=
      H.hom_ext (ht'a.trans hk)
        (by rw [← hgh, ← Category.assoc, ht'g, Category.id_comp, hact1, hgh])
    have hfinal : (D.act v x).left = k₂ ≫ g := by rw [← ht', ht'g, Category.id_comp]
    rw [← Category.assoc, ← Category.assoc k₂, ← hfinal, Q.proj_act v x]
    rfl
  let gd : X ⟶ Q.base.left := EffectiveEpi.desc a (g ≫ Q.proj) hcompat
  have hgd : a ≫ gd = g ≫ Q.proj := EffectiveEpi.fac a (g ≫ Q.proj) hcompat
  have hgdf : gd ≫ Q.base.hom = f := by
    rw [← cancel_epi a, ← Category.assoc, hgd, Category.assoc, ← hQ.w, ← Category.assoc, hgh,
      H.w]
  -- `T ⟶ Z` is the base change of `X ⟶ X^ét`.
  have hsq : IsPullback a g gd Q.proj := by
    refine IsPullback.of_bot ?_ hgd hQ.flip
    rw [hgh, hgdf]
    exact H
  have : IsFinite b := MorphismProperty.of_isPullback H inferInstance
  have : IsFinite g := by
    have : IsFinite (g ≫ h) := by rw [hgh]; infer_instance
    exact IsFinite.of_comp g h
  have hg1 := hasGeomDegree_one_of_universalHomeomorphism g
  have : IsIntegralHom (gd ≫ Q.base.hom) := by rw [hgdf]; infer_instance
  have : IsIntegralHom gd := IsIntegralHom.of_comp gd Q.base.hom
  have : LocallyOfFiniteType Q.proj := MorphismProperty.of_isPullback hQ inferInstance
  refine ⟨Q.base.left, gd, Q.base.hom,
    universalHomeomorphism_of_hasGeomDegree_one gd fun K _ _ p => ?_, hFin, hEt, hgdf⟩
  obtain ⟨⟨p', hp'⟩⟩ := nonempty_geomFibre_of_surjective_of_locallyOfFiniteType Q.proj p
  obtain ⟨e⟩ := hg1 K p'
  subst hp'
  exact ⟨(geomFibreEquivOfIsPullback hsq p').symm.trans e⟩

end Grothendieck.Folder126Existence
