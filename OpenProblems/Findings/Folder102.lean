module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints
import Grothendieck.Attr

@[expose] public section

/-!
# Folder 102: an open-immersion criterion for functors, stated as a proposition

The open row `102-open-immersion-criterion` of the edition's list of findings
(`src/content/findings.ts`), folder 102, p. 12. Nothing here is proved; a `def … : Prop` asserts
nothing.

Functors on `S`-schemes are functors `(Over S)ᵒᵖ ⥤ Type u`. « Commutes with filtered colimits of
rings » is `AlgebraicGeometry.Scheme.IsLimitPreserving` of the Stacks library (Stacks 05LX:
`colim F(T_i) → F(lim T_i)` bijective for cofiltered systems of affine `S`-schemes). An fpqc sheaf
is a sheaf for the fpqc topology of Mathlib restricted to `Over S`. The other notions are written
out below.

## Stated

* `OpenImmersionCriterion`: the criterion of p. 12, as the reading reads it.

## Not stated

* Nothing else in the row; the struck third hypothesis (« `u` … épimorphisme ») is left out, as
  the page strikes it.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace OpenProblems.Findings.Folder102

variable {S : Scheme.{u}}

/-- `Spec B` as an `S`-scheme through `Spec A`, for a ring map `φ : A → B` and `t : Spec A → S`. -/
noncomputable abbrev specOverBase {A B : CommRingCat.{u}} (φ : A ⟶ B) (t : Spec A ⟶ S) : Over S :=
  Over.mk (Spec.map φ ≫ t)

/-- The `S`-morphism `Spec B → Spec A` given by `φ : A → B`. -/
noncomputable abbrev toSpecOver {A B : CommRingCat.{u}} (φ : A ⟶ B) (t : Spec A ⟶ S) :
    specOverBase φ t ⟶ Over.mk t :=
  Over.homMk (Spec.map φ) rfl

/-- The quotient map `A → A ⧸ I` in `CommRingCat`. -/
noncomputable abbrev idealQuotientHom {A : CommRingCat.{u}} (I : Ideal A) :
    A ⟶ CommRingCat.of (A ⧸ I) :=
  CommRingCat.ofHom (Ideal.Quotient.mk I)

/-- `u : G ⟶ F` is formally étale (the page's « infinitésimalement étale »): for every affine
`S`-scheme `T = Spec A` and square-zero ideal `I` of `A`, with `T₀ = Spec (A ⧸ I)`, the map
`G(T) → G(T₀) ×_{F(T₀)} F(T)` is bijective. -/
def IsFormallyEtaleMap {G F : (Over S)ᵒᵖ ⥤ Type u} (u : G ⟶ F) : Prop :=
  ∀ (A : CommRingCat.{u}) (I : Ideal A), I ^ 2 = ⊥ → ∀ (t : Spec A ⟶ S)
    (a : G.obj (op (specOverBase (idealQuotientHom I) t))) (b : F.obj (op (Over.mk t))),
    u.app _ a = F.map (toSpecOver (idealQuotientHom I) t).op b →
    ∃! c : G.obj (op (Over.mk t)),
      G.map (toSpecOver (idealQuotientHom I) t).op c = a ∧ u.app _ c = b

/-- The closed immersion `Spec (A ⧸ I^{n+1}) → Spec (A ⧸ I^{n+2})` over `S`. -/
noncomputable def adicTruncation {A : CommRingCat.{u}} (I : Ideal A) (n : ℕ) (t : Spec A ⟶ S) :
    specOverBase (idealQuotientHom (I ^ (n + 1))) t ⟶
      specOverBase (idealQuotientHom (I ^ (n + 2))) t :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (by omega) : I ^ (n + 2) ≤ I ^ (n + 1))))) (by
      simp only [specOverBase, Over.mk_hom, ← Spec.map_comp_assoc]; rfl)

/-- `F` commutes with adic limits of artinian rings: for every complete noetherian local ring
`(A, m)` over `S`, `F(Spec A) → lim_n F(Spec A/m^{n+1})` is bijective. -/
def CommutesWithAdicLimits (F : (Over S)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (A : CommRingCat.{u}) [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (t : Spec A ⟶ S)
    (x : ∀ n : ℕ,
      F.obj (op (specOverBase (idealQuotientHom (IsLocalRing.maximalIdeal A ^ (n + 1))) t))),
    (∀ n, F.map (adicTruncation _ n t).op (x (n + 1)) = x n) →
    ∃! y : F.obj (op (Over.mk t)),
      ∀ n, F.map (toSpecOver (idealQuotientHom (IsLocalRing.maximalIdeal A ^ (n + 1))) t).op y = x n

/-- `u : G ⟶ F` is an open immersion: for every `S`-scheme `T` and `b ∈ F(T)` there is an open
`V ⊆ T` such that an `S`-morphism `h : T' → T` pulls `b` back into the image of `G(T')` exactly
when `h` factors through `V`. For `u` a monomorphism this says that `G ×_F T` is represented by
the open subscheme `V`. -/
def IsOpenImmersionOfFunctors {G F : (Over S)ᵒᵖ ⥤ Type u} (u : G ⟶ F) : Prop :=
  ∀ (T : Over S) (b : F.obj (op T)), ∃ V : T.left.Opens, ∀ (T' : Over S) (h : T' ⟶ T),
    (∃ a : G.obj (op T'), u.app _ a = F.map h.op b) ↔ Set.range h.left.base ⊆ V

/-- `F` is a sheaf for the fpqc topology on `S`-schemes. -/
def IsFpqcSheaf (F : (Over S)ᵒᵖ ⥤ Type u) : Prop :=
  Presieve.IsSheaf (Scheme.fpqcTopology.over S) F

/-- `102-open-immersion-criterion` (folder 102, p. 12). Over a locally noetherian base `S`, a
monomorphism `u : G → F` of functors on `S`-schemes that is formally étale is an open immersion
as soon as `F` and `G` are fpqc sheaves commuting with filtered colimits of rings and with adic
limits of artinian rings.

Status: candidate. The page gives no proof (checked on the facsimile, #126); the whole proof is
the edition's, not re-checked step by step. Closest in print: Hall–Rydh, Theorem 10.3, after
Artin (1973, VII.7.2), which gives the conclusion for `S` excellent after base change; the
statement for a locally noetherian base was not found.

Choices: « infinitésimalement étale » is read as formally étale (lifting along square-zero
thickenings of affine schemes; unramifiedness is automatic for a monomorphism); « adiques » in
hypothesis (i) is an uncertain reading, taken as the completions of noetherian local rings at
their maximal ideals; « commuting with filtered colimits of rings » is Stacks' limit
preservation along cofiltered systems of affine `S`-schemes. -/
@[montpellier "102, 12"]
def OpenImmersionCriterion : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (G F : (Over S)ᵒᵖ ⥤ Type u) (u : G ⟶ F),
    (∀ T, Function.Injective (u.app T)) → IsFormallyEtaleMap u →
    IsFpqcSheaf F → IsFpqcSheaf G → Scheme.IsLimitPreserving S F → Scheme.IsLimitPreserving S G →
    CommutesWithAdicLimits F → CommutesWithAdicLimits G → IsOpenImmersionOfFunctors u

end OpenProblems.Findings.Folder102
