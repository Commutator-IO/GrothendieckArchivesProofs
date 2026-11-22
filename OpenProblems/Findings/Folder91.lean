/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib

/-!
# Folder 91: Weil restriction and centralisers, stated as propositions

Two open rows of the edition's list of findings (`src/content/findings.ts`) for folder 91:
`91-weil-restriction-finite-etale-criterion` and `91-centraliser-condition-R`. Nothing here is
proved; a `def … : Prop` asserts nothing.

For `t : T → S` and a `T`-scheme `X`, the Weil restriction `Res_{T/S}(X)` is written by its
functor of points on `S`-schemes, `S' ↦ Hom_T(S' ×_S T, X)` (`weilRestriction`); it « is finite
étale » when it is represented by a finite étale `S`-scheme. A morphism of such functors is finite
étale when each of its fibres over an `S'`-point is represented by a finite étale `S'`-scheme.
The number `ν(s)` of geometric points of `T_s` is the number of points of
`T ×_S Spec \bar{κ(s)}`, `\bar{κ(s)}` an algebraic closure of the residue field.

## Stated

* `WeilRestrictionFiniteEtaleTFAE` (`91-weil-restriction-finite-etale-criterion`): Corollary 3 of
  p. 53, the four conditions equivalent.
* `RelativeConnectedComponents` (same row): the finite étale `S`-scheme `π₀(T/S)` of pp. 55–58,
  in the reading's form.
* `CentraliserRepresentable` (`91-centraliser-condition-R`): the corollary of p. 9 for
  centralisers.

## Not stated, and what is missing

* The transporters `Transp_G(H, K)` and normalisers `Norm_G(H)` of the same corollary: « under
  the same hypotheses on `K` » rests on a partly uncertain reading (« de t.f. sur S » for `K`),
  so the hypotheses are not fixed; they are matched in print anyway (Romagny 2022, Cor. A.8).
* The theorem of p. 4 (the locus where a monomorphism of finite type into a flat `X` becomes an
  isomorphism is representable iff it commutes with adic limits): the row's claim is the
  corollary, and the theorem is the means.
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

universe u

namespace OpenProblems.Findings.Folder91

variable {S T : Scheme.{u}}

/-- The Weil restriction `Res_{T/S}(X)` as a functor on `S`-schemes:
`S' ↦ Hom_T(S' ×_S T, X)`. -/
noncomputable abbrev weilRestriction (t : T ⟶ S) (X : Over T) : (Over S)ᵒᵖ ⥤ Type u :=
  (Over.pullback t).op ⋙ yoneda.obj X

/-- The morphism `Res_{T/S}(g) : Res_{T/S}(X) → Res_{T/S}(Y)` induced by `g : X → Y`. -/
noncomputable abbrev weilRestrictionMap (t : T ⟶ S) {X Y : Over T} (g : X ⟶ Y) :
    weilRestriction t X ⟶ weilRestriction t Y :=
  Functor.whiskerLeft (Over.pullback t).op (yoneda.map g)

/-- An `S`-scheme is finite étale over `S`. -/
def IsFiniteEtaleOver (R : Over S) : Prop :=
  IsFinite R.hom ∧ Etale R.hom

/-- A functor on `S`-schemes is represented by a finite étale `S`-scheme. -/
def IsRepresentedFiniteEtale (F : (Over S)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ R : Over S, IsFiniteEtaleOver R ∧ Nonempty (yoneda.obj R ≅ F)

/-- A morphism `a : F ⟶ F'` of functors on `S`-schemes is represented by finite étale morphisms:
for every `S`-scheme `S'` and `y ∈ F'(S')`, the fibre product `F ×_{F'} S'` is represented by a
finite étale `S'`-scheme. -/
def IsRepresentedFiniteEtaleMap {F F' : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ F') : Prop :=
  ∀ (S' : Over S) (y : F'.obj (op S')), ∃ (R : Over S) (r : R ⟶ S'),
    IsFinite r.left ∧ Etale r.left ∧ ∃ e : yoneda.obj R ≅ pullback a (yonedaEquiv.symm y),
      e.hom ≫ pullback.snd _ _ = yoneda.map r

/-- The geometric point `Spec \bar{κ(s)} → S` at `s`, for an algebraic closure `\bar{κ(s)}` of the
residue field. -/
noncomputable abbrev algClosurePoint (S : Scheme.{u}) (s : S) :
    Spec (CommRingCat.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) _)) ≫ S.fromSpecResidueField s

/-- `ν(s)`, the number of geometric points of the fibre `T_s` (its separable degree, for `t`
finite). -/
noncomputable def geometricPointCount (t : T ⟶ S) (s : S) : ℕ :=
  Nat.card ↥(pullback t (algClosurePoint S s) : Scheme.{u})

/-- `91-weil-restriction-finite-etale-criterion` (folder 91, p. 53, Corollary 3). For
`T → S` finite locally free, the following are equivalent: (i) `ν(s)` is locally constant;
(ii) `Res_{T/S}` sends finite étale covers to finite étale covers; (iii) `Res_{T/S}(T')` is finite
étale for every finite étale `T'` over `T`; (iv) `Res_{T/S}(T ⊔ T)` is finite étale over `S`.

Status: candidate; to compare with Conrad–Gabber–Prasad A.5, BLR § 7.6 Prop. 5, EGA IV 6.8 and
18.2, and Ferrand, « Un foncteur norme » (1998). The page draws the chain
(i) ⇒ (ii) ⇒ (iii) ⇒ (iv) ⇒ (i) in the margin.

Choices: finite locally free is finite, flat and locally of finite presentation; in (ii) a finite
étale cover `X → Y` of `T`-schemes is a finite étale morphism, and its image is the morphism of
functors `Res(X) → Res(Y)`, asked to be represented by finite étale morphisms, since `Res(Y)`
need not be representable; `T ⊔ T` is the coproduct of `T` with itself over `T`. -/
def WeilRestrictionFiniteEtaleTFAE : Prop :=
  ∀ (S T : Scheme.{u}) (t : T ⟶ S) [IsFinite t] [Flat t] [LocallyOfFinitePresentation t],
    List.TFAE [IsLocallyConstant (geometricPointCount t),
      ∀ (X Y : Over T) (g : X ⟶ Y), IsFinite g.left → Etale g.left →
        IsRepresentedFiniteEtaleMap (weilRestrictionMap t g),
      ∀ X : Over T, IsFiniteEtaleOver X → IsRepresentedFiniteEtale (weilRestriction t X),
      IsRepresentedFiniteEtale (weilRestriction t (Over.mk (coprod.desc (𝟙 T) (𝟙 T))))]

/-- `91-weil-restriction-finite-etale-criterion` (folder 91, pp. 55–58), the relative `π₀`. For
`T → S` finite locally free with `ν(s)` locally constant, there are a finite étale `S`-scheme
`P = π₀(T/S)` and a surjective `S`-morphism `T → P` with geometrically connected fibres such that
every `S`-morphism from `T` to a finite étale `S`-scheme factors uniquely through `P`; then
`Res_{T/S}(T × I)` is the scheme of maps from `P` to `I`.

Status: as for `WeilRestrictionFiniteEtaleTFAE`. The pages do not suppose `ν` locally constant
here; the reading supplies it, without which `P` does not exist. The identification with the
relative `π₀`, the left-adjoint form and the corrected converse of p. 58 are the reading's; the
relative `π₀` of a finite locally free `T → S` is not given by Romagny 2.5.2 (fibres not reduced),
and this is the open part.

Choices: the reading's form, through the universal property among finite étale `S`-schemes
rather than through the functor `I ↦ Res_{T/S}(T × I)` on finite sets; geometrically connected
fibres are fibres over the geometric points `Spec \bar{κ(p)}` that are connected. -/
def RelativeConnectedComponents : Prop :=
  ∀ (S T : Scheme.{u}) (t : T ⟶ S) [IsFinite t] [Flat t] [LocallyOfFinitePresentation t],
    IsLocallyConstant (geometricPointCount t) →
    ∃ (P : Over S) (q : Over.mk t ⟶ P), IsFiniteEtaleOver P ∧ Surjective q.left ∧
      (∀ p : P.left, ConnectedSpace ↥(pullback q.left (algClosurePoint P.left p) : Scheme.{u})) ∧
      ∀ S' : Over S, IsFiniteEtaleOver S' → Function.Bijective fun h : P ⟶ S' => q ≫ h

/-- Condition (R) of p. 8 for a group scheme `H` over `S`: for every local scheme `T = Spec A`
over `S`, every open subgroup of `H_T` containing the special fibre (the fibre over the closed
point) is all of `H_T`. An open subgroup is an open `V` of `H_T` containing the unit section and
stable under `(a, b) ↦ a b⁻¹` on the points of `H_T` with values in `V`. -/
def SatisfiesConditionR {S : Scheme.{u}} (H : Grp (Over S)) : Prop :=
  ∀ (A : CommRingCat.{u}) [IsLocalRing A] (t : Spec A ⟶ S)
    (V : ((Over.pullback t).mapGrp.obj H).X.left.Opens),
    (∀ z, ((Over.pullback t).mapGrp.obj H).X.hom.base z = IsLocalRing.closedPoint A → z ∈ V) →
    Set.range (η[((Over.pullback t).mapGrp.obj H).X]).left.base ⊆ V →
    (∀ (T' : Over (Spec A)) (a b : T' ⟶ ((Over.pullback t).mapGrp.obj H).X),
      Set.range a.left.base ⊆ V → Set.range b.left.base ⊆ V →
        Set.range (a * b⁻¹).left.base ⊆ V) →
    V = ⊤

/-- The `T`-points of the centraliser `Cent_G(u)` of a homomorphism `u : H → G`: the `g ∈ G(T)`
commuting with `u(x)` for every `T' → T` and every `x ∈ H(T')`. -/
def centraliserPoints {S : Scheme.{u}} {H G : Grp (Over S)} (u : H ⟶ G) (T : Over S) :
    Set (T ⟶ G.X) :=
  {g | ∀ (T' : Over S) (h : T' ⟶ T) (x : T' ⟶ H.X),
    (h ≫ g) * (x ≫ u.hom.hom) = (x ≫ u.hom.hom) * (h ≫ g)}

/-- `91-centraliser-condition-R` (folder 91, pp. 4–9; the corollary of p. 9 for centralisers). For
`H` flat of finite type over a locally noetherian `S` satisfying condition (R), and `u : H → G` any
homomorphism of group schemes, `Cent_G(u)` is representable by a subscheme of `G`, closed if `G`
is separated.

Status: candidate. The connected-fibre case is matched: for `H` flat of finite presentation with
connected fibres, SGA 3 VI_B 6.9 d) with 6.2.4 e) (new edition), after Raynaud–Gruson 1971. What
remains is (R) itself: purity implies it (the pass's own step, unchecked), and whether (R) is
strictly weaker than purity for flat groups of finite type over a local noetherian base is the
open question.

Choices: a subscheme is an immersion `Z → G`, and representability says that the points of
`Cent_G(u)` are the points of `G` factoring through it; « plat » for `H` is in the page's own
interline on p. 9; « `T` local » is read as `T = Spec A` for a local ring `A`. -/
def CentraliserRepresentable : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (H G : Grp (Over S)) (u : H ⟶ G),
    Flat H.X.hom → LocallyOfFiniteType H.X.hom → QuasiCompact H.X.hom → SatisfiesConditionR H →
    ∃ (Z : Scheme.{u}) (i : Z ⟶ G.X.left), IsImmersion i ∧
      (IsSeparated G.X.hom → IsClosedImmersion i) ∧
      ∀ (T : Over S) (g : T ⟶ G.X), g ∈ centraliserPoints u T ↔ ∃ z : T.left ⟶ Z, z ≫ i = g.left

end OpenProblems.Findings.Folder91
