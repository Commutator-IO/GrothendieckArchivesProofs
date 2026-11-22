/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Torsion
import Grothendieck.Attr

/-!
# Folder 100: homomorphisms of abelian schemes, stated as propositions

Two open rows of the edition's list of findings (`src/content/findings.ts`) for folder 100:
`100-full-faithfulness-connected-components` and `100-proper-epimorphism-hom-descent`. Nothing
here is proved; a `def … : Prop` asserts nothing.

## Main definitions

* `ProperEpimorphismHomDescent` (`100-proper-epimorphism-hom-descent`): Lemma 1 of p. 22.
* `FullFaithfulnessConnectedComponents` (`100-full-faithfulness-connected-components`): the
  Corollary of p. 3, with `A[p^∞]` as the system of its levels `A[p^n]`.

## Implementation notes

Abelian schemes are `AlgebraicGeometry.IsAbelianScheme` of the Stacks library (commutative, flat,
proper group schemes of finite presentation whose fibres are abelian varieties), group objects in
`Over S`. The `p^n`-torsion `A[p^n]` is `CategoryTheory.GrpObj.torsion A (p ^ n)`, the kernel of
multiplication by `p^n`, with its inclusion `torsionι`. Base change of group schemes along an open
immersion `U → S` is the functor `(Over.pullback U.ι).mapGrp` of Mathlib.

## Not formalised

* Corollaries 2 and 3 of p. 24 (pull-back along `f` fully faithful on abelian schemes and on
  `p`-divisible groups): they go through the scheme of homomorphisms `Hom_gr(A, B)`, which Stacks
  does not construct, and through `p`-divisible groups, which neither library has.
* The sharpening of p. 20 (`v` algebraic once the closure of every associated point of `O_S` meets
  the algebraicity locus `S_v` in a point of characteristic `p`): it needs the closed subscheme
  `S_v` of the Lemma of p. 3, which the page does not prove and refers to « Invariants 1.2 »,
  unidentified.

## References

* A. Grothendieck, folder 100, pp. 3, 20, 22, 24 (findings
  `100-full-faithfulness-connected-components`, `100-proper-epimorphism-hom-descent`)
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.GrpObj

universe u

namespace OpenProblems.Findings.Folder100

/-- `O_S → f_*O_{S'}` is injective: the folder's « épimorphisme » (p. 22). -/
@[montpellier "100, 22"]
def IsSchematicEpi {S S' : Scheme.{u}} (f : S' ⟶ S) : Prop :=
  ∀ U : S.Opens, Function.Injective (f.app U)

/-- `100-proper-epimorphism-hom-descent` (folder 100, p. 22, Lemma 1). If `f : S' → S` is proper
between locally noetherian schemes and `O_S → f_*O_{S'}` is injective (no flatness, no universal
hypothesis), then for every formally unramified `S`-scheme `X` the diagram
`Hom_S(S, X) → Hom_S(S', X) ⇉ Hom_S(S'', X)`, `S'' = S' ×_S S'`, is exact: an `S`-morphism
`S' → X` whose two pullbacks to `S''` agree comes from a unique `S`-morphism `S → X`.

Status: candidate. The reading supplies the radiciality of `Spec 𝒜 → S`, the surjectivity of `f`
and the end of the proof of Corollary 1; with that, the lemma holds for `X` formally unramified
as the page states it. Whether this exactness for proper `f` under bare schematic dominance
(which is not stable under base change) is known remains to be checked against SGA 1 IX and
Rydh, « Submersions and effective descent of étale morphisms » (2010).

Choices: « propre » is an interlinear addition read with doubt; `Hom_S(S, X)` is the set of
sections of `X → S`. -/
@[montpellier "100, 22"]
def ProperEpimorphismHomDescent : Prop :=
  ∀ (S S' : Scheme.{u}) (f : S' ⟶ S) [IsLocallyNoetherian S] [IsLocallyNoetherian S']
    [IsProper f], IsSchematicEpi f →
    ∀ (X : Scheme.{u}) (p : X ⟶ S) [FormallyUnramified p] (g' : S' ⟶ X), g' ≫ p = f →
      pullback.fst f f ≫ g' = pullback.snd f f ≫ g' →
      ∃! g : S ⟶ X, g ≫ p = 𝟙 S ∧ f ≫ g = g'

/-- The restriction of group schemes over `S` to an open `U`. -/
noncomputable abbrev restrictGrp {S : Scheme.{u}} (U : S.Opens) :
    Grp (Over S) ⥤ Grp (Over (U : Scheme.{u})) :=
  (Over.pullback U.ι).mapGrp

/-- `100-full-faithfulness-connected-components` (folder 100, pp. 2–3, Corollary of p. 3). Let `S`
be locally noetherian, `U ⊆ S` open, `p` a prime with every residue characteristic on `S − U`
equal to `p`. If `U` meets every connected component of `S` (no normality, reducedness or
schematic density assumed), the functor `A ↦ (A_U, A[p^∞], id)` from abelian schemes over `S` to
triples is fully faithful: a homomorphism `w : A_U → B_U` and a compatible system of
homomorphisms `v_n : A[p^n] → B[p^n]` agreeing with `w` over `U` come from a unique homomorphism
`A → B`.

Status: candidate; to compare with Faltings–Chai (ch. I and V), de Jong (Invent. Math. 134,
1998), Messing (LNM 264). The Lemma it rests on (the closed subscheme `S_v`) is not proved on the
page; the Complément's justification by Serre–Tate and Krull is the reading's. The page joins
three inequivalent hypotheses (« `U` rencontre toutes les composantes connexes, i.e. `U` dense,
i.e. `prof_T(S) ≥ 1` »); the reading keeps the weakest, the one stated here.

Choices: `A[p^∞]` is the system of the `A[p^n]`, a morphism `A[p^∞] → B[p^∞]` a system of
homomorphisms `v_n` compatible with the inclusions `A[p^n] ⊆ A[p^{n+1}]` (stated through any
`j` over `A`, which is the inclusion); the third component `id` of the triple is the
identification of `(A_U)[p^n]` with `(A[p^n])_U`, used in the compatibility of `v_n` with `w`. -/
@[montpellier "100, 2–3"]
def FullFaithfulnessConnectedComponents : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (U : S.Opens) (p : ℕ), p.Prime →
    (∀ s : S, s ∉ U → ringChar (S.residueField s) = p) →
    (∀ s : S, ∃ s' ∈ connectedComponent s, s' ∈ U) →
    ∀ (A B : Over S) [GrpObj A] [GrpObj B] [IsAbelianScheme A] [IsAbelianScheme B]
      (w : (restrictGrp U).obj (.mk A) ⟶ (restrictGrp U).obj (.mk B))
      (v : ∀ n : ℕ, torsion A (p ^ n : ℤ) ⟶ torsion B (p ^ n : ℤ)),
      (∀ (n : ℕ) (j : (torsion A (p ^ n : ℤ)).X ⟶ (torsion A (p ^ (n + 1) : ℤ)).X),
        j ≫ torsionι A (p ^ (n + 1) : ℤ) = torsionι A (p ^ n : ℤ) →
          j ≫ (v (n + 1)).hom.hom ≫ torsionι B (p ^ (n + 1) : ℤ) =
            (v n).hom.hom ≫ torsionι B (p ^ n : ℤ)) →
      (∀ n : ℕ, (Over.pullback U.ι).map (torsionι A (p ^ n : ℤ)) ≫ w.hom.hom =
        (Over.pullback U.ι).map ((v n).hom.hom ≫ torsionι B (p ^ n : ℤ))) →
      ∃! f : Grp.mk A ⟶ Grp.mk B, (restrictGrp U).map f = w ∧
        ∀ n : ℕ, torsionι A (p ^ n : ℤ) ≫ f.hom.hom = (v n).hom.hom ≫ torsionι B (p ^ n : ℤ)

end OpenProblems.Findings.Folder100
