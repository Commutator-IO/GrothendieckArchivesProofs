import Mathlib

/-!
# Folder 57: rigid subgroups, stated as a proposition

Two open rows of the edition's list of findings (`src/content/findings.ts`) for folder 57:
`57-rigid-subgroups-one-fibre` is stated, `57-generic-hyperplane-h1-injective` is not. Nothing
here is proved; a `def … : Prop` asserts nothing.

Group schemes over `S` are group objects in `Over S` (`Grp (Over S)`); a closed subgroup scheme
is a morphism of group objects whose underlying morphism of schemes is a closed immersion, and two
of them are equal as subschemes of `G` when their kernels (ideal sheaves, `Scheme.Hom.ker`) are
equal. The `n`-torsion of a group object `H` is the fibre of `n : H → H` over the unit; the
schematic closure of a family of closed subschemes is cut out by the infimum of their ideal
sheaves, so « the prime-to-`p` torsion is schematically dense » is the vanishing of that
infimum.

## Stated

* `RigidSubgroupsOneFibre` (`57-rigid-subgroups-one-fibre`): the Théorème de rigidité of p. 45.

## Not stated, and what is missing

* The corollaries of pp. 46–49 (homomorphisms out of a rigid group agreeing on one fibre; descent
  of rigid subgroups along fppf covers with geometrically connected fibres): not written out.
* `57-generic-hyperplane-h1-injective` (folder 57, pp. 98–99: injectivity of
  `H¹(X, G) → H¹(Y_K̄, G)` for the generic hyperplane section, `G = 𝐆_a` or finite commutative,
  and the corollary on `Pic^τ`): Mathlib has no generic hyperplane section of a projective
  variety over the algebraic closure of `k(t₁, …, t_r)`, no fppf cohomology with coefficients in
  `μ_p` or `α_p` on a scheme, and no `Pic^τ` of a projective variety (Stacks has Picard schemes
  of curves only). The row's scope also rests on uncertain readings (the description of `G` on
  p. 98, nearly every word of the p. 99 corollary), and the row itself suspects Corollary 1 fails
  in characteristic `p`; stating it before the facsimile is re-read would fix a reading the
  edition has not settled.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace OpenProblems.Findings.Folder57

/-- The geometric point `Spec \bar{κ(s)} → S` at `s`, for an algebraic closure of the residue
field. -/
noncomputable abbrev algClosurePoint (S : Scheme.{u}) (s : S) :
    Spec (CommRingCat.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) _)) ≫ S.fromSpecResidueField s

/-- The geometric fibre `H_{\bar s}` of a group scheme `H` over `S`, as a group scheme over
`Spec \bar{κ(s)}`. -/
noncomputable abbrev geomFibreGrp {S : Scheme.{u}} (H : Grp (Over S)) (s : S) :
    Grp (Over (Spec (CommRingCat.of (AlgebraicClosure (S.residueField s))))) :=
  (Over.pullback (algClosurePoint S s)).mapGrp.obj H

/-- The inclusion of the `n`-torsion `H[n] = Ker(n : H → H)` of a group object. -/
noncomputable abbrev torsionKer {C : Type*} [Category C] [CartesianMonoidalCategory C]
    [HasPullbacks C] (H : Grp C) (n : ℕ) : pullback ((𝟙 H.X) ^ n) η[H.X] ⟶ H.X :=
  pullback.fst _ _

/-- `n ≥ 1` is prime to the residue characteristic at `s` (every `n ≥ 1` when it is `0`). -/
def IsPrimeToChar (S : Scheme.{u}) (s : S) (n : ℕ) : Prop :=
  0 < n ∧ (ringChar (S.residueField s) = 0 ∨ n.Coprime (ringChar (S.residueField s)))

/-- A group scheme `H` over `S` is rigid (p. 42, as the reading reads it): commutative, flat, and
every geometric fibre `H_{\bar s}` is the schematic closure of its torsion prime to the residue
characteristic. -/
def IsRigidSubgroup {S : Scheme.{u}} (H : Grp (Over S)) : Prop :=
  Flat H.X.hom ∧ IsCommMonObj H.X ∧ ∀ s : S,
    ⨅ (n : ℕ) (_ : IsPrimeToChar S s n), (torsionKer (geomFibreGrp H s) n).left.ker = ⊥

/-- The ideal sheaf of the fibre at `s` of a subgroup `i : H → G`, in the fibre `G_s`. -/
noncomputable def fibreKer {S : Scheme.{u}} {H G : Grp (Over S)} (i : H ⟶ G) (s : S) :
    (pullback G.X.hom (S.fromSpecResidueField s)).IdealSheafData :=
  ((Over.pullback (S.fromSpecResidueField s)).map i.hom.hom).left.ker

/-- `57-rigid-subgroups-one-fibre` (folder 57, pp. 42–45, Théorème de rigidité). Let `S` be
locally noetherian and connected, and `G` a commutative group scheme of finite type over `S`. Two
rigid closed subgroup schemes of `G` that agree on one fibre are equal.

Status: unsearched; to compare with SGA 3 IX–X and XV (groups of multiplicative type) and Mumford,
GIT 6.1 (abelian schemes), both special cases of the notion. The proof refers to « démonstration
donnée plus haut » in the missing pages 1–3 and is not in the folder; the lemma of p. 44 (finite
étale subschemes of an unramified `S`-scheme agreeing at one point agree everywhere) is.

Choices: the definition of p. 42 is read with many illegible words; condition (ii) is fixed only
by its boxed `ℓ^k`-torsion of the geometric fibre, and the finiteness clause (iii) cannot be read
and is left out, so `IsRigidSubgroup` is the reading's « prime-to-`p` torsion dense ». `G` is taken
commutative (an illegible word after « schéma en groupes » on p. 45, read « comm. »; the row
gives a counterexample in `GL₂` without it). « Agree on one fibre » is equality of the fibres at
a point `s`, as subschemes of `G_s`. -/
def RigidSubgroupsOneFibre : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] [ConnectedSpace S] (G : Over S) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (H₁ H₂ : Grp (Over S)) (i₁ : H₁ ⟶ .mk G) (i₂ : H₂ ⟶ .mk G),
    IsClosedImmersion i₁.hom.hom.left → IsClosedImmersion i₂.hom.hom.left →
    IsRigidSubgroup H₁ → IsRigidSubgroup H₂ → (∃ s : S, fibreKer i₁ s = fibreKer i₂ s) →
    i₁.hom.hom.left.ker = i₂.hom.hom.left.ker

end OpenProblems.Findings.Folder57
