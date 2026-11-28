/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Order.Basic
import Grothendieck.Attr

/-!
# Folder 27, pages 28–31: the inequalities (1)–(10) of the semicontinuity theorem, the arithmetic

Finding `27-semicontinuity-proof`. Page 28 fixes the invariants of a smooth connected group `G`
over an algebraically closed field through its Chevalley decomposition
`e → H → G → A → e` (`H = G_aff` affine smooth connected, `A` abelian): `d = dim G`,
`ρ_ab = dim A`, `d_aff = dim H`, `ρ_r` the dimension of the maximal tori, `ρ_ss` the semisimple
rank, `d_ss = dim H/rad H`, `d_rad = dim rad H`, `ρ_na`, `ρ_u = ρ_na − ρ_r`, `ρ_n` the dimension of
the Cartan subgroups, with

`ρ_na = ρ_r + ρ_u`, `ρ_n = ρ_na + ρ_ab`, `d_aff = d_ss + d_rad`, `d = ρ_ab + d_aff`

(the names are those of page 29, as in the edition's reading). Page 29 numbers the invariants
(1) `ρ_ab`, (2) `ρ_rig = ρ_r + ρ_ab`, (3) `ρ_ss`, (4) `d_ss`, (5) `ρ_n`, (6) `ρ_u`, (7) `ρ_na`,
(8) `d_aff`, (9) `d_rad`, (10) `d_radaff`, and writes the implications

`(2) + (5) ⇒ (6)`, `(1) + (5) ⇒ (7)`, `(1) ⇔ (8)`, `(3) ⇔ (9)`, `(1) + (3) ⇒ (10)`.

Page 31 states the theorem and, over a trait with closed point `s₀` (unprimed) and generic point
`s₁` (primed), the inequalities (1) `ρ_ab ≤ ρ′_ab`, (2) `ρ_ab + ρ_r ≤ ρ′_ab + ρ′_r`,
(3) `ρ_s ≤ ρ′_s`, (5) `ρ_n ≥ ρ′_n`, (6) `ρ_u ≥ ρ′_u`, (7) `ρ_na ≥ ρ′_na`, `ρ_aff ≥ ρ′_aff` (that is
(8)) and `d ≥ d′`, which page 32 a) reduces to `d = d′`.

**The group theory is not formalised.** Group schemes, the Chevalley decomposition, tori, Cartan
subgroups, radicals and the semicontinuity theorem itself are not; the invariants of the two
fibres are natural numbers (`Invariants`), the identities of page 28 are **hypotheses**
(`Chevalley`), and so is `d = d′`. What is proved is which implications of page 29 follow from
them by arithmetic (`omega`), and counterexample values for those that do not.

## Main definitions

* `Invariants`: the ten numbers `d, ρ_ab, d_aff, ρ_r, ρ_ss, d_ss, d_rad, ρ_na, ρ_u, ρ_n`.
* `Chevalley G`: the four identities of page 28.
* `ineq1`, …, `ineq9`: the inequalities (1)–(9) between the special fibre `G₀` and the generic
  fibre `G₁`. Pages 29 and 31 do not write the directions of (4) and (9); they are taken from the
  columns of page 29, lower semicontinuity (`≤`) for (1)–(4), upper (`≥`) for (5)–(10).

## Main results

* `ineq6_of_ineq2_ineq5`, `ineq7_of_ineq1_ineq5`, `ineq1_iff_ineq8` (p. 29, p. 32 a)): the first
  three implications of page 29 hold.
* `not_ineq3_imp_ineq9`, `not_ineq9_imp_ineq3` (p. 29): **`(3) ⇔ (9)` does not follow** from the
  identities of page 28 and `d = d′`, in either direction. The values are those of actual groups:
  `SL₃` against `SL₂ × SL₂ × 𝔾_a²`, and `SL₂ × SL₂ × 𝔾_a³` against `SL₂ × 𝔾_a × E` for an
  abelian variety `E` of dimension `5`. (No claim is made that a family with these fibres
  exists.)
* `ineq9_of_ineq1_ineq4`: what the identities do give for (9) is `(1) + (4) ⇒ (9)`.
* `dRadAff`, `ineq10_iff_ineq4`, `not_ineq1_ineq3_imp_ineq10`,
  `not_ineq1_ineq3_imp_ineq10_ge` (p. 29): `d_radaff` is not defined on the pages; reading the
  braces of page 29 (« sous `d` s'accolent `d_ss` et `d_radaff` ») as `d = d_ss + d_radaff`,
  (10) is equivalent to (4), and `(1) + (3) ⇒ (10)` fails for either direction of (10).

## Not formalised

* Everything group-theoretic above, the reduction to a trait (which takes the invariants locally
  constructible), the proofs of pp. 32–36 (Cartan subgroups through the `H(n)`, the cyclotomic
  character), and the inequality chain of p. 36 for `ρ_ss`.

## References

* A. Grothendieck, folder 27, pp. 28–31 (finding `27-semicontinuity-proof`)
-/

@[expose] public section

namespace Grothendieck.Folder27

/-- The invariants of page 28 of a smooth connected group over an algebraically closed field. -/
structure Invariants where
  /-- `d = dim G`. -/
  d : ℕ
  /-- `ρ_ab = dim A`, the abelian rank. -/
  rhoAb : ℕ
  /-- `d_aff = dim H`, the dimension of the affine part (`ρ_aff` on p. 28). -/
  dAff : ℕ
  /-- `ρ_r`, the dimension of the maximal tori. -/
  rhoR : ℕ
  /-- `ρ_ss`, the semisimple rank (`ρ_s`, `ρ_rs` on p. 28). -/
  rhoSs : ℕ
  /-- `d_ss = dim H/rad H` (`d_s` on p. 28). -/
  dSs : ℕ
  /-- `d_rad = dim rad H` (`ρ_rad` in « `ρ_aff = ρ_ss + ρ_rad` », p. 28). -/
  dRad : ℕ
  /-- `ρ_na`, the dimension of the affine part of a Cartan subgroup. -/
  rhoNa : ℕ
  /-- `ρ_u`, the unipotent rank. -/
  rhoU : ℕ
  /-- `ρ_n`, the dimension of the Cartan subgroups, the nilpotent rank. -/
  rhoN : ℕ

/-- The identities of page 28. -/
structure Chevalley (G : Invariants) : Prop where
  /-- `ρ_na = ρ_r + ρ_u`. -/
  na_eq : G.rhoNa = G.rhoR + G.rhoU
  /-- `ρ_n = ρ_na + ρ_ab`. -/
  n_eq : G.rhoN = G.rhoNa + G.rhoAb
  /-- `ρ_aff = ρ_ss + ρ_rad`, i.e. `d_aff = d_ss + d_rad`. -/
  aff_eq : G.dAff = G.dSs + G.dRad
  /-- `dim G = ρ_ab + ρ_aff`. -/
  d_eq : G.d = G.rhoAb + G.dAff

variable (G₀ G₁ : Invariants)

/-- (1) `ρ_ab ≤ ρ′_ab`. -/
abbrev ineq1 : Prop := G₀.rhoAb ≤ G₁.rhoAb
/-- (2) `ρ_ab + ρ_r ≤ ρ′_ab + ρ′_r`. -/
abbrev ineq2 : Prop := G₀.rhoAb + G₀.rhoR ≤ G₁.rhoAb + G₁.rhoR
/-- (3) `ρ_ss ≤ ρ′_ss`. -/
abbrev ineq3 : Prop := G₀.rhoSs ≤ G₁.rhoSs
/-- (4) `d_ss ≤ d′_ss` (direction from the column of page 29). -/
abbrev ineq4 : Prop := G₀.dSs ≤ G₁.dSs
/-- (5) `ρ_n ≥ ρ′_n`. -/
abbrev ineq5 : Prop := G₁.rhoN ≤ G₀.rhoN
/-- (6) `ρ_u ≥ ρ′_u`. -/
abbrev ineq6 : Prop := G₁.rhoU ≤ G₀.rhoU
/-- (7) `ρ_na ≥ ρ′_na`. -/
abbrev ineq7 : Prop := G₁.rhoNa ≤ G₀.rhoNa
/-- (8) `d_aff ≥ d′_aff` (`ρ_aff ≥ ρ′_aff`, p. 31). -/
abbrev ineq8 : Prop := G₁.dAff ≤ G₀.dAff
/-- (9) `d_rad ≥ d′_rad` (direction from the column of page 29). -/
abbrev ineq9 : Prop := G₁.dRad ≤ G₀.dRad

variable {G₀ G₁}

/-- `27-semicontinuity-proof` (folder 27, p. 29): `(2) + (5) ⇒ (6)`. -/
@[montpellier "27, 29"]
theorem ineq6_of_ineq2_ineq5 (h₀ : Chevalley G₀) (h₁ : Chevalley G₁) (h2 : ineq2 G₀ G₁)
    (h5 : ineq5 G₀ G₁) : ineq6 G₀ G₁ := by
  cases h₀; cases h₁; omega

/-- `27-semicontinuity-proof` (folder 27, p. 29): `(1) + (5) ⇒ (7)`. -/
@[montpellier "27, 29"]
theorem ineq7_of_ineq1_ineq5 (h₀ : Chevalley G₀) (h₁ : Chevalley G₁) (h1 : ineq1 G₀ G₁)
    (h5 : ineq5 G₀ G₁) : ineq7 G₀ G₁ := by
  cases h₀; cases h₁; omega

/-- `27-semicontinuity-proof` (folder 27, pp. 29, 32 a)): with `d = d′`, `(1) ⇔ (8)`. -/
@[montpellier "27, 29, 32"]
theorem ineq1_iff_ineq8 (h₀ : Chevalley G₀) (h₁ : Chevalley G₁) (hd : G₀.d = G₁.d) :
    ineq1 G₀ G₁ ↔ ineq8 G₀ G₁ := by
  cases h₀; cases h₁; omega

/-- With `d = d′`, `(1) + (4) ⇒ (9)`: this, not `(3) ⇒ (9)`, is what the identities of page 28
give for the dimension of the radical. -/
@[montpellier "27, 28, 29"]
theorem ineq9_of_ineq1_ineq4 (h₀ : Chevalley G₀) (h₁ : Chevalley G₁) (hd : G₀.d = G₁.d)
    (h1 : ineq1 G₀ G₁) (h4 : ineq4 G₀ G₁) : ineq9 G₀ G₁ := by
  cases h₀; cases h₁; omega

/-- The invariants of `SL₃`. -/
def exSL3 : Invariants :=
  { d := 8, rhoAb := 0, dAff := 8, rhoR := 2, rhoSs := 2, dSs := 8, dRad := 0, rhoNa := 2,
    rhoU := 0, rhoN := 2 }

/-- The invariants of `SL₂ × SL₂ × 𝔾_a²`. -/
def exSL2SL2Ga2 : Invariants :=
  { d := 8, rhoAb := 0, dAff := 8, rhoR := 2, rhoSs := 2, dSs := 6, dRad := 2, rhoNa := 4,
    rhoU := 2, rhoN := 4 }

/-- The invariants of `SL₂ × SL₂ × 𝔾_a³`. -/
def exSL2SL2Ga3 : Invariants :=
  { d := 9, rhoAb := 0, dAff := 9, rhoR := 2, rhoSs := 2, dSs := 6, dRad := 3, rhoNa := 5,
    rhoU := 3, rhoN := 5 }

/-- The invariants of `SL₂ × 𝔾_a × E`, `E` an abelian variety of dimension `5`. -/
def exSL2GaE5 : Invariants :=
  { d := 9, rhoAb := 5, dAff := 4, rhoR := 1, rhoSs := 1, dSs := 3, dRad := 1, rhoNa := 2,
    rhoU := 1, rhoN := 7 }

/-- `27-semicontinuity-proof` (folder 27, p. 29): `(3) ⇒ (9)` does not follow from the
identities of page 28 and `d = d′`: special fibre `SL₃`, generic fibre `SL₂ × SL₂ × 𝔾_a²`
(`ρ_ss = ρ′_ss = 2`, `d_rad = 0 < 2 = d′_rad`). -/
@[montpellier "27, 28, 29"]
theorem not_ineq3_imp_ineq9 :
    Chevalley exSL3 ∧ Chevalley exSL2SL2Ga2 ∧ exSL3.d = exSL2SL2Ga2.d ∧
      ineq3 exSL3 exSL2SL2Ga2 ∧ ¬ ineq9 exSL3 exSL2SL2Ga2 :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl, by decide, by decide⟩

/-- `27-semicontinuity-proof` (folder 27, p. 29): `(9) ⇒ (3)` does not follow either, even with
(1): special fibre `SL₂ × SL₂ × 𝔾_a³`, generic fibre `SL₂ × 𝔾_a × E`, `dim E = 5`
(`d_rad = 3 ≥ 1 = d′_rad`, `ρ_ss = 2 > 1 = ρ′_ss`, `ρ_ab = 0 ≤ 5`). -/
@[montpellier "27, 28, 29"]
theorem not_ineq9_imp_ineq3 :
    Chevalley exSL2SL2Ga3 ∧ Chevalley exSL2GaE5 ∧ exSL2SL2Ga3.d = exSL2GaE5.d ∧
      ineq1 exSL2SL2Ga3 exSL2GaE5 ∧ ineq9 exSL2SL2Ga3 exSL2GaE5 ∧
      ¬ ineq3 exSL2SL2Ga3 exSL2GaE5 :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl, by decide, by decide, by decide⟩

/-- `d_radaff`, not defined on the pages, read from the braces of page 29 as `d − d_ss`, that is
`ρ_ab + d_rad`. -/
def dRadAff (G : Invariants) : ℕ := G.rhoAb + G.dRad

/-- With the reading `d_radaff = ρ_ab + d_rad` and `d = d′`, (10) `d_radaff ≥ d′_radaff` is
equivalent to (4). -/
@[montpellier "27, 29"]
theorem ineq10_iff_ineq4 (h₀ : Chevalley G₀) (h₁ : Chevalley G₁) (hd : G₀.d = G₁.d) :
    dRadAff G₁ ≤ dRadAff G₀ ↔ ineq4 G₀ G₁ := by
  cases h₀; cases h₁; unfold dRadAff; omega

/-- `27-semicontinuity-proof` (folder 27, p. 29): with the reading `d_radaff = ρ_ab + d_rad`,
`(1) + (3) ⇒ (10)` fails for (10) read as `d_radaff ≥ d′_radaff`: `SL₃` against
`SL₂ × SL₂ × 𝔾_a²`. -/
@[montpellier "27, 29"]
theorem not_ineq1_ineq3_imp_ineq10 :
    Chevalley exSL3 ∧ Chevalley exSL2SL2Ga2 ∧ ineq1 exSL3 exSL2SL2Ga2 ∧
      ineq3 exSL3 exSL2SL2Ga2 ∧ ¬ dRadAff exSL2SL2Ga2 ≤ dRadAff exSL3 :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, by decide, by decide, by decide⟩

/-- `27-semicontinuity-proof` (folder 27, p. 29): and for (10) read as `d_radaff ≤ d′_radaff`:
`SL₂ × SL₂ × 𝔾_a²` against `SL₃`. -/
@[montpellier "27, 29"]
theorem not_ineq1_ineq3_imp_ineq10_ge :
    Chevalley exSL2SL2Ga2 ∧ Chevalley exSL3 ∧ ineq1 exSL2SL2Ga2 exSL3 ∧
      ineq3 exSL2SL2Ga2 exSL3 ∧ ¬ dRadAff exSL2SL2Ga2 ≤ dRadAff exSL3 :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, by decide, by decide, by decide⟩

end Grothendieck.Folder27
