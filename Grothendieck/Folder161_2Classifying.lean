module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.PresheafType
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Group.Idempotent

@[expose] public section

/-!
# Folder 161-2, page 42: the classifying topos of von Neumann regular rings is a presheaf topos

Finding `161-2-vn-regular-cartesian-presheaf-classifier`. Page 42, article 13, of folder 161-2
treats the commutative rings in which every `f` splits the ring, `A ≅ A_f × A/fA`
(« pseudo-corps », absolutely flat or von Neumann regular rings): « ∃(!) e ∈ A(U), e² = e,
e f inv., e(1 − f) = 0 », and concludes that their classifying topos is a presheaf topos,
`X_{ps.corps} ≅ R̂_cons`. The reading explains this by the theory being cartesian: the
idempotent, hence the splitting, exists *uniquely*.

**The theory.** Uniqueness is what lets the existential be replaced by an operation. A
commutative ring is von Neumann regular when every `a` has some `b` with `a² b = a`; it then
has a unique *quasi-inverse* `q a` with `a² q(a) = a` and `q(a)² a = q(a)`
(`existsUnique_quasiInverse_iff`). So von Neumann regular rings are the models of a theory
written with equations only, in the language of rings with one more unary symbol `q`
(`vnrTheory`): the axioms of commutative rings and the two equations of the quasi-inverse.
In sets, a commutative ring with an operation `q` is a model exactly when `q` is the
quasi-inverse (`isSetModel_ofCommRing_iff`), and such a `q` exists, and is then unique, exactly
when the ring is von Neumann regular; the idempotent of the page is `e = a q(a)`.

**The classifying topos.** An equational theory is a Horn theory, and Horn theories are of
presheaf type (lean-pool's `isOfPresheafType_of_isHorn`, roadmap 3.1 of its classifying-topoi
library: the presheaf topos on the Horn category of the theory classifies it). Hence
`vnrTheory_isOfPresheafType`: **the theory of commutative von Neumann regular rings is of
presheaf type**, which is the page's conclusion.

## Main results

* `vnrTheory_isHorn`, `vnrTheory_isOfPresheafType`: the theory is Horn, hence classified by a
  presheaf topos on a small category.
* `isSetModel_ofCommRing_iff`: a commutative ring with an operation `q` is a model of the theory
  iff `q` is a quasi-inverse.
* `existsUnique_quasiInverse_iff`: a commutative ring has a quasi-inverse operation, then a unique
  one, iff it is von Neumann regular.
* `mul_quasiInverse_idempotent`: `e = a q(a)` is idempotent with `e a = a`: the idempotent
  « e » of page 42.

## Not formalised

* The identification of the classifying category with the opposite of the finitely presented
  von Neumann regular rings (`R̂_cons` on the page): lean-pool's site is the Horn category of the
  theory, whose topos is equivalent; the comparison with finitely presented models is not done.
* That every model of the theory in sets is a commutative ring: the converse of
  `isSetModel_ofCommRing_iff` is stated only for structures coming from a ring.
* The relation with the field classifier of the same folder (the topology of the covers
  `A_f ⊔ A/fA`, finding `161-2-field-classifier-absolutely-flat-site`).
-/

open FirstOrder FirstOrder.Language LeanPool.ClassifyingTopoi

universe u w

namespace Grothendieck.Folder161_2Classifying

/-- The function symbols: `0`, `1`, negation, the quasi-inverse `q`, addition, multiplication. -/
inductive Func : ℕ → Type
  | zero : Func 0
  | one : Func 0
  | neg : Func 1
  | qinv : Func 1
  | add : Func 2
  | mul : Func 2

/-- The language of rings with a quasi-inverse; no relation symbols. -/
@[reducible] def lang : Language.{0, 0} := ⟨Func, fun _ => Empty⟩

variable {n : ℕ}

/-- The term `t + s`. -/
def tAdd (t s : lang.Term (Fin n)) : lang.Term (Fin n) := .func Func.add ![t, s]
/-- The term `t * s`. -/
def tMul (t s : lang.Term (Fin n)) : lang.Term (Fin n) := .func Func.mul ![t, s]
/-- The term `-t`. -/
def tNeg (t : lang.Term (Fin n)) : lang.Term (Fin n) := .func Func.neg ![t]
/-- The term `q t`. -/
def tQ (t : lang.Term (Fin n)) : lang.Term (Fin n) := .func Func.qinv ![t]
/-- The term `0`. -/
def tZero : lang.Term (Fin n) := .func Func.zero ![]
/-- The term `1`. -/
def tOne : lang.Term (Fin n) := .func Func.one ![]
/-- The `i`-th variable. -/
def x (i : Fin n) : lang.Term (Fin n) := .var i

/-- The equation `t = s`, as a sequent `⊤ ⊢ t = s` in the context `Fin n`. -/
def eqn (n : ℕ) (t s : lang.Term (Fin n)) : Sequent.{w} lang := ⟨n, .top, .equal t s⟩

/-- The axioms. -/
inductive Ax
  | addAssoc | addComm | zeroAdd | negAdd | mulAssoc | mulComm | oneMul | leftDistrib
  | quasi₁ | quasi₂

/-- The axioms as equations: those of commutative rings, `a² q(a) = a` and `q(a)² a = q(a)`. -/
def ax : Ax → Sequent.{w} lang
  | .addAssoc => eqn 3 (tAdd (tAdd (x 0) (x 1)) (x 2)) (tAdd (x 0) (tAdd (x 1) (x 2)))
  | .addComm => eqn 2 (tAdd (x 0) (x 1)) (tAdd (x 1) (x 0))
  | .zeroAdd => eqn 1 (tAdd tZero (x 0)) (x 0)
  | .negAdd => eqn 1 (tAdd (tNeg (x 0)) (x 0)) tZero
  | .mulAssoc => eqn 3 (tMul (tMul (x 0) (x 1)) (x 2)) (tMul (x 0) (tMul (x 1) (x 2)))
  | .mulComm => eqn 2 (tMul (x 0) (x 1)) (tMul (x 1) (x 0))
  | .oneMul => eqn 1 (tMul tOne (x 0)) (x 0)
  | .leftDistrib =>
    eqn 3 (tMul (x 0) (tAdd (x 1) (x 2))) (tAdd (tMul (x 0) (x 1)) (tMul (x 0) (x 2)))
  | .quasi₁ => eqn 1 (tMul (tMul (x 0) (x 0)) (tQ (x 0))) (x 0)
  | .quasi₂ => eqn 1 (tMul (tMul (tQ (x 0)) (tQ (x 0))) (x 0)) (tQ (x 0))

/-- **The theory of commutative von Neumann regular rings**, with their quasi-inverse. -/
def vnrTheory : GeometricTheory.{w} lang := Set.range ax

/-- The theory is Horn: every axiom is an equation. -/
theorem vnrTheory_isHorn : (vnrTheory.{w}).IsHorn := by
  rintro _ ⟨a, rfl⟩
  cases a <;> exact ⟨trivial, trivial⟩

/-- **Page 42: the classifying topos of commutative von Neumann regular rings is a presheaf
topos.** Their theory, a Horn theory, is classified by the presheaf topos on a small category. -/
theorem vnrTheory_isOfPresheafType : IsOfPresheafType.{u} (vnrTheory.{u}) :=
  isOfPresheafType_of_isHorn _ vnrTheory_isHorn

/-! ### Models in sets -/

section Models

variable (A : Type*) [CommRing A]

/-- The structure of the language on a commutative ring with an operation `q`. -/
@[instance_reducible]
def ofCommRing (q : A → A) : lang.Structure A where
  funMap {n} f v := match n, f with
    | _, .zero => 0
    | _, .one => 1
    | _, .neg => -v 0
    | _, .qinv => q (v 0)
    | _, .add => v 0 + v 1
    | _, .mul => v 0 * v 1
  RelMap r _ := Empty.elim r

/-- **Models of the theory among rings.** A commutative ring with an operation `q` is a model of
`vnrTheory` iff `q` is a quasi-inverse: `a² q(a) = a` and `q(a)² a = q(a)` for every `a`. -/
theorem isSetModel_ofCommRing_iff (q : A → A) :
    letI := ofCommRing A q
    (vnrTheory.{w}).IsSetModel A ↔ ∀ a : A, a * a * q a = a ∧ q a * q a * a = q a := by
  let := ofCommRing A q
  constructor
  · intro h a
    exact ⟨h _ ⟨.quasi₁, rfl⟩ ![a] trivial, h _ ⟨.quasi₂, rfl⟩ ![a] trivial⟩
  · rintro h _ ⟨a, rfl⟩ v -
    cases a
    · exact add_assoc _ _ _
    · exact add_comm _ _
    · exact zero_add _
    · exact neg_add_cancel _
    · exact mul_assoc _ _ _
    · exact mul_comm _ _
    · exact one_mul _
    · exact mul_add _ _ _
    · exact (h _).1
    · exact (h _).2

variable {A}

/-- A quasi-inverse is unique: from `a² y = a`, `y² a = y`, `a² z = a`, `z² a = z`, `y = z`. -/
theorem quasiInverse_unique {a y z : A} (hy₁ : a * a * y = a) (hy₂ : y * y * a = y)
    (hz₁ : a * a * z = a) (hz₂ : z * z * a = z) : y = z := by
  have hy : y = y * a * z := by
    calc y = y * y * a := hy₂.symm
      _ = y * y * (a * a * z) := by rw [hz₁]
      _ = y * y * a * a * z := by ring
      _ = y * a * z := by rw [hy₂]
  have hz : z = z * a * y := by
    calc z = z * z * a := hz₂.symm
      _ = z * z * (a * a * y) := by rw [hy₁]
      _ = z * z * a * a * y := by ring
      _ = z * a * y := by rw [hz₂]
  calc y = y * a * z := hy
    _ = z * a * y := by ring
    _ = z := hz.symm

/-- From any `b` with `a² b = a`, `a b²` is a quasi-inverse of `a`. -/
theorem isQuasiInverse_of_mul {a b : A} (h : a * a * b = a) :
    a * a * (a * b * b) = a ∧ a * b * b * (a * b * b) * a = a * b * b :=
  ⟨by linear_combination (a * b + 1) * h, by linear_combination (a * b ^ 3 + b ^ 2) * h⟩

variable (A) in
/-- **The quasi-inverse.** A commutative ring has a quasi-inverse operation, and then exactly one,
iff it is von Neumann regular: every `a` has some `b` with `a² b = a`. -/
theorem existsUnique_quasiInverse_iff :
    (∀ a : A, ∃ b, a * a * b = a) ↔
      ∃! q : A → A, ∀ a, a * a * q a = a ∧ q a * q a * a = q a := by
  constructor
  · intro h
    choose b hb using h
    refine ⟨fun a => a * b a * b a, fun a => isQuasiInverse_of_mul (hb a), fun q hq => ?_⟩
    funext a
    exact quasiInverse_unique (hq a).1 (hq a).2 (isQuasiInverse_of_mul (hb a)).1
      (isQuasiInverse_of_mul (hb a)).2
  · rintro ⟨q, hq, -⟩ a
    exact ⟨q a, (hq a).1⟩

/-- **The idempotent of page 42.** With `y = q(a)` (only `a² y = a` is needed), `e = a y` is
idempotent and `e a = a`: `A ≅ eA × (1 − e)A`, with `a` invertible in the first factor and zero in the
second, which is `A ≅ A_a × A/aA`. -/
theorem mul_quasiInverse_idempotent {a y : A} (h₁ : a * a * y = a) :
    IsIdempotentElem (a * y) ∧ a * y * a = a :=
  ⟨by unfold IsIdempotentElem; linear_combination y * h₁, by linear_combination h₁⟩

end Models

end Grothendieck.Folder161_2Classifying
