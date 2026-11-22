module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.ModelTheory.Algebra.Ring.Basic
public import Mathlib.ModelTheory.Ultraproducts
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Nilpotent.Lemmas
import Grothendieck.Attr

@[expose] public section

/-!
# p:noncoh: the first-order part, proved by Łoś's theorem

Problem p:noncoh of the note on the open problems (`docs/problems/article.tex`; folder 161-2,
pp. 39, 41–42, *Algèbre universelle*): the classifying topoi of the geometric theories of rings
with irreducible spectrum (nilradical prime) and of rings with zero-dimensional spectrum are not
coherent, the topologies that present them on the affine schemes of finite type over `ℤ` not
being quasi-compact. The open question (do they have enough points?) is not touched here.

What is proved: neither class of commutative rings is **elementary**. There is no first-order
theory `T` in the language of rings (`FirstOrder.Language.ring`) whose models among commutative
rings are exactly the rings with prime nilradical (`not_isAxiomatizable_nilradical_isPrime`), or
exactly the rings of Krull dimension `≤ 0` (`not_isAxiomatizable_krullDimLE_zero`), or exactly
those of Krull dimension `0` (`not_isAxiomatizable_ringKrullDim_eq_zero`). A coherent sequent is
a first-order sentence, so in particular neither theory has the same set-theoretic models as a
coherent quotient of the theory of commutative rings: this is the content behind the page's
remark that the presenting topologies are not quasi-compact. It does **not** prove that the
classifying topoi are not coherent for any presentation: coherence of a topos is not stated here,
and Mathlib has neither geometric theories nor their classifying topoi.

**The argument.** A class of structures defined by a first-order theory is closed under
ultraproducts (Łoś, `FirstOrder.Language.Ultraproduct.sentence_realize`). The ultraproduct of
commutative rings `A i` along an ultrafilter `𝒰` is built as a ring, the quotient
`UltraproductRing A 𝒰` of `∏ A i` by the ideal of families that vanish `𝒰`-almost everywhere;
`equivProduct` identifies it, as a structure for the language of rings, with Mathlib's
ultraproduct `Filter.Product`, so that Łoś applies to it (`realize_sentence_iff`).

**The counterexample**, one family for both properties: with `Cₙ = ℤ/2ⁿ⁺¹` and `ε : Cₙ → 𝔽₂`
the reduction, `Dₙ = {(a, b) ∈ Cₙ × Cₙ | ε a = ε b}` (`D n`), a finite ring. Its nilradical is
the kernel of `(a, b) ↦ ε a`, a maximal ideal, so `Dₙ` has prime nilradical and dimension `0`.
In `Dₙ`, `x = (2, 0)` and `y = (0, 2)` have `xy = 0` and `xᵐ ≠ 0` for `m ≤ n`. In the ultraproduct
along a non-principal ultrafilter on `ℕ`, the classes `X`, `Y` of `(x)ₙ`, `(y)ₙ` have `XY = 0` and
are not nilpotent, so the nilradical is not prime; and `X` lies in the Jacobson radical (`1 + XZ`
is a unit, coordinatewise) without being nilpotent, whereas in dimension `≤ 0` the Jacobson
radical is the nilradical. (The family `k[x,y]/(xy, xⁿ, yⁿ)` would do as well; `Dₙ` is finite and
needs no polynomial computation.)
-/

universe u

open FirstOrder FirstOrder.Language FirstOrder.Ring Filter

namespace OpenProblems.TopoiStacksNoncoh

/-- A property `P` of commutative rings (in universe `u`) is **axiomatisable** in first-order logic
when some theory `T` in the language of rings has, among the commutative rings `R` (with their
structure `compatibleRingOfRing R`), exactly those with `P R` as models. -/
def IsAxiomatizable (P : ∀ (R : Type u) [CommRing R], Prop) : Prop :=
  ∃ T : Language.ring.Theory, ∀ (R : Type u) [CommRing R],
    (letI := compatibleRingOfRing R; R ⊨ T) ↔ P R

section Ultraproduct

variable {ι : Type} (A : ι → Type u) [∀ i, CommRing (A i)] (𝒰 : Ultrafilter ι)

/-- The ideal of `∏ A i` of the families that vanish `𝒰`-almost everywhere. -/
def eventuallyZero : Ideal (∀ i, A i) where
  carrier := {f | ∀ᶠ i in (𝒰 : Filter ι), f i = 0}
  add_mem' {f g} hf hg := (Filter.Eventually.and hf hg).mono fun i h => by
    simp [h.1, h.2]
  zero_mem' := Eventually.of_forall fun _ => rfl
  smul_mem' c f hf := Filter.Eventually.mono hf fun i h => by
    simp [h]

/-- The **ultraproduct** of the commutative rings `A i` along `𝒰`, as a commutative ring: the
quotient of `∏ A i` by the families that vanish `𝒰`-almost everywhere. -/
abbrev UltraproductRing : Type u := (∀ i, A i) ⧸ eventuallyZero A 𝒰

variable {A 𝒰}

theorem mk_eq_mk_iff (f g : ∀ i, A i) :
    Ideal.Quotient.mk (eventuallyZero A 𝒰) f = Ideal.Quotient.mk (eventuallyZero A 𝒰) g ↔
      ∀ᶠ i in (𝒰 : Filter ι), f i = g i := by
  rw [Ideal.Quotient.eq]
  change (∀ᶠ i in (𝒰 : Filter ι), f i - g i = 0) ↔ _
  simp only [sub_eq_zero]

theorem mk_eq_zero_iff (f : ∀ i, A i) :
    Ideal.Quotient.mk (eventuallyZero A 𝒰) f = 0 ↔ ∀ᶠ i in (𝒰 : Filter ι), f i = 0 := by
  rw [← map_zero (Ideal.Quotient.mk (eventuallyZero A 𝒰)), mk_eq_mk_iff]
  rfl

variable (A 𝒰)

/-- The ring structures `compatibleRingOfRing` on the factors, used for Łoś's theorem. -/
@[instance_reducible]
def factorStructure : ∀ i, Language.ring.Structure (A i) :=
  fun i => (compatibleRingOfRing (A i)).toStructure

/-- `UltraproductRing A 𝒰`, with its structure `compatibleRingOfRing`, is isomorphic as a
structure for the language of rings to Mathlib's ultraproduct `Filter.Product` of the factors. -/
noncomputable def equivProduct :
    letI := compatibleRingOfRing (UltraproductRing A 𝒰)
    letI := factorStructure A
    UltraproductRing A 𝒰 ≃[Language.ring] (𝒰 : Filter ι).Product A :=
  letI := compatibleRingOfRing (UltraproductRing A 𝒰)
  letI := factorStructure A
  { toEquiv := Quotient.congr (Equiv.refl _) fun f g => by
      change _ ↔ ∀ᶠ i in (𝒰 : Filter ι), f i = g i
      rw [← mk_eq_mk_iff]
      exact Quotient.eq.symm
    map_fun' := by
      intro n f x
      obtain ⟨y, rfl⟩ : ∃ y : Fin n → ∀ i, A i,
          (fun j => Ideal.Quotient.mk (eventuallyZero A 𝒰) (y j)) = x :=
        ⟨fun j => (Ideal.Quotient.mk_surjective (x j)).choose,
          funext fun j => (Ideal.Quotient.mk_surjective (x j)).choose_spec⟩
      change _ = Structure.funMap f fun j => ((y j : ∀ i, A i) : (𝒰 : Filter ι).Product A)
      rw [Ultraproduct.funMap_cast]
      cases f <;> rfl
    map_rel' := fun r => r.elim }

variable {A 𝒰}

/-- **Łoś's theorem** for `UltraproductRing A 𝒰`: a sentence of the language of rings holds in it
if and only if it holds in `𝒰`-almost every factor. -/
theorem realize_sentence_iff (φ : Language.ring.Sentence) :
    (letI := compatibleRingOfRing (UltraproductRing A 𝒰); UltraproductRing A 𝒰 ⊨ φ) ↔
      ∀ᶠ i in (𝒰 : Filter ι), (letI := compatibleRingOfRing (A i); A i ⊨ φ) := by
  let := compatibleRingOfRing (UltraproductRing A 𝒰)
  let := factorStructure A
  rw [StrongHomClass.realize_sentence (equivProduct A 𝒰) φ]
  exact Ultraproduct.sentence_realize φ

/-- A model of `T` in every factor gives a model of `T` in `UltraproductRing A 𝒰`. -/
theorem model_of_forall (T : Language.ring.Theory)
    (h : ∀ i, letI := compatibleRingOfRing (A i); A i ⊨ T) :
    letI := compatibleRingOfRing (UltraproductRing A 𝒰)
    UltraproductRing A 𝒰 ⊨ T := by
  let := compatibleRingOfRing (UltraproductRing A 𝒰)
  refine (Theory.model_iff T).2 fun φ hφ => (realize_sentence_iff φ).2 ?_
  exact Eventually.of_forall fun i =>
    letI := compatibleRingOfRing (A i)
    (Theory.model_iff T).1 (h i) φ hφ

/-- A property that holds in every factor and fails in `UltraproductRing A 𝒰` is not
axiomatisable. -/
theorem not_isAxiomatizable_of_ultraproduct {P : ∀ (R : Type u) [CommRing R], Prop}
    (hA : ∀ i, P (A i)) (hQ : ¬ P (UltraproductRing A 𝒰)) : ¬ IsAxiomatizable P := by
  rintro ⟨T, hT⟩
  exact hQ ((hT _).1 (model_of_forall T fun i => (hT (A i)).2 (hA i)))

end Ultraproduct

section Counterexample

/-- `Cₙ = ℤ/2ⁿ⁺¹`, lifted to the universe `u`. -/
abbrev C (n : ℕ) : Type u := ULift.{u} (ZMod (2 ^ (n + 1)))

/-- The reduction `ε : Cₙ → 𝔽₂`. -/
noncomputable def ε (n : ℕ) : C.{u} n →+* ZMod 2 :=
  (ZMod.castHom (dvd_pow_self 2 n.succ_ne_zero) (ZMod 2)).comp ULift.ringEquiv.toRingHom

/-- The class of `2` in `Cₙ`. -/
def two (n : ℕ) : C.{u} n := ULift.up 2

theorem isNilpotent_of_ε_eq_zero {n : ℕ} {c : C.{u} n} (h : ε n c = 0) : IsNilpotent c := by
  obtain ⟨z⟩ := c
  have hz : ZMod.castHom (dvd_pow_self 2 n.succ_ne_zero) (ZMod 2) z = 0 := h
  rw [← ZMod.natCast_zmod_val z, map_natCast, ZMod.natCast_eq_zero_iff] at hz
  obtain ⟨k, hk⟩ := hz
  refine ⟨n + 1, ?_⟩
  apply ULift.ext
  change z ^ (n + 1) = 0
  rw [← ZMod.natCast_zmod_val z, hk, ← Nat.cast_pow, mul_pow, Nat.cast_mul, ZMod.natCast_self,
    zero_mul]

theorem ε_two (n : ℕ) : ε n (two.{u} n) = 0 := by
  change ZMod.castHom (dvd_pow_self 2 n.succ_ne_zero) (ZMod 2) 2 = 0
  rw [map_ofNat]
  rfl

theorem two_pow_ne_zero {n m : ℕ} (hm : m ≤ n) : two.{u} n ^ m ≠ 0 := by
  intro h
  have h' : ((2 ^ m : ℕ) : ZMod (2 ^ (n + 1))) = 0 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact congrArg ULift.down h
  rw [ZMod.natCast_eq_zero_iff, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at h'
  omega

/-- `Dₙ = {(a, b) ∈ Cₙ × Cₙ | ε a = ε b}`, the fibre product of `Cₙ` with itself over `𝔽₂`. -/
abbrev D (n : ℕ) : Type u :=
  ↥(RingHom.eqLocus ((ε.{u} n).comp (RingHom.fst (C n) (C n)))
    ((ε.{u} n).comp (RingHom.snd (C n) (C n))))

/-- The map `Dₙ → 𝔽₂`, `(a, b) ↦ ε a`. -/
noncomputable def φ (n : ℕ) : D.{u} n →+* ZMod 2 :=
  ((ε n).comp (RingHom.fst _ _)).comp (Subring.subtype _)

theorem isNilpotent_iff {n : ℕ} (d : D.{u} n) : IsNilpotent d ↔ φ n d = 0 := by
  refine ⟨fun h => (h.map (φ n)).eq_zero, fun h => ?_⟩
  obtain ⟨⟨a, b⟩, hab⟩ := d
  have hab : ε n a = ε n b := hab
  have ha : ε n a = 0 := h
  obtain ⟨N, hN⟩ := isNilpotent_of_ε_eq_zero ha
  obtain ⟨M, hM⟩ := isNilpotent_of_ε_eq_zero (hab ▸ ha)
  refine ⟨N + M, Subtype.ext (Prod.ext ?_ ?_)⟩
  · exact pow_eq_zero_of_le (Nat.le_add_right N M) hN
  · exact pow_eq_zero_of_le (Nat.le_add_left M N) hM

theorem nilradical_eq (n : ℕ) : nilradical (D.{u} n) = RingHom.ker (φ n) :=
  Ideal.ext fun d => mem_nilradical.trans (isNilpotent_iff d)

theorem φ_surjective (n : ℕ) : Function.Surjective (φ.{u} n) := fun z =>
  ⟨(z.val : D n), by rw [map_natCast, ZMod.natCast_zmod_val]⟩

instance nilradical_isMaximal (n : ℕ) : (nilradical (D.{u} n)).IsMaximal := by
  rw [nilradical_eq]
  exact RingHom.ker_isMaximal_of_surjective _ (φ_surjective n)

instance (n : ℕ) : IsLocalRing (D.{u} n) := IsLocalRing.of_isMaximal_nilradical _

instance (n : ℕ) : Ring.KrullDimLE 0 (D.{u} n) := Ring.KrullDimLE.of_isMaximal_nilradical _

/-- `x = (2, 0) ∈ Dₙ`. -/
def x (n : ℕ) : D.{u} n := ⟨(two n, 0), by simp [RingHom.mem_eqLocus, ε_two]⟩

/-- `y = (0, 2) ∈ Dₙ`. -/
def y (n : ℕ) : D.{u} n := ⟨(0, two n), by simp [RingHom.mem_eqLocus, ε_two]⟩

theorem x_mul_y (n : ℕ) : x.{u} n * y n = 0 :=
  Subtype.ext (Prod.ext (mul_zero _) (zero_mul _))

theorem φ_x (n : ℕ) : φ n (x.{u} n) = 0 := ε_two n

theorem x_pow_ne_zero {n m : ℕ} (hm : m ≤ n) : x.{u} n ^ m ≠ 0 := fun h =>
  two_pow_ne_zero hm (congrArg (fun d : D n => d.1.1) h)

theorem y_pow_ne_zero {n m : ℕ} (hm : m ≤ n) : y.{u} n ^ m ≠ 0 := fun h =>
  two_pow_ne_zero hm (congrArg (fun d : D n => d.1.2) h)

/-- The ultraproduct of the `Dₙ` along a non-principal ultrafilter on `ℕ`. -/
abbrev Q : Type u := UltraproductRing D.{u} (hyperfilter ℕ)

/-- The classes `X`, `Y ∈ Q` of `(x)ₙ`, `(y)ₙ`. -/
noncomputable def X : Q.{u} := Ideal.Quotient.mk _ fun n => x n

noncomputable def Y : Q.{u} := Ideal.Quotient.mk _ fun n => y n

theorem eventually_ge (m : ℕ) : ∀ᶠ n in ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ), m ≤ n :=
  Eventually.filter_mono hyperfilter_le_cofinite
    (by rw [Nat.cofinite_eq_atTop]; exact eventually_ge_atTop m)

theorem X_mul_Y : X.{u} * Y = 0 := by
  rw [X, Y, ← map_mul]
  exact (mk_eq_zero_iff _).2 (Eventually.of_forall x_mul_y)

theorem not_isNilpotent_X : ¬ IsNilpotent X.{u} := by
  rintro ⟨m, hm⟩
  rw [X, ← map_pow, mk_eq_zero_iff] at hm
  obtain ⟨n, h1, h2⟩ := (hm.and (eventually_ge m)).exists
  exact x_pow_ne_zero h2 h1

theorem not_isNilpotent_Y : ¬ IsNilpotent Y.{u} := by
  rintro ⟨m, hm⟩
  rw [Y, ← map_pow, mk_eq_zero_iff] at hm
  obtain ⟨n, h1, h2⟩ := (hm.and (eventually_ge m)).exists
  exact y_pow_ne_zero h2 h1

theorem not_nilradical_isPrime : ¬ (nilradical Q.{u}).IsPrime := fun h => by
  have hXY : X * Y ∈ nilradical Q := X_mul_Y ▸ zero_mem _
  rcases h.mem_or_mem hXY with hX | hY
  · exact not_isNilpotent_X (mem_nilradical.1 hX)
  · exact not_isNilpotent_Y (mem_nilradical.1 hY)

theorem X_mem_jacobson : X.{u} ∈ (⊥ : Ideal Q).jacobson := by
  refine Ideal.mem_jacobson_bot.2 fun Z => ?_
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective Z
  have : X * Ideal.Quotient.mk _ g + 1 =
      Ideal.Quotient.mk (eventuallyZero D (hyperfilter ℕ)) ((fun n => x n) * g + 1) := by
    rfl
  rw [this]
  refine IsUnit.map _ (Pi.isUnit_iff.2 fun n => IsNilpotent.isUnit_add_one ?_)
  rw [isNilpotent_iff]
  change φ n (x n * g n) = 0
  rw [map_mul, φ_x, zero_mul]

theorem not_krullDimLE_zero : ¬ Ring.KrullDimLE 0 Q.{u} := fun _ => by
  have hX : X ∈ nilradical Q := by
    rw [nilradical, Ideal.zero_eq_bot, ← Ideal.jacobson_eq_radical]
    exact X_mem_jacobson
  exact not_isNilpotent_X (mem_nilradical.1 hX)

instance : Nontrivial Q.{u} :=
  nontrivial_of_ne X 0 fun h => not_isNilpotent_X ⟨1, by rw [pow_one, h]⟩

end Counterexample

/-- **p:noncoh, rings with irreducible spectrum.** No first-order theory in the language of rings
has, as its models among the commutative rings, exactly the rings whose nilradical is prime. -/
@[montpellier "161-2, 39, 41–42"]
theorem not_isAxiomatizable_nilradical_isPrime :
    ¬ IsAxiomatizable.{u} fun R _ => (nilradical R).IsPrime :=
  not_isAxiomatizable_of_ultraproduct (A := D) (𝒰 := hyperfilter ℕ)
    (fun _ => Ideal.IsMaximal.isPrime inferInstance) not_nilradical_isPrime

/-- **p:noncoh, rings with zero-dimensional spectrum.** No first-order theory in the language of
rings has, as its models among the commutative rings, exactly the rings of Krull dimension `≤ 0`
(the zero ring included). -/
@[montpellier "161-2, 39, 41–42"]
theorem not_isAxiomatizable_krullDimLE_zero :
    ¬ IsAxiomatizable.{u} fun R _ => Ring.KrullDimLE 0 R :=
  not_isAxiomatizable_of_ultraproduct (A := D) (𝒰 := hyperfilter ℕ)
    (fun _ => inferInstance) not_krullDimLE_zero

/-- The same with Krull dimension exactly `0` (the zero ring, of dimension `⊥`, excluded). -/
@[montpellier "161-2, 39, 41–42"]
theorem not_isAxiomatizable_ringKrullDim_eq_zero :
    ¬ IsAxiomatizable.{u} fun R _ => ringKrullDim R = 0 :=
  not_isAxiomatizable_of_ultraproduct (A := D) (𝒰 := hyperfilter ℕ)
    (fun _ => ringKrullDimZero_iff_ringKrullDim_eq_zero.1 inferInstance)
    fun h => not_krullDimLE_zero (ringKrullDimZero_iff_ringKrullDim_eq_zero.2 h)

end OpenProblems.TopoiStacksNoncoh
