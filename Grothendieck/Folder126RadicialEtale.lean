module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianFiniteAlgebras

@[expose] public section

/-!
# Folder 126, pages 17–23: the radicial–étale factorisation, local core

Finding `126-radicial-etale-factorisation`. Pages 17–23 of folder 126 (under the cover
« Descente fidèlement plate ») state: *let `f : X → Y` be finite and universally open, with `Y`
locally noetherian, whose fibres all have the same number `n` of geometric points; then `f`
factors as a finite surjective radicial `X → X^ét` followed by a finite étale cover `X^ét → Y`,
and every `Y`-morphism from `X` to an étale `Y`-scheme factors uniquely through `X^ét`.*

**The reading.** « Univ. ouvert » is an interlinear addition on page 17 whose reading is marked
uncertain in the transcription (and « factorisation » in the heading is uncertain too). The
statement is formalised here *as the reading gives it*, with universal openness as the
hypothesis; if the facsimile showed another word, the statement would have to be revisited.

**Is it true as read?** Yes. After base change to a strict henselisation `R = 𝒪^sh_{Y,ȳ}`
(universal openness is what survives this base change, as openness of `Spec A → Spec R`), the
finite `R`-algebra `A` is a product `∏ᵢ Bᵢ` of local rings (Stacks 04GJ); each `Spec Bᵢ` is open
and closed in `Spec A`, so its image is an open set containing the closed point, hence all of
`Spec R`; each factor therefore has at least one geometric point over every point, the closed
fibre has exactly `|ι|` of them, and constancy of `d` forces exactly one over every point: each
`Spec Bᵢ → Spec R` is radicial, and `Spec A → ∐_ι Spec R` is the factorisation. The global
`X^ét` is obtained from these by étale descent, and its universal property is the topological
invariance of the étale site. That argument is the one formalised below in its local form.

**What is proved.** `radicial_etale_factorisation_of_strictlyHenselian`: let `R` be a strictly
henselian local ring and `A` a module-finite `R`-algebra such that `Spec A → Spec R` is an open
map and, for every algebraically closed field `K` and every ring map `φ : R → K`, the number of
`R`-maps `A → K` over `φ` (the geometric points of the fibre over `φ`, `GeomPoints`) is a constant
`n`. Then there are a finite index type `ι` with `|ι| = n` and strictly henselian local
module-finite `R`-algebras `Bᵢ` with `A ≃ₐ[R] ∏ᵢ Bᵢ`, such that
* every `Spec Bᵢ → Spec R` has exactly one geometric point over every geometric point of `Spec R`
  (it is surjective and universally injective, i.e. radicial — the first arrow `f₁`);
* `etalePartMap e : R^ι → A` (the trivial finite étale cover `∐_ι Spec R`, the second arrow `f₂`)
  has the universal property: every `R`-algebra map `R^J → A` from a split finite étale algebra
  factors uniquely through it (`existsUnique_comp_etalePartMap_eq`).

The general pieces: a ring map from a finite product into a local ring factors through exactly
one factor (`exists_map_single_eq_one`, `geomPointsPiEquiv`); a prime of an integral extension
over `ker φ` gives a geometric point over `φ` (`exists_ringHom_lift_of_prime`, Stacks 09GU via
`IsAlgClosed.lift`); openness gives a point of each factor over each prime
(`nonempty_geomPoints_of_isOpenMap`). The splitting itself is the AxiomMath/Stacks
`exists_algEquiv_pi_strictHenselian_of_module_finite` (from 04GJ), and the count on the closed
fibre is its `finiteAlgHomCharsEquiv`.

**Not formalised.**
* The global statement over a locally noetherian `Y`: the base change to the strict
  henselisations, and the construction of `X^ét` by descent of étale covers (SGA 1 IX §4, the
  draft's Stacks 02L5), are not done; Mathlib has no finite étale part `π₀(X/Y)` of a finite
  morphism.
* The universal property is proved only against split finite étale algebras `R^J`; that every
  finite étale algebra over a strictly henselian ring is split (Stacks 04GL), and the topological
  invariance of the étale site used on page 23, are not formalised here.
* Universal openness enters only through the openness of `Spec A → Spec R` after base change;
  the page's remark that « `d` constant » may be dropped for connected `Y` is false (the
  reading's counterexample `y² = t` over `k[t]`) and is not stated.
-/

open IsLocalRing

universe u

namespace Grothendieck.Folder126RadicialEtale

/-- The geometric points over `φ : R → K` of `Spec A`: the ring maps `A → K` extending `φ`. When
`K` is algebraically closed and `A` is finite over `R`, their number is the separable degree
`d(y)` of the fibre over the point `y = ker φ` (folder 126, page 17). -/
abbrev GeomPoints (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] {K : Type*} [CommRing K]
    (φ : R →+* K) : Type _ :=
  {ψ : A →+* K // ψ.comp (algebraMap R A) = φ}

/-- An idempotent of a local ring is `0` or `1`. -/
theorem idempotent_eq_zero_or_one {T : Type*} [CommRing T] [IsLocalRing T] {t : T}
    (ht : IsIdempotentElem t) : t = 0 ∨ t = 1 := by
  have h0 : t * (1 - t) = 0 := ht.mul_one_sub_self
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self t with h | h
  · right
    exact (sub_eq_zero.mp ((h.mul_right_eq_zero).mp h0)).symm
  · left
    exact (h.mul_left_eq_zero).mp h0

/-- A ring map from a finite product into a local ring sends one of the unit idempotents to `1`. -/
theorem exists_map_single_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*}
    [∀ i, CommRing (B i)] {T : Type*} [CommRing T] [IsLocalRing T] (F : (∀ i, B i) →+* T) :
    ∃ i, F (Pi.single i 1) = 1 := by
  by_contra h
  simp only [not_exists] at h
  have h0 : ∀ i, F (Pi.single i 1) = 0 := by
    intro i
    have hidem : IsIdempotentElem (F (Pi.single i 1)) := by
      show F (Pi.single i 1) * F (Pi.single i 1) = F (Pi.single i 1)
      rw [← map_mul, ← Pi.single_mul, one_mul]
    exact (idempotent_eq_zero_or_one hidem).resolve_right (h i)
  have hsum : (∑ i, Pi.single i (1 : B i) : ∀ i, B i) = 1 := Finset.univ_sum_single (1 : ∀ i, B i)
  have h1 : F 1 = 0 := by
    rw [← hsum, map_sum]
    exact Finset.sum_eq_zero fun i _ => h0 i
  rw [map_one] at h1
  exact one_ne_zero h1

/-- A ring map from a product which sends the `i`-th unit idempotent to `1` only sees the `i`-th
coordinate. -/
theorem map_eq_map_single_apply {ι : Type*} [DecidableEq ι] {B : ι → Type*}
    [∀ i, CommRing (B i)] {T : Type*} [CommRing T] (F : (∀ i, B i) →+* T) {i : ι}
    (hi : F (Pi.single i 1) = 1) (x : ∀ j, B j) : F x = F (Pi.single i (x i)) := by
  have hx : x * Pi.single i 1 = Pi.single i (x i) := by
    funext j
    by_cases hj : j = i
    · rw [hj, Pi.mul_apply, Pi.single_eq_same, Pi.single_eq_same, mul_one]
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, mul_zero]
  rw [← hx, map_mul, hi, mul_one]

/-- The ring map `B i → T` induced by a ring map from the product supported on the `i`-th
factor. -/
def restrictSingle {ι : Type*} [DecidableEq ι] {B : ι → Type*} [∀ i, CommRing (B i)]
    {T : Type*} [CommRing T] (F : (∀ i, B i) →+* T) (i : ι) (hi : F (Pi.single i 1) = 1) :
    B i →+* T where
  toFun b := F (Pi.single i b)
  map_one' := hi
  map_mul' a b := by
    show F (Pi.single i (a * b)) = F (Pi.single i a) * F (Pi.single i b)
    rw [Pi.single_mul, map_mul]
  map_zero' := by
    show F (Pi.single i 0) = 0
    rw [Pi.single_zero, map_zero]
  map_add' a b := by
    show F (Pi.single i (a + b)) = F (Pi.single i a) + F (Pi.single i b)
    rw [Pi.single_add, map_add]

/-- The geometric points of a finite product are the disjoint union of those of its factors. -/
noncomputable def geomPointsPiEquiv {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] {K : Type*} [Field K]
    (φ : R →+* K) : (Σ i, GeomPoints R (B i) φ) ≃ GeomPoints R (∀ i, B i) φ :=
  Equiv.ofBijective
    (fun z => ⟨z.2.1.comp (Pi.evalRingHom B z.1), RingHom.ext fun r => RingHom.congr_fun z.2.2 r⟩)
    (by
      classical
      constructor
      · rintro ⟨i, ψ⟩ ⟨j, ψ'⟩ h
        have h' : ψ.1.comp (Pi.evalRingHom B i) = ψ'.1.comp (Pi.evalRingHom B j) :=
          congrArg Subtype.val h
        have hij : i = j := by
          by_contra hne
          have h1 : (ψ.1.comp (Pi.evalRingHom B i)) (Pi.single i 1) = 1 := by
            show ψ.1 (Pi.single i 1 i) = 1
            rw [Pi.single_eq_same, map_one]
          have h2 : (ψ'.1.comp (Pi.evalRingHom B j)) (Pi.single i 1) = 0 := by
            show ψ'.1 (Pi.single i 1 j) = 0
            rw [Pi.single_eq_of_ne' hne, map_zero]
          exact one_ne_zero (h1.symm.trans ((RingHom.congr_fun h' _).trans h2))
        subst hij
        have hψ : ψ = ψ' := by
          apply Subtype.ext
          refine RingHom.ext fun b => ?_
          have h3 : ψ.1 (Pi.single i b i) = ψ'.1 (Pi.single i b i) :=
            RingHom.congr_fun h' (Pi.single i b)
          rwa [Pi.single_eq_same] at h3
        rw [hψ]
      · rintro ⟨F, hF⟩
        obtain ⟨i, hi⟩ := exists_map_single_eq_one F
        have hcomp : (restrictSingle F i hi).comp (algebraMap R (B i)) = φ := by
          refine RingHom.ext fun r => ?_
          rw [← hF]
          show F (Pi.single i (algebraMap R (B i) r)) = F (algebraMap R (∀ j, B j) r)
          exact (map_eq_map_single_apply F hi (algebraMap R (∀ j, B j) r)).symm
        exact ⟨⟨i, ⟨restrictSingle F i hi, hcomp⟩⟩,
          Subtype.ext (RingHom.ext fun x => (map_eq_map_single_apply F hi x).symm)⟩)

/-- Geometric points are transported along an isomorphism of algebras. -/
def geomPointsCongr {R A A' : Type*} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A]
    [Algebra R A'] (e : A ≃ₐ[R] A') {K : Type*} [CommRing K] (φ : R →+* K) :
    GeomPoints R A φ ≃ GeomPoints R A' φ where
  toFun ψ := ⟨ψ.1.comp e.symm.toRingHom, by
    have hcomm : e.symm.toRingHom.comp (algebraMap R A') = algebraMap R A :=
      RingHom.ext fun r => e.symm.commutes r
    rw [RingHom.comp_assoc, hcomm, ψ.2]⟩
  invFun ψ := ⟨ψ.1.comp e.toRingHom, by
    have hcomm : e.toRingHom.comp (algebraMap R A) = algebraMap R A' :=
      RingHom.ext fun r => e.commutes r
    rw [RingHom.comp_assoc, hcomm, ψ.2]⟩
  left_inv := by
    rintro ⟨ψ, hψ⟩
    apply Subtype.ext
    ext x
    simp
  right_inv := by
    rintro ⟨ψ, hψ⟩
    apply Subtype.ext
    ext x
    simp

/-- A prime `q` of an integral `R`-algebra `B` lying over the kernel of `φ : R → K`, with `K`
algebraically closed, carries a geometric point of `Spec B` over `φ`. -/
theorem exists_ringHom_lift_of_prime {R B K : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsIntegral R B] [Field K] [IsAlgClosed K] (q : Ideal B) [q.IsPrime]
    (φ : R →+* K) (hφ : RingHom.ker φ = q.under R) :
    ∃ ψ : B →+* K, ψ.comp (algebraMap R B) = φ := by
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have : q.LiesOver (RingHom.ker φ) := ⟨hφ⟩
  let : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  have : FaithfulSMul (R ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective φ)
  let g : (B ⧸ q) →ₐ[R ⧸ RingHom.ker φ] K := IsAlgClosed.lift
  refine ⟨g.toRingHom.comp (Ideal.Quotient.mk q), RingHom.ext fun r => ?_⟩
  have h := g.commutes (Ideal.Quotient.mk (RingHom.ker φ) r)
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at h
  exact h.trans (RingHom.kerLift_mk φ r)

/-- If `Spec A → Spec R` is open, `R` is local and `A ≃ ∏ Bᵢ` with `Bᵢ` local and integral over
`R`, then every factor `Spec Bᵢ` has a geometric point over every geometric point of `Spec R`:
`Spec Bᵢ` is open in `Spec A`, so its image is an open set containing the closed point
(page 19 of the folder, and the reading's justification of it). -/
theorem nonempty_geomPoints_of_isOpenMap {R : Type*} [CommRing R] [IsLocalRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap R A)))
    {ι : Type*} {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, IsLocalRing (B i)] [∀ i, Algebra.IsIntegral R (B i)]
    (e : A ≃ₐ[R] ∀ i, B i) (i : ι) {K : Type*} [Field K] [IsAlgClosed K] (φ : R →+* K) :
    Nonempty (GeomPoints R (B i) φ) := by
  classical
  let π : A →+* B i := (Pi.evalRingHom B i).comp e.toAlgHom.toRingHom
  have hπ : Function.Surjective π := fun b => ⟨e.symm (Pi.single i b), by
    show e (e.symm (Pi.single i b)) i = b
    rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same]⟩
  have hπalg : π.comp (algebraMap R A) = algebraMap R (B i) := by
    refine RingHom.ext fun r => ?_
    exact congrFun (e.commutes r) i
  let ε : A := e.symm (Pi.single i 1)
  have hπε : π ε = 1 := by
    show e (e.symm (Pi.single i 1)) i = 1
    rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same]
  -- the kernel of `π` is killed by the idempotent `ε`
  have hker : ∀ x, π x = 0 → x * ε = 0 := by
    intro x hx
    have hx' : e x i = 0 := hx
    apply e.injective
    rw [map_mul, map_zero]
    funext j
    show e x j * e (e.symm (Pi.single i 1)) j = 0
    rw [AlgEquiv.apply_symm_apply]
    by_cases hj : j = i
    · rw [hj, Pi.single_eq_same, mul_one]
      exact hx'
    · rw [Pi.single_eq_of_ne hj, mul_zero]
  -- the closed point of `Spec R` is the image of a point of `D(ε) = Spec Bᵢ`
  let MA : PrimeSpectrum A := ⟨(maximalIdeal (B i)).comap π, inferInstance⟩
  have hMA : MA ∈ PrimeSpectrum.basicOpen ε := by
    rw [PrimeSpectrum.mem_basicOpen]
    intro h
    have h' : π ε ∈ maximalIdeal (B i) := h
    rw [hπε] at h'
    exact (maximalIdeal.isMaximal (B i)).ne_top ((Ideal.eq_top_iff_one _).mpr h')
  have hMAc : PrimeSpectrum.comap (algebraMap R A) MA = closedPoint R := by
    ext1
    show ((maximalIdeal (B i)).comap π).comap (algebraMap R A) = maximalIdeal R
    rw [Ideal.comap_comap, hπalg]
    exact eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R)
      (maximalIdeal (B i)))
  -- an open set containing the closed point is everything
  let p : PrimeSpectrum R := ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  have hp : p ∈ PrimeSpectrum.comap (algebraMap R A) ''
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum A)) := by
    have hsp : p ⤳ closedPoint R := (PrimeSpectrum.le_iff_specializes p (closedPoint R)).mp
      ((PrimeSpectrum.asIdeal_le_asIdeal p (closedPoint R)).mp
        (le_maximalIdeal p.isPrime.ne_top))
    exact hsp.mem_open (hopen _ PrimeSpectrum.isOpen_basicOpen) ⟨MA, hMA, hMAc⟩
  obtain ⟨P, hPε, hPp⟩ := hp
  have hPε' : ε ∉ P.asIdeal := (PrimeSpectrum.mem_basicOpen ε P).mp hPε
  -- push `P` down to a prime `q` of `Bᵢ` over `ker φ`
  have hkerP : RingHom.ker π ≤ P.asIdeal := by
    intro x hx
    have h0 : x * ε ∈ P.asIdeal := by
      rw [hker x (RingHom.mem_ker.mp hx)]
      exact P.asIdeal.zero_mem
    exact (P.isPrime.mem_or_mem h0).resolve_right hPε'
  have hq : (P.asIdeal.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ hkerP
  have hqP : (P.asIdeal.map π).comap π = P.asIdeal := by
    rw [Ideal.comap_map_of_surjective' π hπ, sup_eq_left.mpr hkerP]
  have hqunder : RingHom.ker φ = (P.asIdeal.map π).under R := by
    show RingHom.ker φ = (P.asIdeal.map π).comap (algebraMap R (B i))
    rw [← hπalg, ← Ideal.comap_comap, hqP]
    exact (congrArg PrimeSpectrum.asIdeal hPp).symm
  obtain ⟨ψ, hψ⟩ := exists_ringHom_lift_of_prime (P.asIdeal.map π) φ hqunder
  exact ⟨⟨ψ, hψ⟩⟩

/-- The structure map `R^ι → A ≃ ∏ᵢ Bᵢ` of the étale part: `Spec A → ∐_ι Spec R`, the arrow
`X → X^ét` of page 17 over a strictly henselian base, where `X^ét` is the trivial finite étale
cover with one sheet for each local factor. -/
def etalePartMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}
    {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (e : A ≃ₐ[R] ∀ i, B i) :
    (ι → R) →ₐ[R] A :=
  e.symm.toAlgHom.comp
    (AlgHom.pi fun i => (Algebra.ofId R (B i)).comp (Pi.evalAlgHom R (fun _ : ι => R) i))

/-- The `i`-th coordinate of `etalePartMap e y` is `y i`, seen in `Bᵢ`. -/
theorem etalePartMap_apply {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}
    {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (e : A ≃ₐ[R] ∀ i, B i)
    (y : ι → R) (i : ι) : e (etalePartMap e y) i = algebraMap R (B i) (y i) :=
  congrFun (e.apply_symm_apply (AlgHom.pi (fun i =>
    (Algebra.ofId R (B i)).comp (Pi.evalAlgHom R (fun _ : ι => R) i)) y)) i

/-- An `R`-algebra map from a split finite étale algebra `R^J` into a local `R`-algebra is the
evaluation at one point of `J`. -/
theorem exists_eq_ofId_comp_evalAlgHom {R T J : Type*} [CommRing R] [CommRing T]
    [IsLocalRing T] [Algebra R T] [Fintype J] (f : (J → R) →ₐ[R] T) :
    ∃ j, f = (Algebra.ofId R T).comp (Pi.evalAlgHom R (fun _ : J => R) j) := by
  classical
  obtain ⟨j, hj⟩ := exists_map_single_eq_one (B := fun _ : J => R) f.toRingHom
  refine ⟨j, AlgHom.ext fun x => ?_⟩
  have h1 : f x = f (Pi.single j (x j)) :=
    map_eq_map_single_apply (B := fun _ : J => R) f.toRingHom hj x
  have h2 : (Pi.single j (x j) : J → R) = x j • Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · rw [hk, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul, mul_one]
    · rw [Pi.smul_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, smul_zero]
  have hj' : f (Pi.single j 1) = 1 := hj
  show f x = algebraMap R T (x j)
  rw [h1, h2, map_smul, hj', Algebra.smul_def, mul_one]

/-- An `R`-algebra map `R^J → R^ι` over a local ring `R` is induced by a map `ι → J`. -/
theorem exists_apply_eq_of_algHom_pi {R : Type*} [CommRing R] [IsLocalRing R] {ι J : Type*}
    [Fintype J] (h : (J → R) →ₐ[R] (ι → R)) : ∃ τ : ι → J, ∀ x i, h x i = x (τ i) := by
  choose τ hτ using fun i =>
    exists_eq_ofId_comp_evalAlgHom ((Pi.evalAlgHom R (fun _ : ι => R) i).comp h)
  exact ⟨τ, fun x i => AlgHom.congr_fun (hτ i) x⟩

/-- The universal property of the étale part over a local base, for split finite étale algebras:
when `A ≃ ∏ᵢ Bᵢ` with `Bᵢ` local, every `R`-algebra map `R^J → A` factors uniquely through
`etalePartMap e : R^ι → A` (page 23: a `Y`-morphism from `X` to an étale `Y`-scheme factors
uniquely through `X^ét`). -/
theorem existsUnique_comp_etalePartMap_eq {R : Type*} [CommRing R] [IsLocalRing R]
    {A : Type*} [CommRing A] [Algebra R A] {ι : Type*} {B : ι → Type*} [∀ i, CommRing (B i)]
    [∀ i, Algebra R (B i)] [∀ i, IsLocalRing (B i)] (e : A ≃ₐ[R] ∀ i, B i) {J : Type*}
    [Fintype J] (f : (J → R) →ₐ[R] A) :
    ∃! g : (J → R) →ₐ[R] (ι → R), (etalePartMap e).comp g = f := by
  classical
  choose σ hσ using fun i =>
    exists_eq_ofId_comp_evalAlgHom ((Pi.evalAlgHom R B i).comp (e.toAlgHom.comp f))
  have hf : ∀ x i, e (f x) i = algebraMap R (B i) (x (σ i)) := fun x i =>
    AlgHom.congr_fun (hσ i) x
  refine ⟨AlgHom.pi fun i => Pi.evalAlgHom R (fun _ : J => R) (σ i), ?_, ?_⟩
  · refine AlgHom.ext fun x => e.injective ?_
    funext i
    exact (etalePartMap_apply e _ i).trans (hf x i).symm
  · intro g hg
    obtain ⟨τ, hτ⟩ := exists_apply_eq_of_algHom_pi g
    have hστ : ∀ i, τ i = σ i := by
      intro i
      by_contra hne
      have h1 := hf (Pi.single (σ i) 1) i
      rw [← hg, AlgHom.comp_apply, etalePartMap_apply, hτ, Pi.single_eq_same,
        Pi.single_eq_of_ne hne, map_zero, map_one] at h1
      exact zero_ne_one h1
    refine AlgHom.ext fun x => ?_
    funext i
    exact (hτ x i).trans (congrArg x (hστ i))

/-- **Folder 126, page 17, over a strictly henselian base.** Let `R` be strictly henselian local
and `A` a module-finite `R`-algebra such that `Spec A → Spec R` is open (what universal openness,
« univ. ouvert » — an uncertain reading — gives after base change to the strict henselisation)
and such that every geometric fibre has the same number `n` of geometric points. Then
`A ≃ ∏_{i ∈ ι} Bᵢ` with `|ι| = n` and each `Bᵢ` strictly henselian, local and finite over `R`;
each `Spec Bᵢ → Spec R` has exactly one geometric point over every geometric point (finite,
surjective, radicial: the arrow `X → X^ét` sheet by sheet), and `R^ι → A` is the étale part:
every `R`-algebra map `R^J → A` factors uniquely through it. -/
theorem radicial_etale_factorisation_of_strictlyHenselian
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] (n : ℕ)
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap R A)))
    (hconst : ∀ (K : Type u) [Field K] [IsAlgClosed K] (φ : R →+* K),
      Nat.card (GeomPoints R A φ) = n) :
    ∃ (ι : Type u) (_ : Fintype ι) (B : ι → Type u) (_ : ∀ i, CommRing (B i))
      (_ : ∀ i, Algebra R (B i)) (_ : ∀ i, StrictlyHenselianLocalRing (B i))
      (e : A ≃ₐ[R] ∀ i, B i),
      Fintype.card ι = n ∧ (∀ i, Module.Finite R (B i)) ∧
      (∀ i (K : Type u) [Field K] [IsAlgClosed K] (φ : R →+* K),
        Nat.card (GeomPoints R (B i) φ) = 1) ∧
      ∀ (J : Type u) [Fintype J] (f : (J → R) →ₐ[R] A),
        ∃! g : (J → R) →ₐ[R] (ι → R), (etalePartMap e).comp g = f := by
  obtain ⟨ι, hι, B, hBc, hBa, hBs, hBf, ⟨e⟩⟩ :=
    exists_algEquiv_pi_strictHenselian_of_module_finite R A
  let : Fintype ι := Fintype.ofFinite ι
  have hloc : ∀ i, IsLocalHom (algebraMap R (B i)) := fun i =>
    isLocalHom_algebraMap_of_finite_local R (B i)
  -- the geometric point over the closed point
  let k := AlgebraicClosure (ResidueField R)
  let φ₀ : R →+* k := (algebraMap (ResidueField R) k).comp (residue R)
  have hφ₀ : IsLocalHom φ₀ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h0 : residue R a = 0 :=
      (residue_eq_zero_iff a).mpr ((mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr hna))
    have h1 : φ₀ a = 0 := by
      show algebraMap (ResidueField R) k (residue R a) = 0
      rw [h0, map_zero]
    rw [h1] at ha
    exact not_isUnit_zero ha
  -- the closed fibre has exactly `|ι|` geometric points
  have hcard : Fintype.card ι = n := by
    rw [← hconst k φ₀, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (finiteAlgHomCharsEquiv B e φ₀)
  -- every factor has exactly one geometric point over every geometric point
  have hpts : ∀ i (K : Type u) [Field K] [IsAlgClosed K] (φ : R →+* K),
      Nat.card (GeomPoints R (B i) φ) = 1 := by
    intro i K _ _ φ
    have hne : ∀ j, Nonempty (GeomPoints R (B j) φ) := fun j =>
      nonempty_geomPoints_of_isOpenMap hopen e j φ
    have hSig : Nat.card (Σ j, GeomPoints R (B j) φ) = n :=
      (Nat.card_congr ((geomPointsCongr e φ).trans (geomPointsPiEquiv φ).symm)).symm.trans
        (hconst K φ)
    by_cases hn : n = 0
    · exact (Fintype.card_eq_zero_iff.mp (hcard.trans hn)).elim i
    have hfin : Finite (Σ j, GeomPoints R (B j) φ) :=
      Nat.finite_of_card_ne_zero (by rw [hSig]; exact hn)
    have hfin' : ∀ j, Finite (GeomPoints R (B j) φ) := fun j =>
      Finite.of_injective
        (fun x : GeomPoints R (B j) φ => (⟨j, x⟩ : Σ j, GeomPoints R (B j) φ))
        (fun x y h => by simpa using h)
    have hsum : ∑ j, Nat.card (GeomPoints R (B j) φ) = ∑ _j : ι, 1 := by
      rw [← Nat.card_sigma (β := fun j => GeomPoints R (B j) φ), hSig, ← hcard,
        Fintype.card_eq_sum_ones]
    have hle : ∀ j ∈ (Finset.univ : Finset ι), 1 ≤ Nat.card (GeomPoints R (B j) φ) := by
      intro j _
      have := hne j
      exact Nat.succ_le_of_lt (Nat.card_pos (α := GeomPoints R (B j) φ))
    exact ((Finset.sum_eq_sum_iff_of_le hle).mp hsum.symm i (Finset.mem_univ i)).symm
  exact ⟨ι, inferInstance, B, hBc, hBa, hBs, e, hcard, hBf, hpts,
    fun J _ f => existsUnique_comp_etalePartMap_eq e f⟩

end Grothendieck.Folder126RadicialEtale
