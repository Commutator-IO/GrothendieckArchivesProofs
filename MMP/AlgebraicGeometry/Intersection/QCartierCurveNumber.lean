module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
public import MMP.AlgebraicGeometry.Intersection.InvertibleSheafCurveDegree

/-!
# Intersection numbers of `ℚ`-Cartier divisors with curves

Let `X` be a normal scheme of finite type over a field `k`, `C ⊆ X` a closed curve proper over
`k`, and `D` a `ℚ`-Cartier `ℚ`-divisor on `X` with Cartier index `m_D`. Then `m_D D` is a Cartier
divisor, so `𝒪_X(m_D D)` is invertible, and the *intersection number* of `D` and `C` is
`(D · C) = (1 / m_D) · deg_C 𝒪_X(m_D D) ∈ ℚ`.

When the degree `deg_C 𝒪_X(-)` is additive on Cartier divisors, the intersection number may be
computed with any positive multiple `m` making `mD` Cartier, and it is additive in `D`.

A Cartier divisor `L` on `X` is *`f`-ample* for a morphism `f : X ⟶ Y` if its invertible sheaf
`𝒪_X(L)` is, and *ample over* an open `U ⊆ Y` if `𝒪_X(L)` is ample over `U`.

## Main definitions

* `MMP.Mori.QDivisor.IsCartierDivisor.toDivisor`: the integral divisor underlying a `ℚ`-divisor
  which is a Cartier divisor.
* `MMP.Mori.Divisor.degreeOn`: the degree `deg_C 𝒪_X(D)` of a Cartier divisor `D` along a curve.
* `MMP.Mori.QDivisor.intersectionNumber`: the intersection number `(D · C)`.
* `MMP.Mori.Divisor.IsRelativelyAmple`, `MMP.Mori.Divisor.IsAmpleOver`: relatively ample Cartier
  divisors.

## Main results

* `MMP.Mori.QDivisor.cartierIndex_mul_intersectionNumber`: `m_D · (D · C) = deg_C 𝒪_X(m_D D)`.
* `MMP.Mori.QDivisor.intersectionNumber_toQDivisor`: for a Cartier divisor `E`,
  `(E · C) = deg_C 𝒪_X(E)`.
* `MMP.Mori.QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul`: if the degree is additive,
  `(D · C) = (1 / m) · deg_C 𝒪_X(mD)` for every `m > 0` such that `mD` is Cartier.
* `MMP.Mori.QDivisor.intersectionNumber_add`: if the degree is additive, so is `(D · C)`.

## Implementation notes

The curve is a morphism `i : C ⟶ X` from a scheme of dimension at most one, proper over `k`
through `X`, as for `MMP.Mori.degreeOn`; a closed curve `C ⊆ X` is the case of a closed
immersion. Of the finite-type hypothesis on `X` only quasi-compactness of the structure morphism
is used, to make `X` quasi-compact, which the invertibility of `𝒪_X(D)` for Cartier `D` requires;
local Noetherianity, which finite type over `k` also gives
(`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`), is the standing hypothesis under
which divisors and the Cartier condition are defined.

Additivity of the degree, `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')` for Cartier `E`,
`E'`, is a hypothesis of the results that need it. It combines `𝒪_X(E + E') ≅ 𝒪_X(E) ⊗ 𝒪_X(E')`
[Har77, II.6.13] with the additivity of the degree on tensor products of invertible sheaves on a
proper curve [Stacks, Tag 0AYX].

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4,
  1.33–1.34, Proposition 1.41, Theorem 1.42
* [R. Hartshorne, *Algebraic geometry*][Har77], II.6.11–II.6.13, II.7
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

variable {X : Scheme.{u}}

/-! ### The integral divisor of a Cartier `ℚ`-divisor -/

namespace QDivisor

section Integral

variable [IsLocallyNoetherian X] [IsNormal X]

/-- The integral divisor `D'` with `D = D'` as `ℚ`-divisors, for a `ℚ`-divisor `D` which is a
Cartier divisor; it is unique (`MMP.Mori.QDivisor.IsCartierDivisor.toDivisor_eq_iff`). -/
def IsCartierDivisor.toDivisor {D : QDivisor X} (h : D.IsCartierDivisor) : Divisor X :=
  Classical.choose h

/-- The integral divisor `h.toDivisor` is `D` as a `ℚ`-divisor. -/
theorem IsCartierDivisor.toQDivisor_toDivisor {D : QDivisor X} (h : D.IsCartierDivisor) :
    Divisor.toQDivisor h.toDivisor = D :=
  (Classical.choose_spec h).1

/-- The integral divisor `h.toDivisor` is Cartier. -/
theorem IsCartierDivisor.isCartier_toDivisor {D : QDivisor X} (h : D.IsCartierDivisor) :
    h.toDivisor.IsCartier :=
  (Classical.choose_spec h).2

/-- An integral divisor `E` equals `h.toDivisor` if and only if `E = D` as `ℚ`-divisors. -/
theorem IsCartierDivisor.toDivisor_eq_iff {D : QDivisor X} (h : D.IsCartierDivisor)
    {E : Divisor X} : h.toDivisor = E ↔ Divisor.toQDivisor E = D := by
  refine ⟨fun h' => h' ▸ h.toQDivisor_toDivisor, fun h' => ?_⟩
  exact Divisor.toQDivisor_injective (by rw [h.toQDivisor_toDivisor, h'])

/-- A Cartier divisor has Cartier index one. -/
theorem cartierIndex_toQDivisor {D : Divisor X} (h : D.IsCartier)
    (h' : (Divisor.toQDivisor D).IsQCartier) : (Divisor.toQDivisor D).cartierIndex h' = 1 :=
  le_antisymm (cartierIndex_le h' one_pos (by
    rw [Nat.cast_one, one_smul]; exact isCartierDivisor_toQDivisor.mpr h)) (cartierIndex_pos h')

end Integral

end QDivisor

/-! ### Degrees of Cartier divisors and intersection numbers -/

section Degree

variable (k : Type u) [Field k] {C : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
  [IsLocallyNoetherian X] [IsNormal X]

namespace Divisor

/-- The degree `deg_C 𝒪_X(D)` of the invertible sheaf of a Cartier divisor `D` on a normal
`k`-scheme `X`, quasi-compact over `k`, along a curve `i : C ⟶ X` proper over `k`. -/
def degreeOn (D : Divisor X) (hD : D.IsCartier) : ℤ :=
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := hD.isInvertibleModule_divisorialSheaf
  Mori.degreeOn k sX i hdim D.divisorialSheaf

variable {k sX i hdim} in
/-- The degree depends only on the divisor. -/
theorem degreeOn_congr {D E : Divisor X} (h : D = E) (hD : D.IsCartier) (hE : E.IsCartier) :
    D.degreeOn k sX i hdim hD = E.degreeOn k sX i hdim hE := by
  subst h; rfl

/-- If the degree is additive on Cartier divisors, the degree of `0` is zero. -/
theorem degreeOn_zero
    (hadd : ∀ (E E' : Divisor X) (hE : E.IsCartier) (hE' : E'.IsCartier),
      (E + E').degreeOn k sX i hdim (hE.add hE') =
        E.degreeOn k sX i hdim hE + E'.degreeOn k sX i hdim hE') :
    (0 : Divisor X).degreeOn k sX i hdim isCartier_zero = 0 := by
  have h := hadd 0 0 isCartier_zero isCartier_zero
  rw [degreeOn_congr (add_zero 0) _ isCartier_zero] at h
  omega

/-- If the degree is additive on Cartier divisors, then `deg_C 𝒪_X(nD) = n · deg_C 𝒪_X(D)`. -/
theorem degreeOn_nsmul
    (hadd : ∀ (E E' : Divisor X) (hE : E.IsCartier) (hE' : E'.IsCartier),
      (E + E').degreeOn k sX i hdim (hE.add hE') =
        E.degreeOn k sX i hdim hE + E'.degreeOn k sX i hdim hE')
    (D : Divisor X) (hD : D.IsCartier) (n : ℕ) :
    (n • D).degreeOn k sX i hdim (hD.nsmul n) = n * D.degreeOn k sX i hdim hD := by
  induction n with
  | zero =>
    rw [degreeOn_congr (zero_nsmul D) _ isCartier_zero, degreeOn_zero k sX i hdim hadd]
    simp
  | succ n ih =>
    rw [degreeOn_congr (succ_nsmul D n) _ ((hD.nsmul n).add hD), hadd _ _ (hD.nsmul n) hD, ih]
    push_cast; ring

end Divisor

namespace QDivisor

/-- The *intersection number* `(D · C) = (1 / m_D) · deg_C 𝒪_X(m_D D)` of a `ℚ`-Cartier
`ℚ`-divisor `D`, with Cartier index `m_D`, on a normal `k`-scheme `X`, quasi-compact over `k`, and
a curve `i : C ⟶ X` proper over `k`. -/
@[mmp "def_km0_intersection_number_curve"]
def intersectionNumber (D : QDivisor X) (hD : D.IsQCartier) : ℚ :=
  ((isCartierDivisor_cartierIndex_smul hD).toDivisor.degreeOn k sX i hdim
      (isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor : ℚ) / D.cartierIndex hD

/-- The intersection number computed from any integral divisor `E` equal to `m_D D`. -/
theorem intersectionNumber_eq_of_toQDivisor_eq (D : QDivisor X) (hD : D.IsQCartier)
    (E : Divisor X) (hE : E.IsCartier)
    (h : Divisor.toQDivisor E = ((D.cartierIndex hD : ℕ) : ℤ) • D) :
    D.intersectionNumber k sX i hdim hD = (E.degreeOn k sX i hdim hE : ℚ) / D.cartierIndex hD := by
  rw [intersectionNumber, Divisor.degreeOn_congr
    (((isCartierDivisor_cartierIndex_smul hD).toDivisor_eq_iff).mpr h) _ hE]

/-- `m_D · (D · C) = deg_C 𝒪_X(m_D D)`. -/
theorem cartierIndex_mul_intersectionNumber (D : QDivisor X) (hD : D.IsQCartier) :
    (D.cartierIndex hD : ℚ) * D.intersectionNumber k sX i hdim hD =
      (isCartierDivisor_cartierIndex_smul hD).toDivisor.degreeOn k sX i hdim
        (isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor := by
  have := cartierIndex_pos hD
  rw [intersectionNumber, mul_div_cancel₀]
  exact_mod_cast this.ne'

/-- For a Cartier divisor `E`, `(E · C) = deg_C 𝒪_X(E)`. -/
theorem intersectionNumber_toQDivisor (E : Divisor X) (hE : E.IsCartier)
    (h : (Divisor.toQDivisor E).IsQCartier) :
    (Divisor.toQDivisor E).intersectionNumber k sX i hdim h = E.degreeOn k sX i hdim hE := by
  rw [intersectionNumber_eq_of_toQDivisor_eq k sX i hdim _ h E hE
    (by rw [cartierIndex_toQDivisor hE h, Nat.cast_one, one_smul]),
    cartierIndex_toQDivisor hE h, Nat.cast_one, div_one]

/-- **Independence of the multiplier.** If the degree is additive on Cartier divisors, then
`(D · C) = (1 / m) · deg_C 𝒪_X(mD)` for every `m > 0` such that `mD` is a Cartier divisor `E`. -/
theorem intersectionNumber_eq_of_toQDivisor_eq_smul
    (hadd : ∀ (E E' : Divisor X) (hE : E.IsCartier) (hE' : E'.IsCartier),
      (E + E').degreeOn k sX i hdim (hE.add hE') =
        E.degreeOn k sX i hdim hE + E'.degreeOn k sX i hdim hE')
    (D : QDivisor X) (hD : D.IsQCartier) {m : ℕ} (hm : 0 < m) (E : Divisor X)
    (hE : E.IsCartier) (h : Divisor.toQDivisor E = (m : ℤ) • D) :
    D.intersectionNumber k sX i hdim hD = (E.degreeOn k sX i hdim hE : ℚ) / m := by
  set hF := isCartierDivisor_cartierIndex_smul hD
  set F := hF.toDivisor
  set n := D.cartierIndex hD
  have hn : 0 < n := cartierIndex_pos hD
  have hFE : m • F = n • E := by
    apply Divisor.toQDivisor_injective
    rw [map_nsmul, map_nsmul, hF.toQDivisor_toDivisor, h, ← natCast_zsmul, ← natCast_zsmul,
      smul_smul, smul_smul, mul_comm]
  have key : (m : ℤ) * F.degreeOn k sX i hdim hF.isCartier_toDivisor =
      n * E.degreeOn k sX i hdim hE := by
    rw [← Divisor.degreeOn_nsmul k sX i hdim hadd, ← Divisor.degreeOn_nsmul k sX i hdim hadd,
      Divisor.degreeOn_congr hFE]
  rw [intersectionNumber, div_eq_div_iff (by exact_mod_cast hn.ne') (by exact_mod_cast hm.ne')]
  have key' : ((m : ℤ) : ℚ) * (F.degreeOn k sX i hdim hF.isCartier_toDivisor : ℚ) =
      ((n : ℤ) : ℚ) * (E.degreeOn k sX i hdim hE : ℚ) := by exact_mod_cast key
  push_cast at key'
  linarith

/-- A sum of `ℚ`-Cartier `ℚ`-divisors is `ℚ`-Cartier. -/
theorem IsQCartier.add {D D' : QDivisor X} (hD : D.IsQCartier) (hD' : D'.IsQCartier) :
    (D + D').IsQCartier := by
  obtain ⟨m, hm, E, hE, hEC⟩ := hD
  obtain ⟨m', hm', E', hE', hE'C⟩ := hD'
  refine ⟨m * m', mul_ne_zero hm hm', m' • E + m • E', ?_, (hEC.zsmul m').add (hE'C.zsmul m)⟩
  rw [map_add, map_zsmul, map_zsmul, hE, hE', smul_add, smul_smul, smul_smul, mul_comm m' m]

/-- **Additivity.** If the degree is additive on Cartier divisors, then
`((D + D') · C) = (D · C) + (D' · C)`. -/
theorem intersectionNumber_add
    (hadd : ∀ (E E' : Divisor X) (hE : E.IsCartier) (hE' : E'.IsCartier),
      (E + E').degreeOn k sX i hdim (hE.add hE') =
        E.degreeOn k sX i hdim hE + E'.degreeOn k sX i hdim hE')
    (D D' : QDivisor X) (hD : D.IsQCartier) (hD' : D'.IsQCartier) (hDD' : (D + D').IsQCartier) :
    (D + D').intersectionNumber k sX i hdim hDD' =
      D.intersectionNumber k sX i hdim hD + D'.intersectionNumber k sX i hdim hD' := by
  have hF := isCartierDivisor_cartierIndex_smul hD
  have hF' := isCartierDivisor_cartierIndex_smul hD'
  have hn : 0 < D.cartierIndex hD := cartierIndex_pos hD
  have hn' : 0 < D'.cartierIndex hD' := cartierIndex_pos hD'
  have hG : (D'.cartierIndex hD' • hF.toDivisor + D.cartierIndex hD • hF'.toDivisor).IsCartier :=
    (hF.isCartier_toDivisor.nsmul _).add (hF'.isCartier_toDivisor.nsmul _)
  rw [intersectionNumber_eq_of_toQDivisor_eq_smul k sX i hdim hadd (D + D') hDD'
      (Nat.mul_pos hn hn') _ hG (by
        rw [map_add, map_nsmul, map_nsmul, hF.toQDivisor_toDivisor, hF'.toQDivisor_toDivisor,
          ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, smul_add, Nat.cast_mul,
          mul_comm ((D'.cartierIndex hD' : ℕ) : ℤ)]),
    hadd _ _ (hF.isCartier_toDivisor.nsmul _) (hF'.isCartier_toDivisor.nsmul _),
    Divisor.degreeOn_nsmul k sX i hdim hadd _ hF.isCartier_toDivisor,
    Divisor.degreeOn_nsmul k sX i hdim hadd _ hF'.isCartier_toDivisor,
    intersectionNumber_eq_of_toQDivisor_eq k sX i hdim D hD _ hF.isCartier_toDivisor
      hF.toQDivisor_toDivisor,
    intersectionNumber_eq_of_toQDivisor_eq k sX i hdim D' hD' _ hF'.isCartier_toDivisor
      hF'.toQDivisor_toDivisor]
  have h1 : (D.cartierIndex hD : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : (D'.cartierIndex hD' : ℚ) ≠ 0 := by exact_mod_cast hn'.ne'
  push_cast
  field_simp

end QDivisor

end Degree

/-! ### Relatively ample Cartier divisors -/

namespace Divisor

variable [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- A Cartier divisor `L` on `X` is *`f`-ample* for `f : X ⟶ Y` if every point of `Y` has an
affine open neighbourhood `V` such that the restriction of `𝒪_X(L)` to `f⁻¹(V)` is ample. -/
@[mmp "def_km1b_relatively_ample"]
def IsRelativelyAmple {Y : Scheme.{u}} (f : X ⟶ Y) (L : Divisor X) (hL : L.IsCartier) : Prop :=
  haveI := hL.isInvertibleModule_divisorialSheaf
  _root_.MMP.Mori.IsRelativelyAmple f L.divisorialSheaf

/-- A Cartier divisor `L` on `X` is *ample over* an open `U` of `Y` if its restriction to `f⁻¹(U)`
is ample relative to the restriction `f ∣_ U : f⁻¹(U) ⟶ U` of `f`, that is, if the restriction of
`𝒪_X(L)` to `f⁻¹(U)` is. -/
@[mmp "def_km1b_relatively_ample"]
def IsAmpleOver {Y : Scheme.{u}} (f : X ⟶ Y) (L : Divisor X) (hL : L.IsCartier) (U : Y.Opens) :
    Prop :=
  haveI := hL.isInvertibleModule_divisorialSheaf
  _root_.MMP.Mori.IsAmpleOver f L.divisorialSheaf U

variable {Y : Scheme.{u}} (f : X ⟶ Y) (L : Divisor X) (hL : L.IsCartier)

/-- A Cartier divisor is `f`-ample if and only if its invertible sheaf is. -/
theorem isRelativelyAmple_iff :
    L.IsRelativelyAmple f hL ↔
      haveI := hL.isInvertibleModule_divisorialSheaf
      _root_.MMP.Mori.IsRelativelyAmple f L.divisorialSheaf :=
  Iff.rfl

/-- A Cartier divisor is ample over `U` if and only if its invertible sheaf is. -/
theorem isAmpleOver_iff (U : Y.Opens) :
    L.IsAmpleOver f hL U ↔
      haveI := hL.isInvertibleModule_divisorialSheaf
      _root_.MMP.Mori.IsAmpleOver f L.divisorialSheaf U :=
  Iff.rfl

end Divisor

end MMP.Mori
