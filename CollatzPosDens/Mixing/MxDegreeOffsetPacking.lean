/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.S02DyadicReduction
public import CollatzPosDens.Transfer.ResidueMap
public import CollatzPosDens.Mixing.MxOffsetInjective
public import CollatzPosDens.Mixing.MxShResidueCount

/-!
# Joint degree and real-offset packing

Let `n ∈ ℕ`, `y ∈ G_n = ℤ/3^nℤ`, let `I` be a finite set of integers and `R ≥ 0` a real number.
Consider the words `u` of length `n` with `[off(u)]_n = y`, `A(u) ∈ I` and `off(u) ≤ R`. For a
fixed value `A = A(u)`, the numbers `t_u = 2^A off(u)` are distinct nonnegative integers in
`[0, 2^A R]`, all congruent to a representative of `[2^A]_n y` modulo `3^n`; hence there are at
most `2^A R 3^{-n} + 1` such words, each of geometric weight `2^{-A}`. Since `A(u) ≥ |u| = n`,
only the values `A ∈ I` with `A ≥ n` occur, and summing over them gives
$$3^n\,\mathbf p(\{u : |u| = n,\ [\mathrm{off}(u)]_n = y,\ A(u) \in I,\ \mathrm{off}(u) \le R\})
  \le \#I \cdot R + 3^n \sum_{A \in I,\ A \ge n} 2^{-A}.$$
For `I` a set of `D` consecutive integers, `#I = D`.

## Main results

* `CollatzPosDens.ncard_setOf_off_le_of_valSum_eq_le`: the words of length `n`, valuation sum
  `A`, offset residue `y` and offset at most `R` number at most `2^A R 3^{-n} + 1`.
* `CollatzPosDens.three_pow_mul_geomMass_offsetPacking_le`: the packing bound for an arbitrary
  finite set `I` of integers.
* `CollatzPosDens.three_pow_mul_geomMass_degreeOffsetPacking_le`: the packing bound for a set
  `I = {a, …, a + D - 1}` of `D` consecutive integers.

## Implementation notes

The geometric mass lives in `ℝ≥0∞`, so the bound is stated there, with the right-hand side
embedded by `ENNReal.ofReal`; it shows in particular that the mass is finite. The valuation sum is
a natural number and is compared with the integers of `I` through the cast `ℕ → ℤ`, and the
weight `2^{-A}` for `A ∈ ℤ` is the integer power `(2 : ℝ) ^ (-A)`. The offset residue
`[off(u)]_n` is `dyadicRed n` applied to `off(u) ∈ ℤ[1/2]`. The bounds hold without the
hypotheses `n ≥ 1` and `D ≥ 1`.

## References

* [Mazur, *Collatz positive density*], §12.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- For every word `w`, the rational number `off(w) 2^{A(w)}` is an integer. -/
theorem exists_intCast_eq_off_mul_two_pow_valSum (w : Word) :
    ∃ t : ℤ, off w * 2 ^ w.valSum = t := by
  rcases eq_or_ne w [] with rfl | hw
  · exact ⟨0, by simp⟩
  · obtain ⟨N, -, h⟩ := exists_odd_off_mul_two_pow_valSum hw
    exact ⟨N, by simp [h]⟩

/-- **Residue count of a degree slice.** Let `n, A ∈ ℕ`, `y ∈ G_n` and `R ≥ 0`. The words `u` of
length `n` with `[off(u)]_n = y`, `A(u) = A` and `off(u) ≤ R` number at most
`2^A R 3^{-n} + 1`. -/
theorem ncard_setOf_off_le_of_valSum_eq_le (n : ℕ) (y : ResidueGroup n) (A : ℕ) {R : ℝ}
    (hR : 0 ≤ R) :
    ({u : Word | u.length = n ∧ dyadicRed n ⟨off u, off_mem_dyadicRationals u⟩ = y ∧
        u.valSum = A ∧ (off u : ℝ) ≤ R}.ncard : ℝ) ≤ 2 ^ A * R * 3⁻¹ ^ n + 1 := by
  choose t ht using exists_intCast_eq_off_mul_two_pow_valSum
  set c : ℤ := ((y * 2 ^ A).val : ℤ)
  set T := {s : ℤ | (0 : ℝ) ≤ s ∧ (s : ℝ) ≤ 0 + 2 ^ A * R ∧ s ≡ c [ZMOD 3 ^ n]}
  have hmaps : ∀ u ∈ {u : Word | u.length = n ∧
      dyadicRed n ⟨off u, off_mem_dyadicRationals u⟩ = y ∧ u.valSum = A ∧ (off u : ℝ) ≤ R},
      t u ∈ T := by
    rintro u ⟨hlen, hy, hA, hoff⟩
    have htR : (t u : ℝ) = (off u : ℝ) * 2 ^ A := by
      rw [← hA]; exact_mod_cast (ht u).symm
    refine ⟨?_, ?_, ?_⟩
    · rw [htR]; exact mul_nonneg (by exact_mod_cast off_nonneg u) (by positivity)
    · rw [htR, zero_add, mul_comm (2 ^ A : ℝ)]
      exact mul_le_mul_of_nonneg_right hoff (by positivity)
    · have hsub : (⟨(t u : ℚ), by simp⟩ : dyadicRationals) =
          ⟨off u, off_mem_dyadicRationals u⟩ * 2 ^ A := by
        apply Subtype.ext
        have h2 : ((2 : dyadicRationals) : ℚ) = 2 := rfl
        simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow, h2, ← ht u, hA]
      have hred := dyadicRed_intCast n (t u)
      rw [hsub, map_mul, map_pow, map_ofNat, hy] at hred
      have hc : ((c : ℤ) : ResidueGroup n) = y * 2 ^ A := by
        simp only [c, Int.cast_natCast, ZMod.natCast_zmod_val]
      have := (ZMod.intCast_eq_intCast_iff (t u) c (3 ^ n)).1 (by rw [← hred, hc])
      simpa using this
  have hinj : Set.InjOn t {u : Word | u.length = n ∧
      dyadicRed n ⟨off u, off_mem_dyadicRationals u⟩ = y ∧ u.valSum = A ∧ (off u : ℝ) ≤ R} := by
    rintro u ⟨hlen, -, hA, -⟩ u' ⟨hlen', -, hA', -⟩ h
    refine off_injective_of_length_eq (hlen.trans hlen'.symm) ?_
    have e := ht u
    have e' := ht u'
    rw [h, hA, ← e', hA'] at e
    exact mul_right_cancel₀ (by positivity) e
  have hT : T.Finite := finite_setOf_modEq_of_mem_Icc _ _ _ _
  have hle := Set.ncard_le_ncard_of_injOn t hmaps hinj hT
  have hcount := ncard_setOf_modEq_pow_three_le n c (α := 0) (L := 2 ^ A * R) (by positivity)
  exact (Nat.cast_le.2 hle).trans hcount

/-- **Degree and real-offset packing, for a finite set of degrees.** Let `n ∈ ℕ`, `y ∈ G_n`,
`I` a finite set of integers and `R ≥ 0`. Then
`3^n 𝐩({u : |u| = n, [off(u)]_n = y, A(u) ∈ I, off(u) ≤ R}) ≤ #I R + 3^n ∑_{A ∈ I, A ≥ n} 2^{-A}`.
-/
theorem three_pow_mul_geomMass_offsetPacking_le (n : ℕ) (y : ResidueGroup n) (I : Finset ℤ)
    {R : ℝ} (hR : 0 ≤ R) :
    (3 : ℝ≥0∞) ^ n * geomMass {u : Word | u.length = n ∧
        dyadicRed n ⟨off u, off_mem_dyadicRationals u⟩ = y ∧ (u.valSum : ℤ) ∈ I ∧
        (off u : ℝ) ≤ R} ≤
      ENNReal.ofReal (I.card * R + 3 ^ n * ∑ A ∈ I with (n : ℤ) ≤ A, (2 : ℝ) ^ (-A)) := by
  set E := {u : Word | u.length = n ∧ dyadicRed n ⟨off u, off_mem_dyadicRationals u⟩ = y ∧
    (u.valSum : ℤ) ∈ I ∧ (off u : ℝ) ≤ R} with hE
  have hEfin : E.Finite := by
    refine (Word.finite_setOf_valSum_le (∑ A ∈ I, A.toNat)).subset ?_
    rintro u ⟨-, -, hI, -⟩
    have h := Finset.single_le_sum (f := fun A : ℤ => A.toNat) (fun _ _ => Nat.zero_le _) hI
    simpa using h
  set F := hEfin.toFinset
  have hEF : E = (F : Set Word) := hEfin.coe_toFinset.symm
  have hmass : geomMass E = ENNReal.ofReal (∑ w ∈ F, (2 : ℝ)⁻¹ ^ w.valSum) := by
    rw [hEF, ← toReal_geomMass_coe_finset, ENNReal.ofReal_toReal (geomMass_coe_finset_ne_top F)]
  have hfib : ∑ w ∈ F, (2 : ℝ)⁻¹ ^ w.valSum =
      ∑ A ∈ I, ∑ w ∈ F with (w.valSum : ℤ) = A, (2 : ℝ)⁻¹ ^ w.valSum :=
    (Finset.sum_fiberwise_of_maps_to (fun w hw => ((hEfin.mem_toFinset).1 hw).2.2.1) _).symm
  have hslice : ∀ A ∈ I, (3 : ℝ) ^ n * ∑ w ∈ F with (w.valSum : ℤ) = A, (2 : ℝ)⁻¹ ^ w.valSum ≤
      if (n : ℤ) ≤ A then R + 3 ^ n * (2 : ℝ) ^ (-A) else 0 := by
    intro A _
    split_ifs with hnA
    · obtain ⟨B, rfl⟩ : ∃ B : ℕ, A = B := ⟨A.toNat, by omega⟩
      have hsum : ∑ w ∈ F with (w.valSum : ℤ) = B, (2 : ℝ)⁻¹ ^ w.valSum =
          (F.filter fun w => (w.valSum : ℤ) = B).card * (2 : ℝ)⁻¹ ^ B := by
        rw [Finset.sum_congr rfl fun w hw => by
          rw [show w.valSum = B by exact_mod_cast (Finset.mem_filter.1 hw).2],
          Finset.sum_const, nsmul_eq_mul]
      have hcard : ((F.filter fun w => (w.valSum : ℤ) = B).card : ℝ) ≤
          2 ^ B * R * 3⁻¹ ^ n + 1 := by
        refine le_trans ?_ (ncard_setOf_off_le_of_valSum_eq_le n y B hR)
        rw [← Set.ncard_coe_finset]
        refine Nat.cast_le.2 (Set.ncard_le_ncard ?_ ((Word.finite_setOf_valSum_le B).subset
          fun u hu => hu.2.2.1.le))
        intro u hu
        obtain ⟨hu, hB⟩ := Finset.mem_filter.1 hu
        obtain ⟨h1, h2, -, h4⟩ := (hEfin.mem_toFinset).1 hu
        exact ⟨h1, h2, by exact_mod_cast hB, h4⟩
      rw [hsum, zpow_neg, zpow_natCast, ← inv_pow]
      have h3 : (3 : ℝ) ^ n * 3⁻¹ ^ n = 1 := by rw [← mul_pow]; norm_num
      have h2 : (2 : ℝ) ^ B * 2⁻¹ ^ B = 1 := by rw [← mul_pow]; norm_num
      calc (3 : ℝ) ^ n * (((F.filter fun w => (w.valSum : ℤ) = B).card : ℝ) * 2⁻¹ ^ B)
          ≤ 3 ^ n * ((2 ^ B * R * 3⁻¹ ^ n + 1) * 2⁻¹ ^ B) := by gcongr
        _ = R * ((3 ^ n * 3⁻¹ ^ n) * (2 ^ B * 2⁻¹ ^ B)) + 3 ^ n * 2⁻¹ ^ B := by ring
        _ = R + 3 ^ n * 2⁻¹ ^ B := by rw [h3, h2]; ring
    · have hempty : (F.filter fun w => (w.valSum : ℤ) = A) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun w hw hA => hnA ?_
        rw [← hA, ← ((hEfin.mem_toFinset).1 hw).1]
        exact_mod_cast Word.length_le_valSum w
      rw [hempty, Finset.sum_empty, mul_zero]
  have hreal : (3 : ℝ) ^ n * ∑ w ∈ F, (2 : ℝ)⁻¹ ^ w.valSum ≤
      I.card * R + 3 ^ n * ∑ A ∈ I with (n : ℤ) ≤ A, (2 : ℝ) ^ (-A) := by
    rw [hfib, Finset.mul_sum]
    refine (Finset.sum_le_sum hslice).trans ?_
    rw [← Finset.sum_filter, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum]
    gcongr
    exact Finset.filter_subset _ _
  rw [hmass, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Joint degree and real-offset packing.** Let `n ∈ ℕ`, let `I = {a, …, a + D - 1}` be a set of
`D` consecutive integers and let `R ≥ 0` be real. Then for every `y ∈ G_n`,
`3^n 𝐩({u ∈ ℤ_{≥1}^n : [off(u)]_n = y, A(u) ∈ I, off(u) ≤ R}) ≤ D R + 3^n ∑_{A ∈ I, A ≥ n} 2^{-A}`.
-/
@[collatz_pos_dens "lem_mx_degree_offset_packing"]
theorem three_pow_mul_geomMass_degreeOffsetPacking_le (n : ℕ) (a : ℤ) (D : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (y : ResidueGroup n) :
    (3 : ℝ≥0∞) ^ n * geomMass {u : Word | u.length = n ∧
        dyadicRed n ⟨off u, off_mem_dyadicRationals u⟩ = y ∧
        (u.valSum : ℤ) ∈ Finset.Ico a (a + D) ∧ (off u : ℝ) ≤ R} ≤
      ENNReal.ofReal (D * R +
        3 ^ n * ∑ A ∈ Finset.Ico a (a + D) with (n : ℤ) ≤ A, (2 : ℝ) ^ (-A)) := by
  have h := three_pow_mul_geomMass_offsetPacking_le n y (Finset.Ico a (a + D)) hR
  rwa [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] at h

end CollatzPosDens
