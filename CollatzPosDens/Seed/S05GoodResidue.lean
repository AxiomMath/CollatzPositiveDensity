/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.NstarRange
public import CollatzPosDens.Recipe.PhQstarFloor
public import CollatzPosDens.Recipe.Qstar
public import CollatzPosDens.Seed.Pullback
public import CollatzPosDens.Seed.PullbackMean
public import CollatzPosDens.Seed.S05TupleMass
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# A favourable residue

There is a residue `y ∈ G_{q_*}` at which the pulled-back reference density satisfies
`Ψ(y) > 13/15`.

Let `Y ⊆ G_{q_*}` be the cylinder of the residues `y` with `ỹ ≡ 6275 (mod 3^8)`. As
`q_* ≥ 352 ≥ 8`, `Y` is a fibre of the reduction modulo `3^8` and has `3^{q_* - 8}` elements.
The sum of `Ψ` over `Y` is `3^{q_*}` times the mass of the selected tuples of generation `N_*`
in the cylinder `pr_8 = [6275]_8`, and, as `N_* ≥ j_e`, this mass exceeds
$$\mu = \Bigl(\frac{617014680840434}{2^{62}} - \frac1{20000000}\Bigr)
  \Bigl(\frac{199}{200} - 2^{-592}\Bigr).$$
So the average of `Ψ` over `Y` exceeds `3^8 μ = 6561 μ`, and the exact rational comparison
`6561 μ > 13/15 + 2^{-28}` (the left side is `0.87310…`, the right side `0.86666…`) gives a
`y ∈ Y` with `Ψ(y) > 13/15 + 2^{-28} > 13/15`.

## Main results

* `CollatzPosDens.exists_lt_of_card_mul_lt_sum_filter`: a function whose sum over a fibre of the
  reduction modulo `3^m` exceeds `3^{q-m} c` exceeds `c` somewhere on that fibre.
* `CollatzPosDens.lt_sum_filter_selectedTuples`: the mass bound of the selected tuples in the
  cylinder as a real inequality.
* `CollatzPosDens.add_two_inv_pow_lt_mul_cylinderMass`: the comparison `6561 μ > 13/15 + 2^{-28}`.
* `CollatzPosDens.exists_lt_pullbackDensity`: some `y ∈ G_{q_*}` has `Ψ(y) > 13/15`.

## Implementation notes

The comparison `6561 μ > 13/15 + 2^{-28}` is reduced to the case `2^{-592} = 2^{-20}`, which
only lowers `μ`, and is then a single comparison of natural numbers after clearing denominators.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

open scoped ENNReal

/-- A real function on `G_q` whose sum over the fibre of `r ∈ G_m` under `π_{q,m}` exceeds
`3^{q-m} c` exceeds `c` at some point of that fibre. -/
theorem exists_lt_of_card_mul_lt_sum_filter {m q : ℕ} [NeZero (3 ^ q)] (h : m ≤ q)
    (r : ResidueGroup m) {f : ResidueGroup q → ℝ} {c : ℝ}
    (hc : (3 : ℝ) ^ (q - m) * c < ∑ y with residueReduction h y = r, f y) :
    ∃ y, residueReduction h y = r ∧ c < f y := by
  have hcard : #{y : ResidueGroup q | residueReduction h y = r} = 3 ^ (q - m) :=
    card_filter_residueReduction_eq h r
  have hconst : ∑ _y : ResidueGroup q with residueReduction h _y = r, c =
      (3 : ℝ) ^ (q - m) * c := by
    rw [sum_const, hcard, nsmul_eq_mul]
    push_cast
    rfl
  obtain ⟨y, hy, hlt⟩ := exists_lt_of_sum_lt (hconst.trans_lt hc)
  exact ⟨y, (mem_filter.1 hy).2, hlt⟩

/-- The mass bound of the selected tuples in the cylinder as a real inequality: for `n ≥ j_e`,
`μ < ∑_{τ ∈ 𝔗_n, |ŵ(τ)| ≥ 8, pr_8(ŵ(τ)) = [6275]_8} 2^{-A(ŵ(τ))}` with
`μ = (617014680840434/2^62 - 1/20000000)(199/200 - 2^{-592})`. -/
theorem lt_sum_filter_selectedTuples (n : ℕ) (hn : selEnd ≤ n) :
    ((617014680840434 / 2 ^ 62 : ℝ) - 1 / 20000000) * (199 / 200 - (2 : ℝ)⁻¹ ^ 592) <
      ∑ τ ∈ (selectedTuples_finite n).toFinset with
          8 ≤ (concatWord τ).length ∧
            prefixResidue 8 (concatWord τ) = dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩,
        (2 : ℝ) ^ (-((concatWord τ).valSum : ℤ)) := by
  have h := two_inv_pow_lt_tsum_selectedTuples n hn
  set s := (selectedTuples_finite n).toFinset.filter fun τ => 8 ≤ (concatWord τ).length ∧
    prefixResidue 8 (concatWord τ) = dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩ with hs_def
  have hs : {τ : Fin n → Word | τ ∈ selectedTuples n ∧ 8 ≤ (concatWord τ).length ∧
      prefixResidue 8 (concatWord τ) = dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩} =
      (s : Set (Fin n → Word)) := by
    rw [hs_def, coe_filter]
    ext τ
    simp only [Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
  have heq : ∑' τ : {τ : Fin n → Word | τ ∈ selectedTuples n ∧
        8 ≤ (concatWord τ).length ∧
          prefixResidue 8 (concatWord τ) = dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩},
      (2⁻¹ : ℝ≥0∞) ^ (concatWord (τ : Fin n → Word)).valSum =
      ∑ τ ∈ s, (2⁻¹ : ℝ≥0∞) ^ (concatWord τ).valSum := by
    rw [← Finset.tsum_subtype s (fun τ => (2⁻¹ : ℝ≥0∞) ^ (concatWord τ).valSum), hs]
    rfl
  rw [heq] at h
  have hR : (617014680840434 / 2 ^ 62 : ℝ≥0∞) - 20000000⁻¹ =
      ENNReal.ofReal (617014680840434 / 2 ^ 62 - 1 / 20000000) := by
    rw [ENNReal.ofReal_sub _ (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num),
      ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, one_div,
      ENNReal.ofReal_pow (by norm_num)]
    norm_num
  have hP : (199 / 200 : ℝ≥0∞) - 2⁻¹ ^ 592 = ENNReal.ofReal (199 / 200 - (2⁻¹) ^ 592) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_div_of_pos (by norm_num),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [hR, hP, ← ENNReal.ofReal_mul (by norm_num)] at h
  have hne : ∑ τ ∈ s, (2⁻¹ : ℝ≥0∞) ^ (concatWord τ).valSum ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun _ _ => ENNReal.pow_ne_top (by simp)
  have hpos : (0 : ℝ) ≤ (617014680840434 / 2 ^ 62 - 1 / 20000000) * (199 / 200 - (2⁻¹) ^ 592) := by
    have hp : (2⁻¹ : ℝ) ^ 592 ≤ 2⁻¹ ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
    generalize (2⁻¹ : ℝ) ^ 592 = x at hp ⊢
    norm_num at hp ⊢
    nlinarith
  have h' := (ENNReal.ofReal_lt_iff_lt_toReal hpos hne).1 h
  rw [ENNReal.toReal_sum fun _ _ => ENNReal.pow_ne_top (by simp)] at h'
  refine h'.trans_eq (sum_congr rfl fun τ _ => ?_)
  rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, zpow_neg, zpow_natCast,
    inv_pow]

/-- The comparison `6561 μ > 13/15 + 2^{-28}` with `2^{-592}` replaced by `2^{-20}`, as an exact
comparison of natural numbers after clearing the denominators: with
`a = 617014680840434 · 20000000 - 2^62` and `b = 199 · 2^20 - 200`,
`(13 · 2^28 + 15) · (2^62 · 20000000 · 200 · 2^20) < 15 · 2^28 · 3^8 · a · b`. -/
private theorem cylinderMass_nat_lt :
    (13 * 2 ^ 28 + 15) * (2 ^ 62 * 20000000 * 200 * 2 ^ 20) <
      15 * 2 ^ 28 * 3 ^ 8 * (12335681930790252612096 * 208666424) := by
  norm_num

/-- The exact rational comparison `6561 μ > 13/15 + 2^{-28}` for
`μ = (617014680840434/2^62 - 1/20000000)(199/200 - 2^{-592})`. -/
theorem add_two_inv_pow_lt_mul_cylinderMass :
    (13 / 15 : ℝ) + (2 : ℝ)⁻¹ ^ 28 <
      3 ^ 8 *
        (((617014680840434 / 2 ^ 62 : ℝ) - 1 / 20000000) * (199 / 200 - (2 : ℝ)⁻¹ ^ 592)) := by
  have hp : (2⁻¹ : ℝ) ^ 592 ≤ 2⁻¹ ^ 20 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
  have hA : (617014680840434 / 2 ^ 62 : ℝ) - 1 / 20000000 =
      (12335681930790252612096 : ℕ) / (2 ^ 62 * 20000000) := by
    norm_num
  have hB : (199 / 200 : ℝ) - 2⁻¹ ^ 20 = (208666424 : ℕ) / (200 * 2 ^ 20) := by
    norm_num
  have hL : (13 / 15 : ℝ) + 2⁻¹ ^ 28 = ((13 * 2 ^ 28 + 15 : ℕ) : ℝ) / (15 * 2 ^ 28) := by
    norm_num
  have hApos : (0 : ℝ) ≤ (617014680840434 / 2 ^ 62 : ℝ) - 1 / 20000000 := by
    rw [hA]
    positivity
  have hkey : (13 / 15 : ℝ) + (2 : ℝ)⁻¹ ^ 28 <
      3 ^ 8 * (((617014680840434 / 2 ^ 62 : ℝ) - 1 / 20000000) * (199 / 200 - (2 : ℝ)⁻¹ ^ 20)) := by
    rw [hA, hB, hL, div_mul_div_comm, mul_div_assoc', div_lt_div_iff₀ (by positivity)
      (by positivity)]
    have h := (Nat.cast_lt (α := ℝ)).2 cylinderMass_nat_lt
    push_cast at h ⊢
    linarith
  refine hkey.trans_le ?_
  gcongr

/-- There is a residue `y ∈ G_{q_*}` at which the pulled-back reference density satisfies
`Ψ(y) > 13/15`. -/
@[collatz_pos_dens "lem_s05_good_residue"]
theorem exists_lt_pullbackDensity :
    ∃ y : ResidueGroup conductor, (13 / 15 : ℝ) < pullbackDensity y := by
  have h8 : 8 ≤ conductor := le_trans (by norm_num) three_hundred_fifty_two_le_conductor
  have hn : selEnd ≤ generationThreshold := selEnd_le_generationThreshold_range.1
  have hsum := sum_filter_pullbackDensity
  rw [filter_congr fun y _ => val_modEq_iff_residueReduction_eq h8 y] at hsum
  have hmass := lt_sum_filter_selectedTuples _ hn
  have hpow : (3 : ℝ) ^ conductor = 3 ^ (conductor - 8) * 3 ^ 8 := by
    rw [← pow_add, Nat.sub_add_cancel h8]
  obtain ⟨y, -, hy⟩ := exists_lt_of_card_mul_lt_sum_filter h8
    (dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩) (f := pullbackDensity) (c := 13 / 15) (by
      rw [hsum, hpow, mul_assoc]
      refine mul_lt_mul_of_pos_left ?_ (by positivity)
      exact (lt_add_of_pos_right _ (by positivity)).trans
        (add_two_inv_pow_lt_mul_cylinderMass.trans
        (mul_lt_mul_of_pos_left hmass (by norm_num))))
  exact ⟨y, hy⟩

end CollatzPosDens
