/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Mixing.MxOffsetTail

/-!
# Offsets before a crossing

Let `n ∈ ℕ` and `V ≥ 0`, `R > 0` reals. The words `w ∈ ℤ_{≥1}^n` for which some `1 ≤ i ≤ n`
has `A(w_{≤ i-1}) ≤ V < A(w_{≤ i})` and `2^{A(w_{≤ i}) - ⌊V⌋ - 1} off(w_{≤ i-1}) ≥ R` have
geometric mass at most `∑_{r ≥ 0} 2^{-r-1} · 7 / (R 2^{-r} + 2)`.

## Main results

* `CollatzPosDens.geomMass_crossingOffsetTail_le`: the bound.

## Implementation notes

The power `2^{A(w_{≤ i}) - ⌊V⌋ - 1}` has an integer exponent and is a `zpow` in `ℝ`; the
offset is cast from `ℚ`. The right side is a sum in `ℝ≥0∞` of the nonnegative real terms.

The proof sorts the words by the overshoot `r = A(w_{≤ i}) - ⌊V⌋ - 1 ∈ ℕ` at the crossing index
`i`. For fixed `r`, replacing the crossing letter `a = ⌊V⌋ + 1 + r - A(w_{≤ i-1})` by
`⌊V⌋ + 1 + k - A(w_{≤ i-1})` for every `k ∈ ℕ` is an injection of pairs `(w, k)` into the words
crossing at the same `i` with the same prefix `w_{≤ i-1}`, all of which lie in
`{off(w) ≥ R 2^{-r}}` because the offset of a prefix is at most that of the word. Summing the
geometric series in `k` gives the factor `2^{-r-1}`; then `geomMass_offsetTail_le` bounds the
target. [mazur2026]'s hypothesis `n ≥ 1` is not needed (for `n = 0` the set is empty), so the
lemma is stated for every `n`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-! ### Replacing one letter of a word -/

/-- Replace the letter of index `j` (the `(j+1)`-st letter) of `w` by `b`. -/
private def replLetter (j : ℕ) (b : ℕ+) (w : Word) : Word := w.take j ++ b :: w.drop (j + 1)

private theorem length_replLetter {j : ℕ} {w : Word} (hj : j < w.length) (b : ℕ+) :
    (replLetter j b w).length = w.length := by
  simp only [replLetter, List.length_append, List.length_take, List.length_cons,
    List.length_drop]
  omega

private theorem take_replLetter {j : ℕ} {w : Word} (hj : j < w.length) (b : ℕ+) :
    (replLetter j b w).take j = w.take j :=
  List.take_left' (List.length_take_of_le hj.le)

private theorem drop_replLetter {j : ℕ} {w : Word} (hj : j < w.length) (b : ℕ+) :
    (replLetter j b w).drop (j + 1) = w.drop (j + 1) := by
  have hl : (w.take j).length = j := List.length_take_of_le hj.le
  rw [replLetter, List.drop_append, hl, List.drop_eq_nil_of_le (by omega),
    Nat.add_sub_cancel_left]
  simp

private theorem valSum_take_succ_replLetter {j : ℕ} {w : Word} (hj : j < w.length) (b : ℕ+) :
    Word.valSum ((replLetter j b w).take (j + 1)) = Word.valSum (w.take j) + b := by
  rw [replLetter, List.take_append, List.length_take_of_le hj.le, List.take_take,
    Nat.min_eq_right (Nat.le_succ j), Nat.add_sub_cancel_left]
  simp [Word.valSum_append]

private theorem valSum_replLetter (j : ℕ) (w : Word) (b : ℕ+) :
    Word.valSum (replLetter j b w) =
      Word.valSum (w.take j) + b + Word.valSum (w.drop (j + 1)) := by
  simp only [replLetter, Word.valSum_append, Word.valSum_cons]
  ring

private theorem valSum_eq_take_add_drop (w : Word) (j : ℕ) :
    Word.valSum w = Word.valSum (w.take j) + Word.valSum (w.drop j) := by
  rw [← Word.valSum_append, List.take_append_drop]

private theorem replLetter_eq_self {j : ℕ} {w : Word} (hj : j < w.length) {b : ℕ+}
    (hb : Word.valSum (w.take (j + 1)) = Word.valSum (w.take j) + b) :
    replLetter j b w = w := by
  have e : w.take (j + 1) = w.take j ++ [w[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]
    rfl
  rw [e, Word.valSum_append, Word.valSum_singleton] at hb
  have : w[j] = b := PNat.coe_injective (by omega)
  rw [replLetter, ← this, List.getElem_cons_drop, List.take_append_drop]

private theorem replLetter_replLetter {j : ℕ} {w : Word} (hj : j < w.length) (b c : ℕ+) :
    replLetter j c (replLetter j b w) = replLetter j c w := by
  rw [replLetter, take_replLetter hj, drop_replLetter hj]
  rfl

/-- The prefix sums of a word cross a level `h` at most once. -/
private theorem crossing_unique {w : Word} {h i i' : ℕ} (hi : 1 ≤ i) (hi' : 1 ≤ i')
    (h1 : Word.valSum (w.take (i - 1)) < h) (h2 : h ≤ Word.valSum (w.take i))
    (h1' : Word.valSum (w.take (i' - 1)) < h) (h2' : h ≤ Word.valSum (w.take i')) :
    i = i' := by
  have mono : ∀ a b, a ≤ b → Word.valSum (w.take a) ≤ Word.valSum (w.take b) :=
    fun a b hab => Word.valSum_le_of_isPrefix (List.take_prefix_take_left hab)
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · have := mono i (i' - 1) (by omega); omega
  · exact heq
  · have := mono i' (i - 1) (by omega); omega

/-- **Crossing with a fixed overshoot.** The words of length `n` whose prefix sums cross the
level `h` at some index `i`, landing exactly at `h + r`, with `off(w_{≤ i-1}) ≥ y`, have
geometric mass at most `2^{-r-1}` times that of `{w ∈ ℤ_{≥1}^n : off(w) ≥ y}`. -/
private theorem geomMass_crossingAt_le (n h r : ℕ) (y : ℝ) :
    geomMass {w : Word | w.length = n ∧ ∃ i, 1 ≤ i ∧ i ≤ n ∧
        Word.valSum (w.take (i - 1)) < h ∧ Word.valSum (w.take i) = h + r ∧
        y ≤ (off (w.take (i - 1)) : ℝ)} ≤
      2⁻¹ ^ (r + 1) * geomMass {w : Word | w.length = n ∧ y ≤ (off w : ℝ)} := by
  set E := {w : Word | w.length = n ∧ ∃ i, 1 ≤ i ∧ i ≤ n ∧
        Word.valSum (w.take (i - 1)) < h ∧ Word.valSum (w.take i) = h + r ∧
        y ≤ (off (w.take (i - 1)) : ℝ)} with hE
  set T := {w : Word | w.length = n ∧ y ≤ (off w : ℝ)} with hT
  choose iOf hi1 hin hlt heq hy using fun w (hw : w ∈ E) => hw.2
  have hj : ∀ w (hw : w ∈ E), iOf w hw - 1 < w.length := fun w hw => by
    have := hw.1; have := hi1 w hw; have := hin w hw; omega
  have hsucc : ∀ w (hw : w ∈ E), iOf w hw - 1 + 1 = iOf w hw := fun w hw => by
    have := hi1 w hw; omega
  -- the new letter `h - A(w_{≤ i-1}) + k`
  let L : ℕ → ℕ → ℕ+ := fun s k => (h - s + k).toPNat'
  have hL : ∀ s k, s < h → ((L s k : ℕ+) : ℕ) = h - s + k := fun s k hs => by
    simp only [L, Nat.toPNat'_coe]; split_ifs <;> omega
  let ψ : E → ℕ → Word := fun w k =>
    replLetter (iOf w w.2 - 1) (L (Word.valSum ((w : Word).take (iOf w w.2 - 1))) k) w
  have hψT : ∀ w k, ψ w k ∈ T := fun w k => by
    refine ⟨(length_replLetter (hj w w.2) _).trans w.2.1, ?_⟩
    calc y ≤ (off ((w : Word).take (iOf w w.2 - 1)) : ℝ) := hy w w.2
      _ = (off ((ψ w k).take (iOf w w.2 - 1)) : ℝ) := by
          simp only [ψ, take_replLetter (hj w w.2)]
      _ ≤ (off (ψ w k) : ℝ) := by exact_mod_cast off_take_le _ _
  have hψ1 : ∀ w k, Word.valSum ((ψ w k).take (iOf w w.2 - 1)) =
      Word.valSum ((w : Word).take (iOf w w.2 - 1)) := fun w k => by
    simp only [ψ, take_replLetter (hj w w.2)]
  have hψ2 : ∀ w k, Word.valSum ((ψ w k).take (iOf w w.2 - 1 + 1)) = h + k := fun w k => by
    simp only [ψ]
    rw [valSum_take_succ_replLetter (hj w w.2), hL _ _ (hlt w w.2)]
    have := hlt w w.2
    omega
  have hψself : ∀ w : E, (w : Word) =
      replLetter (iOf w w.2 - 1) (L (Word.valSum ((w : Word).take (iOf w w.2 - 1))) r) w :=
    fun w => by
    refine (replLetter_eq_self (hj w w.2) ?_).symm
    rw [hL _ _ (hlt w w.2), hsucc w w.2, heq w w.2]
    have := hlt w w.2
    omega
  let φ : E × ℕ → T := fun p => ⟨ψ p.1 p.2, hψT p.1 p.2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨w, k⟩ ⟨w', k'⟩ hww
    have hz : ψ w k = ψ w' k' := congrArg Subtype.val hww
    have hii : iOf w w.2 - 1 + 1 = iOf w' w'.2 - 1 + 1 := by
      refine crossing_unique (w := ψ w k) (h := h) (by omega) (by omega) ?_ ?_ ?_ ?_
      · simp only [Nat.add_sub_cancel, hψ1]; exact hlt w w.2
      · rw [hψ2]; omega
      · rw [hz]; simp only [Nat.add_sub_cancel, hψ1]; exact hlt w' w'.2
      · rw [hz, hψ2]; omega
    have hii' : iOf w w.2 - 1 = iOf w' w'.2 - 1 := by omega
    have hkk : k = k' := by
      have e1 := hψ2 w k
      have e2 := hψ2 w' k'
      rw [← hz, ← hii] at e2
      omega
    subst hkk
    have hS : Word.valSum ((w : Word).take (iOf w w.2 - 1)) =
        Word.valSum ((w' : Word).take (iOf w' w'.2 - 1)) := by
      rw [← hψ1 w k, ← hψ1 w' k, hz, hii']
    have hww' : (w : Word) = w' := by
      have e1 : (w : Word) = replLetter (iOf w w.2 - 1)
          (L (Word.valSum ((w : Word).take (iOf w w.2 - 1))) r) (ψ w k) := by
        simp only [ψ]
        rw [replLetter_replLetter (hj w w.2)]
        exact hψself w
      have e2 : (w' : Word) = replLetter (iOf w' w'.2 - 1)
          (L (Word.valSum ((w' : Word).take (iOf w' w'.2 - 1))) r) (ψ w' k) := by
        simp only [ψ]
        rw [replLetter_replLetter (hj w' w'.2)]
        exact hψself w'
      rw [e1, e2, hz, hii']
      rw [hii'] at hS
      rw [hS]
    rw [Subtype.ext hww']
  have hweight : ∀ w : E, (w : Word).massWeight =
      2⁻¹ ^ (r + 1) * ∑' k : ℕ, ((φ (w, k) : T) : Word).massWeight := fun w => by
    obtain ⟨c, hc⟩ : ∃ c, c = h + Word.valSum ((w : Word).drop (iOf w w.2 - 1 + 1)) :=
      ⟨_, rfl⟩
    have hw : Word.valSum (w : Word) = c + r := by
      have e : Word.valSum ((w : Word).take (iOf w w.2 - 1 + 1)) = h + r := by
        rw [hsucc w w.2]; exact heq w w.2
      rw [valSum_eq_take_add_drop _ (iOf w w.2 - 1 + 1), e, hc]
      ring
    have hk : ∀ k, Word.valSum (ψ w k) = c + k := fun k => by
      simp only [ψ]
      rw [valSum_replLetter, hL _ _ (hlt w w.2)]
      have := hlt w w.2
      omega
    simp only [Word.massWeight, φ, hk, hw]
    simp_rw [pow_add (2⁻¹ : ℝ≥0∞) c]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    calc (2⁻¹ : ℝ≥0∞) ^ c * 2⁻¹ ^ r = 2⁻¹ ^ c * 2⁻¹ ^ r * (2⁻¹ * 2) := by
          rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
      _ = _ := by ring
  calc geomMass E = ∑' w : E, 2⁻¹ ^ (r + 1) * ∑' k : ℕ, ((φ (w, k) : T) : Word).massWeight := by
        rw [geomMass_def]
        exact tsum_congr hweight
    _ = 2⁻¹ ^ (r + 1) * ∑' p : E × ℕ, ((φ p : T) : Word).massWeight := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        exact (ENNReal.tsum_prod
          (f := fun (w : E) (k : ℕ) => ((φ (w, k) : T) : Word).massWeight)).symm
    _ ≤ 2⁻¹ ^ (r + 1) * ∑' t : T, (t : Word).massWeight := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hφ fun t => (t : Word).massWeight
    _ = 2⁻¹ ^ (r + 1) * geomMass T := by rw [geomMass_def]

/-- **Offsets before a crossing.** For `n ∈ ℕ`, `V ≥ 0` and `R > 0`, the words of length `n`
crossing `V` at some index `i` with `2^{A(w_{≤ i}) - ⌊V⌋ - 1} off(w_{≤ i-1}) ≥ R` have
geometric mass at most `∑_{r ≥ 0} 2^{-r-1} · 7 / (R 2^{-r} + 2)`. -/
@[collatz_pos_dens "lem_mx_crossing_offset_tail"]
theorem geomMass_crossingOffsetTail_le {n : ℕ} {V R : ℝ} (hV : 0 ≤ V) (hR : 0 < R) :
    geomMass {w : Word | w.length = n ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧
        (Word.valSum (w.take (i - 1)) : ℝ) ≤ V ∧ V < (Word.valSum (w.take i) : ℝ) ∧
        R ≤ (2 : ℝ) ^ ((Word.valSum (w.take i) : ℤ) - ⌊V⌋ - 1) *
          (off (w.take (i - 1)) : ℝ)} ≤
      ∑' r : ℕ, ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (r + 1) * (7 / (R * (2 : ℝ)⁻¹ ^ r + 2))) := by
  set h : ℕ := ⌊V⌋₊ + 1 with hh
  set E : ℕ → Set Word := fun r => {w : Word | w.length = n ∧ ∃ i, 1 ≤ i ∧ i ≤ n ∧
      Word.valSum (w.take (i - 1)) < h ∧ Word.valSum (w.take i) = h + r ∧
      R * (2 : ℝ)⁻¹ ^ r ≤ (off (w.take (i - 1)) : ℝ)} with hE
  have hfl : ⌊V⌋ = ((⌊V⌋₊ : ℕ) : ℤ) := (Int.natCast_floor_eq_floor hV).symm
  have hsub : {w : Word | w.length = n ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧
        (Word.valSum (w.take (i - 1)) : ℝ) ≤ V ∧ V < (Word.valSum (w.take i) : ℝ) ∧
        R ≤ (2 : ℝ) ^ ((Word.valSum (w.take i) : ℤ) - ⌊V⌋ - 1) *
          (off (w.take (i - 1)) : ℝ)} ⊆ ⋃ r, E r := by
    rintro w ⟨hlen, i, hi1, hin, h1, h2, h3⟩
    have h1' : Word.valSum (w.take (i - 1)) < h := by
      have := Nat.le_floor h1; omega
    have h2' : h ≤ Word.valSum (w.take i) := (Nat.floor_lt hV).2 h2
    refine Set.mem_iUnion.2 ⟨Word.valSum (w.take i) - h,
      hlen, i, hi1, hin, h1', by omega, ?_⟩
    have hz : (Word.valSum (w.take i) : ℤ) - ⌊V⌋ - 1 =
        ((Word.valSum (w.take i) - h : ℕ) : ℤ) := by
      rw [hfl, Nat.cast_sub h2', hh]; push_cast; ring
    rw [hz, zpow_natCast] at h3
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  calc _ ≤ geomMass (⋃ r, E r) := geomMass_mono hsub
    _ ≤ ∑' r, geomMass (E r) := by
        simp only [geomMass_def]
        exact ENNReal.tsum_iUnion_le_tsum _ _
    _ ≤ ∑' r : ℕ, 2⁻¹ ^ (r + 1) * ENNReal.ofReal (7 / (R * (2 : ℝ)⁻¹ ^ r + 2)) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        refine (geomMass_crossingAt_le n h r _).trans ?_
        gcongr
        exact geomMass_offsetTail_le n (by positivity)
    _ = _ := by
        refine tsum_congr fun r => ?_
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

end CollatzPosDens
