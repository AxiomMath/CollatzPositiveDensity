/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset

/-!
# Bounds on the offset of a word

For a nonempty word `w = (a₁, …, a_d)` the offset satisfies `0 < off(w) < (3/2)^d`.
Since every `aᵢ ≥ 1`, each term `3^{j-1} 2^{-(a₁ + ⋯ + a_j)}` of the offset is at most
`3^{j-1} 2^{-j}`, and summing gives `off(w) ≤ (3/2)^d - 1`.

## Main results

* `CollatzPosDens.off_pos`: `0 < off(w)` for every nonempty word `w`.
* `CollatzPosDens.off_le_three_halves_pow_sub_one`: `off(w) ≤ (3/2)^{|w|} - 1`.
* `CollatzPosDens.off_lt_three_halves_pow`: `off(w) < (3/2)^{|w|}`.

## Implementation notes

The upper bound is proved by induction on the Horner recursion
`off(a w) = 2^{-a} (1 + 3 off(w))` rather than termwise on the sum, and it holds for every word,
including the empty one; only positivity needs `|w| ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The offset of a nonempty word is positive. -/
@[collatz_pos_dens "lem_offset_bound"]
theorem off_pos {w : Word} (hw : 1 ≤ w.length) : 0 < off w := by
  cases w with
  | nil => simp at hw
  | cons a w =>
    rw [off_cons]
    have := off_nonneg w
    positivity

/-- The offset of a word of length `d` is at most `(3/2)^d - 1`. -/
theorem off_le_three_halves_pow_sub_one (w : Word) :
    off w ≤ (3 / 2 : ℚ) ^ w.length - 1 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [off_cons, List.length_cons, pow_succ]
    have := off_nonneg w
    have hinv : ((2 : ℚ) ^ (a : ℕ))⁻¹ ≤ 2⁻¹ :=
      inv_anti₀ (by norm_num) (le_self_pow₀ (by norm_num) a.pos.ne')
    calc ((2 : ℚ) ^ (a : ℕ))⁻¹ * (1 + 3 * off w)
        ≤ 2⁻¹ *(1 + 3 * ((3 / 2 : ℚ) ^ w.length - 1)) := by gcongr
      _ = (3 / 2 : ℚ) ^ w.length * (3 / 2) - 1 := by ring

/-- The offset of a word of length `d` is less than `(3/2)^d`. -/
@[collatz_pos_dens "lem_offset_bound"]
theorem off_lt_three_halves_pow (w : Word) : off w < (3 / 2 : ℚ) ^ w.length :=
  (off_le_three_halves_pow_sub_one w).trans_lt (sub_one_lt _)

end CollatzPosDens
