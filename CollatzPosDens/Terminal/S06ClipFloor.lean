/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CollatzPosDens.Attr

/-!
# The clipping degree floor

For `m ∈ ℕ` and a real `B > 0`, the *clipping degree floor* is the integer
$$A^{\mathrm{clp}}_{m,B} = \bigl\lceil \log_2\bigl(8 \cdot 3^m / B\bigr)\bigr\rceil.$$
It is the least integer `A` with `8 · 3^m / B ≤ 2^A`, i.e. with `2^{-A} 3^m ≤ B / 8`.

## Main definitions

* `CollatzPosDens.clipFloor m B`: the clipping degree floor `A^clp_{m,B}`.

## Main results

* `CollatzPosDens.clipFloor_le_iff`: for `B > 0`, `A^clp_{m,B} ≤ A ↔ 8 · 3^m / B ≤ 2^A`.
* `CollatzPosDens.le_two_zpow_clipFloor`: for `B > 0`, `8 · 3^m / B ≤ 2^{A^clp_{m,B}}`.

## Implementation notes

The definition uses `Real.logb 2` and `Int.ceil` and makes sense for every real `B`; the
characterisation lemmas `clipFloor_le_iff` and `le_two_zpow_clipFloor` assume `B > 0`.

## References

* [Mazur, *Collatz positive density*], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The clipping degree floor `A^clp_{m,B} = ⌈log₂(8 · 3^m / B)⌉ ∈ ℤ`. -/
@[collatz_pos_dens "def_s06_clip_floor"]
noncomputable def clipFloor (m : ℕ) (B : ℝ) : ℤ :=
  ⌈Real.logb 2 (8 * 3 ^ m / B)⌉

/-- Unfolding lemma for `clipFloor`. -/
theorem clipFloor_def (m : ℕ) (B : ℝ) : clipFloor m B = ⌈Real.logb 2 (8 * 3 ^ m / B)⌉ :=
  rfl

/-- For `B > 0`, an integer `A` is at least the clipping floor exactly when
`8 · 3^m / B ≤ 2^A`. -/
theorem clipFloor_le_iff {m : ℕ} {B : ℝ} (hB : 0 < B) {A : ℤ} :
    clipFloor m B ≤ A ↔ 8 * 3 ^ m / B ≤ (2 : ℝ) ^ A := by
  rw [clipFloor_def, Int.ceil_le, Real.logb_le_iff_le_rpow one_lt_two (by positivity),
    Real.rpow_intCast]

/-- For `B > 0`, `8 · 3^m / B ≤ 2^{A^clp_{m,B}}`. -/
theorem le_two_zpow_clipFloor (m : ℕ) {B : ℝ} (hB : 0 < B) :
    8 * 3 ^ m / B ≤ (2 : ℝ) ^ clipFloor m B :=
  (clipFloor_le_iff hB).1 le_rfl

/-- For `B > 0` and `A ≥ A^clp_{m,B}`, the weight bound `2^{-A} 3^m ≤ B / 8`. -/
theorem three_pow_div_two_zpow_le {m : ℕ} {B : ℝ} (hB : 0 < B) {A : ℤ}
    (hA : clipFloor m B ≤ A) : (3 : ℝ) ^ m / (2 : ℝ) ^ A ≤ B / 8 := by
  have h := (clipFloor_le_iff hB).1 hA
  have h2 : (0 : ℝ) < 2 ^ A := zpow_pos two_pos A
  rw [div_le_iff₀ hB] at h
  rw [div_le_div_iff₀ h2 (by norm_num)]
  linarith

end CollatzPosDens
