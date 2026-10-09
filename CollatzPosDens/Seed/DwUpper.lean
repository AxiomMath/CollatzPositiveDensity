/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Clog
public import CollatzPosDens.FirstCrossing.Width
public import CollatzPosDens.Seed.DepthWidth

/-!
# An upper bound for the depth half-width

The depth half-width satisfies `dw(b) ≤ ⌈√(32 b lg b)⌉`. For `b ≥ 256` this is immediate,
since `dw(b) = wd(b)` is a minimum one of whose entries is `⌈√(32 b lg b)⌉`. For `b < 256`
one has `dw(b) = ⌊3b/5⌋`, and `(3b/5)² = (9b/25)·b < 96 b ≤ 32 b lg b` as soon as
`lg b ≥ 3`, i.e. `b ≥ 5`; the remaining levels `b ≤ 4` are checked directly.

## Main results

* `CollatzPosDens.dw_le_ceil_sqrt`: `dw b ≤ ⌈√(32 b lg b)⌉₊` for every `b`.

## Implementation notes

In [mazur2026] the bound is stated for integers `b ≥ 9`. It holds for every natural number
`b`, so the hypothesis is dropped.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every natural number `b`, `dw b ≤ ⌈√(32 b lg b)⌉₊`. -/
@[collatz_pos_dens "lem_s05_dw_upper"]
theorem dw_le_ceil_sqrt (b : ℕ) : dw b ≤ ⌈√(32 * (b : ℝ) * (lg b : ℝ))⌉₊ := by
  rcases lt_or_ge b 256 with hb | hb
  · rw [dw_of_lt hb]
    have key : (3 * b / 5) ^ 2 ≤ 32 * b * lg b := by
      rcases lt_or_ge b 5 with h5 | h5
      · rcases Nat.lt_or_ge b 2 with h2 | h2
        · simp [show 3 * b / 5 = 0 by omega]
        · have hlg : 1 ≤ lg b := by
            by_contra h
            have := lg_le_iff_le_two_pow.1 (show lg b ≤ 0 by omega)
            simp at this
            omega
          calc (3 * b / 5) ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left (by omega) 2
            _ ≤ 32 * b * lg b := by nlinarith
      · have hlg : 3 ≤ lg b := by
          by_contra h
          have := lg_le_iff_le_two_pow.1 (show lg b ≤ 2 by omega)
          omega
        have h1 : (3 * b / 5) * 5 ≤ 3 * b := Nat.div_mul_le_self _ _
        generalize hq : 3 * b / 5 = q at h1
        generalize lg b = L at hlg
        have hqb : q ≤ b := by omega
        have e1 : q * 5 * (q * 5) ≤ 3 * b * (3 * b) := Nat.mul_le_mul h1 h1
        have e2 : b * b ≤ 255 * b := Nat.mul_le_mul_right _ (by omega)
        have e3 : 3 * b ≤ b * L := by nlinarith
        nlinarith
    have hr : ((3 * b / 5 : ℕ) : ℝ) ≤ √(32 * (b : ℝ) * (lg b : ℝ)) :=
      Real.le_sqrt_of_sq_le (by exact_mod_cast key)
    exact_mod_cast hr.trans (Nat.le_ceil _)
  · rw [dw_of_le hb]
    exact wd_le_ceil_sqrt b

end CollatzPosDens
