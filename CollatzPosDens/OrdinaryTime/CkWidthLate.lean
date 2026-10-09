/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Clog
public import CollatzPosDens.FirstCrossing.Width

/-!
# The width at late levels

For every integer `u ≥ 2^{40}` the width `wd u` is a tiny fraction of the level `u`:
$$20000\,\mathrm{wd}(u) \le u.$$

Write `k = ⌊log₂ u⌋ ≥ 40`, so that `2^k ≤ u` and `lg u ≤ k + 1`. Since `(k+1)/2^k` is
nonincreasing, `(k + 1) 2^{40} ≤ 41 · 2^k`, hence `2^{40} lg u ≤ 41 u`. With `m = ⌊u/20000⌋`
one has `20000 m ≥ u - 19999`, and for `u ≥ 2^{40}` this gives
`32 u lg u ≤ m^2`, i.e. `√(32 u lg u) ≤ m`. Therefore `wd u ≤ ⌈√(32 u lg u)⌉ ≤ m` and
`20000 wd u ≤ 20000 m ≤ u`.

## Main results

* `CollatzPosDens.twenty_thousand_mul_wd_le`: `20000 wd u ≤ u` for `u ≥ 2^{40}`.

## Implementation notes

Rather than bounding `wd(u)/u` by `√(1312/2^{40}) + 2^{-40}` and checking a rational
inequality, the ceiling is absorbed directly by comparing `√(32 u lg u)` with the integer
`⌊u/20000⌋`, which reduces the claim to a polynomial inequality over `ℕ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- `(k + 1) 2^{40} ≤ 41 · 2^k` for `k ≥ 40`. -/
private lemma succ_mul_two_pow_forty_le {k : ℕ} (hk : 40 ≤ k) :
    (k + 1) * 2 ^ 40 ≤ 41 * 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ 2 k]
    nlinarith

/-- `2^{40} lg u ≤ 41 u` for `u ≥ 2^{40}`. -/
private lemma two_pow_forty_mul_lg_le {u : ℕ} (hu : 2 ^ 40 ≤ u) :
    2 ^ 40 * lg u ≤ 41 * u := by
  set k := Nat.log 2 u
  have hk : 40 ≤ k := Nat.le_log_of_pow_le (by norm_num) hu
  have hpow : 2 ^ k ≤ u := Nat.pow_log_le_self 2 (by positivity)
  have hlg : lg u ≤ k + 1 :=
    lg_le_of_le_two_pow (Nat.lt_pow_succ_log_self (by norm_num) u).le
  calc 2 ^ 40 * lg u ≤ (k + 1) * 2 ^ 40 := by
        rw [mul_comm]
        gcongr
    _ ≤ 41 * 2 ^ k := succ_mul_two_pow_forty_le hk
    _ ≤ 41 * u := by gcongr

/-- **Width at late levels.** For every integer `u ≥ 2^{40}`, `20000 wd(u) ≤ u`. -/
@[collatz_pos_dens "lem_ck_width_late"]
theorem twenty_thousand_mul_wd_le {u : ℕ} (hu : 2 ^ 40 ≤ u) : 20000 * wd u ≤ u := by
  set m := u / 20000
  have hm : u < 20000 * m + 20000 := by omega
  have hL := two_pow_forty_mul_lg_le hu
  have hkey : 32 * u * lg u ≤ m ^ 2 := by
    have h1 : 724432 * u ≤ 1048576 * (20000 * m) := by omega
    have h2 : 724432 ^ 2 * u ^ 2 ≤ 2 ^ 40 * (20000 * m) ^ 2 := by
      nlinarith [Nat.mul_le_mul h1 h1]
    have h3 : 2 ^ 40 * (32 * u * lg u) ≤ 2 ^ 40 * m ^ 2 := by
      have h4 : 2 ^ 40 * (32 * u * lg u) ≤ 32 * 41 * u ^ 2 := by nlinarith
      nlinarith
    exact Nat.le_of_mul_le_mul_left h3 (by positivity)
  have hsqrt : √(32 * (u : ℝ) * (lg u : ℝ)) ≤ (m : ℝ) := by
    rw [Real.sqrt_le_left (by positivity)]
    exact_mod_cast hkey
  have hwd : wd u ≤ m := (wd_le_ceil_sqrt u).trans (Nat.ceil_le.2 hsqrt)
  calc 20000 * wd u ≤ 20000 * m := by gcongr
    _ ≤ u := Nat.mul_div_le u 20000

end CollatzPosDens
