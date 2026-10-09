/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Barrier
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The minimal early overshoot `μ_b(d)`

For natural numbers `b` and `d`, the minimal early overshoot `μ_b(d)` is the
least `k ∈ ℕ` with
$$16 \cdot 3^d \cdot 2^{3b} < (2^{3b} - 1)\, 2^{H_{b,r_b}(d) + k},$$
where `H_{b,u}(s)` is the barrier `barrier` and `r_b` the shift radius `rb`. The exponent
`H_{b,r_b}(d) + k` is an integer which may be negative, so the inequality is read in `ℝ` with an
integer power. For `b ≥ 1` the factor `2^{3b} - 1` is at least `1` and the right-hand side is
unbounded and strictly increasing in `k`, so the least such `k` exists, and the inequality holds
exactly for the `k ≥ μ_b(d)`.

## Main definitions

* `CollatzPosDens.fcMinOvershoot`: the minimal early overshoot `μ_b(d)`.

## Main results

* `CollatzPosDens.fcMinOvershoot_exists`: for `b ≥ 1` some `k` satisfies the inequality.
* `CollatzPosDens.fcMinOvershoot_spec`: for `b ≥ 1`, `k = μ_b(d)` satisfies it.
* `CollatzPosDens.fcMinOvershoot_le`: every `k` satisfying it is at least `μ_b(d)`.
* `CollatzPosDens.fcMinOvershoot_le_iff`: for `b ≥ 1`, `μ_b(d) ≤ k` iff `k` satisfies it.

## Implementation notes

The source considers only `b ∈ {9, 10, 11}`. The definition is stated for every natural `b` as
an infimum `sInf` over `ℕ`, and the lemmas that need the least element to exist assume only
`1 ≤ b` (for `b = 0` the factor `2^{3b} - 1` vanishes and no `k` works, so `sInf` returns `0`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §15.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The **minimal early overshoot** `μ_b(d)`: the least `k ∈ ℕ` with
`16 · 3^d · 2^{3b} < (2^{3b} - 1) · 2^{H_{b,r_b}(d) + k}` (in `ℝ`, integer exponent), where
`H_{b,r_b}(d) = barrier b (rb b) d`. For `b = 0` no such `k` exists and the value is `0`. -/
@[collatz_pos_dens "def_fc_min_overshoot"]
noncomputable def fcMinOvershoot (b d : ℕ) : ℕ :=
  sInf {k : ℕ | (16 * 3 ^ d * 2 ^ (3 * b) : ℝ) <
    (2 ^ (3 * b) - 1) * (2 : ℝ) ^ (barrier b (rb b) d + k)}

/-- Unfolding lemma for `fcMinOvershoot`. -/
theorem fcMinOvershoot_def (b d : ℕ) :
    fcMinOvershoot b d = sInf {k : ℕ | (16 * 3 ^ d * 2 ^ (3 * b) : ℝ) <
      (2 ^ (3 * b) - 1) * (2 : ℝ) ^ (barrier b (rb b) d + k)} := rfl

/-- For `b ≥ 1` the factor `2^{3b} - 1` is at least `1`. -/
theorem fcMinOvershoot_one_le_factor {b : ℕ} (hb : 1 ≤ b) : (1 : ℝ) ≤ 2 ^ (3 * b) - 1 := by
  have : (2 : ℝ) ≤ 2 ^ (3 * b) := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (3 * b) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

/-- For `b ≥ 1` some `k` satisfies the defining inequality of `μ_b(d)`. -/
theorem fcMinOvershoot_exists {b : ℕ} (hb : 1 ≤ b) (d : ℕ) :
    ∃ k : ℕ, (16 * 3 ^ d * 2 ^ (3 * b) : ℝ) <
      (2 ^ (3 * b) - 1) * (2 : ℝ) ^ (barrier b (rb b) d + k) := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (16 * 3 ^ d * 2 ^ (3 * b) : ℝ) one_lt_two
  set H := barrier b (rb b) d
  refine ⟨N + (-H).toNat, ?_⟩
  have hexp : (N : ℤ) ≤ H + ((N + (-H).toNat : ℕ) : ℤ) := by
    push_cast; omega
  have h1 : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ (H + ((N + (-H).toNat : ℕ) : ℤ)) := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ (by norm_num) hexp
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (H + ((N + (-H).toNat : ℕ) : ℤ)) :=
    zpow_pos (by norm_num) _
  have hf := fcMinOvershoot_one_le_factor hb
  nlinarith

/-- For `b ≥ 1`, `k = μ_b(d)` satisfies the defining inequality. -/
theorem fcMinOvershoot_spec {b : ℕ} (hb : 1 ≤ b) (d : ℕ) :
    (16 * 3 ^ d * 2 ^ (3 * b) : ℝ) <
      (2 ^ (3 * b) - 1) * (2 : ℝ) ^ (barrier b (rb b) d + fcMinOvershoot b d) :=
  Nat.sInf_mem (fcMinOvershoot_exists hb d)

/-- Every `k` satisfying the defining inequality is at least `μ_b(d)`. -/
theorem fcMinOvershoot_le {b d k : ℕ}
    (h : (16 * 3 ^ d * 2 ^ (3 * b) : ℝ) <
      (2 ^ (3 * b) - 1) * (2 : ℝ) ^ (barrier b (rb b) d + k)) :
    fcMinOvershoot b d ≤ k :=
  Nat.sInf_le h

/-- Below `μ_b(d)` the defining inequality fails. -/
theorem fcMinOvershoot_not_lt {b d k : ℕ} (hk : k < fcMinOvershoot b d) :
    ¬ (16 * 3 ^ d * 2 ^ (3 * b) : ℝ) <
      (2 ^ (3 * b) - 1) * (2 : ℝ) ^ (barrier b (rb b) d + k) :=
  fun h => (fcMinOvershoot_le h).not_gt hk

/-- For `b ≥ 1`, `μ_b(d) ≤ k` exactly when `k` satisfies the defining inequality. -/
theorem fcMinOvershoot_le_iff {b : ℕ} (hb : 1 ≤ b) (d k : ℕ) :
    fcMinOvershoot b d ≤ k ↔ (16 * 3 ^ d * 2 ^ (3 * b) : ℝ) <
      (2 ^ (3 * b) - 1) * (2 : ℝ) ^ (barrier b (rb b) d + k) := by
  refine ⟨fun hle => ?_, fcMinOvershoot_le⟩
  refine (fcMinOvershoot_spec hb d).trans_le ?_
  have hf := fcMinOvershoot_one_le_factor hb
  gcongr
  · norm_num

end CollatzPosDens
