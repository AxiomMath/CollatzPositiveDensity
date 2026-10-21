/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Decay of the cap term

The overshoot caps `cap j` grow at least like `29 + j/56` up to the additive constant one:
`cap j + 1 ≥ 29 + j/56` for every `j`. Hence the cap term `2^{-(cap j + 1)}` decays geometrically
in `j`, at rate `2^{-1/56}`: for every `j`,
$$2^{-(\mathrm{cap}\,j+1)} \le 2^{-29}\cdot 2^{-j/56},$$
where `2^{-j/56}` is the positive real power. This follows from the lower bound
`CollatzPosDens.add_le_fiftySix_mul_cap_add_one` on the caps and the monotonicity of `x ↦ 2^x`
on `ℝ`.

## Main results

* `CollatzPosDens.two_zpow_neg_cap_succ_le`: `2^{-(cap j + 1)} ≤ 2^{-29} · 2^{-j/56}`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Decay of the cap term.** For every `j`, `2^{-(cap j + 1)} ≤ 2^{-29} · 2^{-j/56}`, the
last factor being the positive real power. -/
@[collatz_pos_dens "lem_fc_cap_rate"]
theorem two_zpow_neg_cap_succ_le (j : ℕ) :
    (2 : ℝ) ^ (-((cap j : ℤ) + 1)) ≤ (2 : ℝ) ^ (-29 : ℤ) * (2 : ℝ) ^ (-((j : ℝ) / 56)) := by
  have hlow : (29 : ℝ) + (j : ℝ) / 56 ≤ (cap j : ℝ) + 1 := by
    have h : ((56 * 29 + j : ℕ) : ℝ) ≤ ((56 * (cap j + 1) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (add_le_fiftySix_mul_cap_add_one j)
    push_cast at h
    linarith
  rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_add two_pos]
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  push_cast
  linarith

end CollatzPosDens
