/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPacketFn

/-!
# The capped packet factor `Φ^cap_c`

For an integer `c` and a real number `θ`, the capped packet factor is
`Φ^cap_c(θ) = max {Φ_{c-1}(θ), 2^{-16}}` when `3 ≤ c ≤ 16`, and `Φ^cap_c(θ) = 1` otherwise,
where `Φ_t` is the packet function `CollatzPosDens.chPacketFn`. It always lies in
`[2^{-16}, 1]`.

## Main definitions

* `CollatzPosDens.trCapFactor`: the capped packet factor `Φ^cap_c(θ)`.

## Main results

* `CollatzPosDens.trCapFactor_of_mem`: the value `max {Φ_{c-1}(θ), 2^{-16}}` for `3 ≤ c ≤ 16`.
* `CollatzPosDens.trCapFactor_of_not_mem`: the value `1` outside `3 ≤ c ≤ 16`.
* `CollatzPosDens.trCapFactor_pos`, `CollatzPosDens.trCapFactor_le_one`: `0 < Φ^cap_c(θ) ≤ 1`.

## Implementation notes

The packet function is indexed by natural numbers, so `Φ_{c-1}` is taken at `(c - 1).toNat`;
on the range `3 ≤ c ≤ 16` where it is used, `(c - 1).toNat = c - 1`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The capped packet factor: `Φ^cap_c(θ) = max {Φ_{c-1}(θ), 2^{-16}}` if `3 ≤ c ≤ 16`, and
`1` otherwise. -/
@[collatz_pos_dens "def_tr_cap_factor"]
noncomputable def trCapFactor (c : ℤ) (θ : ℝ) : ℝ :=
  if 3 ≤ c ∧ c ≤ 16 then max (chPacketFn (c - 1).toNat θ) ((2 : ℝ) ^ (-16 : ℤ)) else 1

/-- For `3 ≤ c ≤ 16`, `Φ^cap_c(θ) = max {Φ_{c-1}(θ), 2^{-16}}`. -/
theorem trCapFactor_of_mem {c : ℤ} (h₁ : 3 ≤ c) (h₂ : c ≤ 16) (θ : ℝ) :
    trCapFactor c θ = max (chPacketFn (c - 1).toNat θ) ((2 : ℝ) ^ (-16 : ℤ)) :=
  ite_eq_left_of_eq_true _ _ (eq_true ⟨h₁, h₂⟩)

/-- Outside the range `3 ≤ c ≤ 16`, `Φ^cap_c(θ) = 1`. -/
theorem trCapFactor_of_not_mem {c : ℤ} (h : ¬(3 ≤ c ∧ c ≤ 16)) (θ : ℝ) :
    trCapFactor c θ = 1 :=
  ite_eq_right_of_eq_false _ _ (eq_false h)

/-- The capped packet factor is at least `2^{-16}`. -/
theorem two_zpow_neg_sixteen_le_trCapFactor (c : ℤ) (θ : ℝ) :
    (2 : ℝ) ^ (-16 : ℤ) ≤ trCapFactor c θ := by
  unfold trCapFactor
  split_ifs
  · exact le_max_right _ _
  · exact zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)

/-- The capped packet factor is positive. -/
theorem trCapFactor_pos (c : ℤ) (θ : ℝ) : 0 < trCapFactor c θ :=
  lt_of_lt_of_le (by positivity) (two_zpow_neg_sixteen_le_trCapFactor c θ)

/-- The capped packet factor is at most `1`. -/
theorem trCapFactor_le_one (c : ℤ) (θ : ℝ) : trCapFactor c θ ≤ 1 := by
  unfold trCapFactor
  split_ifs
  · exact max_le (chPacketFn_le_one _ _) (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num))
  · exact le_rfl

end CollatzPosDens
