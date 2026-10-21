/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCapFactor

/-!
# The retained factor `ψ^cut_{r,h,c}`

For a cutoff function `cut : ℕ → ℕ`, natural numbers `r, h`, an integer `c` and a real number
`X`, the retained factor is
`ψ^cut_{r,h,c}(X) = Φ^cap_c(9^r X / 2^{h+c})` when `2 ≤ c ≤ cut(h)`, and `1` otherwise,
where `Φ^cap_c` is the capped packet factor `CollatzPosDens.trCapFactor`. Like the capped
packet factor, it always lies in `[2^{-16}, 1]`.

## Main definitions

* `CollatzPosDens.trTreeFactor`: the retained factor `ψ^cut_{r,h,c}(X)`.

## Main results

* `CollatzPosDens.trTreeFactor_of_mem`: the value `Φ^cap_c(9^r X / 2^{h+c})` for
  `2 ≤ c ≤ cut(h)`.
* `CollatzPosDens.trTreeFactor_of_not_mem`: the value `1` outside `2 ≤ c ≤ cut(h)`.
* `CollatzPosDens.trTreeFactor_pos`, `CollatzPosDens.trTreeFactor_le_one`:
  `0 < ψ^cut_{r,h,c}(X) ≤ 1`.

## Implementation notes

The exponent `h + c` may be negative as an integer expression, so `2^{h+c}` is the integer
power `(2 : ℝ) ^ ((h : ℤ) + c)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The retained factor: `ψ^cut_{r,h,c}(X) = Φ^cap_c(9^r X / 2^{h+c})` if `2 ≤ c ≤ cut(h)`,
and `1` otherwise. -/
@[collatz_pos_dens "def_tr_tree_factor"]
noncomputable def trTreeFactor (cut : ℕ → ℕ) (r h : ℕ) (c : ℤ) (X : ℝ) : ℝ :=
  if 2 ≤ c ∧ c ≤ (cut h : ℤ) then
    trCapFactor c (9 ^ r * X / (2 : ℝ) ^ ((h : ℤ) + c))
  else 1

/-- For `2 ≤ c ≤ cut(h)`, `ψ^cut_{r,h,c}(X) = Φ^cap_c(9^r X / 2^{h+c})`. -/
theorem trTreeFactor_of_mem {cut : ℕ → ℕ} {r h : ℕ} {c : ℤ} (h₁ : 2 ≤ c)
    (h₂ : c ≤ (cut h : ℤ)) (X : ℝ) :
    trTreeFactor cut r h c X = trCapFactor c (9 ^ r * X / (2 : ℝ) ^ ((h : ℤ) + c)) :=
  ite_eq_left_of_eq_true _ _ (eq_true ⟨h₁, h₂⟩)

/-- Outside `2 ≤ c ≤ cut(h)`, `ψ^cut_{r,h,c}(X) = 1`. -/
theorem trTreeFactor_of_not_mem {cut : ℕ → ℕ} {r h : ℕ} {c : ℤ}
    (hc : ¬(2 ≤ c ∧ c ≤ (cut h : ℤ))) (X : ℝ) : trTreeFactor cut r h c X = 1 :=
  ite_eq_right_of_eq_false _ _ (eq_false hc)

/-- The retained factor is at least `2^{-16}`. -/
theorem two_zpow_neg_sixteen_le_trTreeFactor (cut : ℕ → ℕ) (r h : ℕ) (c : ℤ) (X : ℝ) :
    (2 : ℝ) ^ (-16 : ℤ) ≤ trTreeFactor cut r h c X := by
  unfold trTreeFactor
  split_ifs
  · exact two_zpow_neg_sixteen_le_trCapFactor _ _
  · exact zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)

/-- The retained factor is positive. -/
theorem trTreeFactor_pos (cut : ℕ → ℕ) (r h : ℕ) (c : ℤ) (X : ℝ) :
    0 < trTreeFactor cut r h c X :=
  lt_of_lt_of_le (by positivity) (two_zpow_neg_sixteen_le_trTreeFactor cut r h c X)

/-- The retained factor is at most `1`. -/
theorem trTreeFactor_le_one (cut : ℕ → ℕ) (r h : ℕ) (c : ℤ) (X : ℝ) :
    trTreeFactor cut r h c X ≤ 1 := by
  unfold trTreeFactor
  split_ifs
  · exact trCapFactor_le_one _ _
  · exact le_rfl

end CollatzPosDens
