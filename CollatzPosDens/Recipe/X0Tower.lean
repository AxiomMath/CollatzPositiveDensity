/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Recipe.X0
public import CollatzPosDens.Recipe.BhtLe
public import CollatzPosDens.Recipe.PhSeedTower

/-!
# The cutoff lies below the endpoint threshold

For every endpoint `s ≥ 1` the cutoff `X_0(s) = 32 (2 ^ B 𝓤 + 1)`, where `B` is the height
exponent and `𝓤 = 𝓜(s)` the seed bound, is strictly smaller than the endpoint threshold
`X_end(s) = 2 ^ (s ^ 3 · 2 ^ 2 ^ 2 ^ 87640)`.

The argument is pure natural-number arithmetic. Since `2 ^ B 𝓤 ≥ 1` and `𝓤 < 2 ^ 𝓤`, we have
`X_0(s) ≤ 64 · 2 ^ B 𝓤 < 2 ^ (6 + B + 𝓤)`. The height bound `B < 2 ^ 16 𝓤 ^ 3` and
`6 + 𝓤 ≤ 7 𝓤 ^ 3` give `6 + B + 𝓤 < 2 ^ 17 𝓤 ^ 3 = s ^ 3 · 2 ^ 17 𝓜(1) ^ 3`, which is at most
`s ^ 3 · 2 ^ 33 𝓜(1) ^ 4 < s ^ 3 · 2 ^ 2 ^ 2 ^ 87640`; monotonicity of `x ↦ 2 ^ x` concludes.

## Main results

* `CollatzPosDens.cutoff_lt_collatzDensityThresholdDep`: `X_0(s) < X_end(s)` for `0 < s`.

## Implementation notes

The tower `2 ^ 2 ^ 2 ^ 87640` is never evaluated: it enters only through the bound
`2 ^ 33 𝓜(1) ^ 4 < 2 ^ 2 ^ 2 ^ 87640`, after which it is treated as an opaque natural number.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Bridge for the cutoff**: for every endpoint `s ≥ 1`, the cutoff is
smaller than the endpoint threshold, `X_0(s) < X_end(s)`. -/
@[collatz_pos_dens "lem_X0_tower"]
theorem cutoff_lt_collatzDensityThresholdDep {s : ℕ} (hs : 0 < s) :
    cutoff s < collatzDensityThresholdDep s := by
  have hB := heightExponent_lt_two_pow_sixteen_mul_seedBound_pow_three hs
  have hT := two_pow_mul_seedBound_one_pow_lt
  have hU := seedBound_eq_mul s
  have hM1 : 1 ≤ seedBound 1 := one_le_seedBound one_pos
  have hUlt : seedBound s < 2 ^ seedBound s := Nat.lt_two_pow_self
  have hU1 : 1 ≤ seedBound s := one_le_seedBound hs
  rw [cutoff_def, collatzDensityThresholdDep]
  generalize 2 ^ 2 ^ 2 ^ 87640 = T at hT ⊢
  generalize heightExponent s = B at hB ⊢
  generalize seedBound s = U at hB hU hUlt hU1 ⊢
  generalize seedBound 1 = M at hT hU hM1
  -- `X_0 < 2 ^ (6 + B + U)`.
  have h1 : 32 * (2 ^ B * U + 1) < 2 ^ (6 + B + U) := by
    have hpos : 1 ≤ 2 ^ B * U := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [pow_add, pow_add]
    calc 32 * (2 ^ B * U + 1) ≤ 64 * (2 ^ B * U) := by omega
      _ < 64 * (2 ^ B * 2 ^ U) := by
        apply Nat.mul_lt_mul_of_pos_left _ (by norm_num)
        exact Nat.mul_lt_mul_of_pos_left hUlt (by positivity)
      _ = 2 ^ 6 * 2 ^ B * 2 ^ U := by ring
  -- `6 + B + U < s ^ 3 * T`.
  have h2 : 6 + B + U < s ^ 3 * T := by
    have hU3 : U ≤ U ^ 3 := by
      calc U = U ^ 1 := (pow_one U).symm
        _ ≤ U ^ 3 := Nat.pow_le_pow_right hU1 (by norm_num)
    have hU31 : 1 ≤ U ^ 3 := Nat.one_le_pow _ _ hU1
    have hs3 : 1 ≤ s ^ 3 := Nat.one_le_pow _ _ hs
    have hM3 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by norm_num)
    calc 6 + B + U < 2 ^ 17 * U ^ 3 := by omega
      _ = s ^ 3 * (2 ^ 17 * M ^ 3) := by rw [hU]; ring
      _ ≤ s ^ 3 * (2 ^ 33 * M ^ 4) := by
        apply Nat.mul_le_mul_left
        calc 2 ^ 17 * M ^ 3 ≤ 2 ^ 33 * M ^ 3 := Nat.mul_le_mul_right _ (by norm_num)
          _ ≤ 2 ^ 33 * M ^ 4 := Nat.mul_le_mul_left _ hM3
      _ < s ^ 3 * T := Nat.mul_lt_mul_of_pos_left hT (by omega)
  exact h1.trans (Nat.pow_lt_pow_right (by norm_num) h2)

end CollatzPosDens
