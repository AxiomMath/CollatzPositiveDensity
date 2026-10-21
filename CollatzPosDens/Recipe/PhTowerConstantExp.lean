/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.PhQstarPower

/-!
# The power `3 ^ q_*` below the double tower `2 ^ 2 ^ E_tow`

The conductor `q_*` and the tower exponent `E_tow` satisfy
$$16 \cdot 3^{q_*} < 2^{2^{E_{\mathrm{tow}}}}.$$
The exact comparison `3 ^ 200 < 2 ^ 317` gives `3 < 2 ^ (317/200)`, hence
`16 · 3 ^ q < 2 ^ (4 + (317/200) q)`, and the finite conductor comparison
`4 + (317/200) q_* < 2 ^ E_tow` (`CollatzPosDens.four_add_mul_conductor_lt_two_pow_towerExp`)
concludes.

## Main results

* `CollatzPosDens.sixteen_mul_three_pow_lt_two_pow_two_pow`: for natural numbers `q`, `E` with
  `4 + (317/200) q < 2 ^ E`, one has `16 · 3 ^ q < 2 ^ 2 ^ E`.
* `CollatzPosDens.sixteen_mul_three_pow_conductor_lt_two_pow_two_pow_towerExp`:
  `16 · 3 ^ q_* < 2 ^ 2 ^ E_tow`.

## Implementation notes

The real power `2 ^ (317/200)` is avoided by raising both sides to the `200`-th power:
`(16 · 3 ^ q) ^ 200 = 2 ^ 800 · (3 ^ 200) ^ q ≤ 2 ^ (800 + 317 q) < (2 ^ 2 ^ E) ^ 200`.
The argument is carried out for variable `q` and `E`, so neither `3 ^ q_*` nor the double
tower is ever evaluated. The comparison holds for every natural `q`, so no lower bound on `q_*`
is needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- If `4 + (317/200) q < 2 ^ E` then `16 · 3 ^ q < 2 ^ 2 ^ E`. -/
theorem sixteen_mul_three_pow_lt_two_pow_two_pow {q E : ℕ}
    (h : (4 : ℝ) + 317 / 200 * q < 2 ^ E) : 16 * 3 ^ q < 2 ^ 2 ^ E := by
  have h' : 800 + 317 * q < 200 * 2 ^ E := by
    have : (800 : ℝ) + 317 * q < 200 * 2 ^ E := by linarith
    exact_mod_cast this
  have hle : (16 * 3 ^ q) ^ 200 ≤ 2 ^ (800 + 317 * q) := by
    rw [mul_pow, ← pow_mul, mul_comm q 200, pow_mul, pow_add, pow_mul 2 317]
    refine Nat.mul_le_mul (by rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]) ?_
    exact Nat.pow_le_pow_left (by decide +kernel) q
  have hlt : 2 ^ (800 + 317 * q) < (2 ^ 2 ^ E) ^ 200 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by rw [mul_comm (2 ^ E)]; exact h')
  exact lt_of_pow_lt_pow_left₀ 200 (Nat.zero_le _) (hle.trans_lt hlt)

/-- `16 · 3 ^ conductor < 2 ^ 2 ^ towerExp`. -/
@[collatz_pos_dens "lem_ph_tower_constant_exp"]
theorem sixteen_mul_three_pow_conductor_lt_two_pow_two_pow_towerExp :
    16 * 3 ^ conductor < 2 ^ 2 ^ towerExp :=
  sixteen_mul_three_pow_lt_two_pow_two_pow four_add_mul_conductor_lt_two_pow_towerExp

end CollatzPosDens
