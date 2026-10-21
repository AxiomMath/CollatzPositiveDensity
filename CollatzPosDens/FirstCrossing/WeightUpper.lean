/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.FirstCrossing.S03BarrierPower
public import CollatzPosDens.Maps.Weight

/-!
# An upper bound on the weight of a first-crossing word

Every word `w` of the first-crossing family `𝒲(b, u, K)` has weight
$$\omega(w) < 2^{1 + r_b - u} (3/4)^b.$$
Indeed, if `s = |w|` then `A(w) ≥ H_{b,u}(s)`, so
`ω(w) = 3^s 2^{-A(w)} ≤ 3^s 2^{-H_{b,u}(s)}`, and the lower bound
`2^{H_{b,u}(s)} > ½ 4^b 3^{s-b} 2^{u-r_b}` gives the claim.

## Main results

* `CollatzPosDens.weight_le_of_mem_firstCrossing`: `ω(w) < 2^{1 + r_b - u} (3/4)^b` for
  `w ∈ 𝒲(b, u, K)`.

## Implementation notes

The source assumes integers `b ≥ 1` and `K ≥ 0`; here `b` and `K` are arbitrary natural
numbers, which is a generalization (the bound holds also for `b = 0`). The bound is stated in
`ℚ`, where the weight lives, with an integer power of `2` since `1 + r_b - u ∈ ℤ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A word `w ∈ 𝒲(b, u, K)` has weight `ω(w) < 2^{1 + r_b - u} (3/4)^b`. -/
@[collatz_pos_dens "lem_weight_upper"]
theorem weight_le_of_mem_firstCrossing {b : ℕ} {u : ℤ} {K : ℕ} {w : Word}
    (hw : w ∈ firstCrossing b u K) :
    w.weight < (2 : ℚ) ^ (1 + rb b - u) * (3 / 4) ^ b := by
  have hA := barrier_le_valSum_of_mem_firstCrossing hw
  have hP := (barrier_power_bounds b w.length u).1
  rw [← Rat.cast_lt (K := ℝ)]
  push_cast [Word.weight]
  set s := w.length
  set H := barrier b u s
  have h2A : (2 : ℝ) ^ H ≤ 2 ^ w.valSum := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ one_le_two hA
  have key : (3 : ℝ) ^ s = 3 ^ ((s : ℤ) - b) * 3 ^ b := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ three_ne_zero, sub_add_cancel]
  have key2 : (2 : ℝ) ^ (1 + rb b - u) = 2 / 2 ^ (u - rb b) := by
    rw [eq_div_iff (by positivity), ← zpow_add₀ two_ne_zero]
    norm_num
  calc (3 : ℝ) ^ s / 2 ^ w.valSum ≤ 3 ^ s / 2 ^ H :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h2A
    _ < 3 ^ s / ((1 / 2) * 4 ^ b * 3 ^ ((s : ℤ) - b) * 2 ^ (u - rb b)) :=
        div_lt_div_of_pos_left (by positivity) (by positivity) hP
    _ = 2 ^ (1 + rb b - u) * (3 / 4) ^ b := by
        rw [key, key2, div_pow]
        field_simp

end CollatzPosDens
