/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CeilLog3
public import CollatzPosDens.FirstCrossing.Barrier

/-!
# Monotonicity of the barrier `H_{b,u}`

For all `b`, `u`, the barrier `s ↦ H_{b,u}(s)` is nondecreasing: in particular
`H_{b,u}(s) ≤ H_{b,u}(s + 1)` for every `s ≥ 0`. Indeed `B(j) = ⌈j log₂ 3⌉` is nondecreasing,
`s ↦ (s - b)₊` is nondecreasing and `s ↦ (b - s)₊` is nonincreasing, so
`B((s - b)₊) - B((b - s)₊)` is nondecreasing in `s`, and so is its sum with the constant
`2b + u - r_b`.

## Main results

* `CollatzPosDens.monotone_barrier`: `s ↦ H_{b,u}(s)` is monotone.
* `CollatzPosDens.barrier_le_barrier_succ`: `H_{b,u}(s) ≤ H_{b,u}(s + 1)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The rounded logarithm `B(j) = ⌈j log₂ 3⌉` is monotone in `j`. -/
private theorem monotone_ceilLog3 : Monotone ceilLog3 := fun _ _ hij =>
  Nat.ceil_mono <| mul_le_mul_of_nonneg_right (by exact_mod_cast hij)
    (Real.logb_nonneg one_lt_two (by norm_num))

/-- For fixed `b` and `u`, the barrier `s ↦ H_{b,u}(s)` is monotone. -/
theorem monotone_barrier (b : ℕ) (u : ℤ) : Monotone (barrier b u) := fun s t hst => by
  have h1 : (ceilLog3 (s - b) : ℤ) ≤ ceilLog3 (t - b) := by
    exact_mod_cast monotone_ceilLog3 (Nat.sub_le_sub_right hst b)
  have h2 : (ceilLog3 (b - t) : ℤ) ≤ ceilLog3 (b - s) := by
    exact_mod_cast monotone_ceilLog3 (Nat.sub_le_sub_left hst b)
  rw [barrier_def, barrier_def]
  linarith

/-- The barrier is nondecreasing in its step argument: `H_{b,u}(s) ≤ H_{b,u}(s + 1)`. -/
@[collatz_pos_dens "lem_s03_barrier_mono"]
theorem barrier_le_barrier_succ (b : ℕ) (u : ℤ) (s : ℕ) : barrier b u s ≤ barrier b u (s + 1) :=
  monotone_barrier b u s.le_succ

end CollatzPosDens
