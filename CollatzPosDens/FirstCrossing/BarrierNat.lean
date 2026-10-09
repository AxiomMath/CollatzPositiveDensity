/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

/-!
# Computable forms of `B(j)` and of the centred barrier

The rounded logarithm `B(j) = ⌈j log₂ 3⌉` (`CollatzPosDens.ceilLog3`) and the barrier
`H_{b,u}(s)` (`CollatzPosDens.barrier`) are defined through a real logarithm, so the kernel
cannot evaluate them. The kernel-checked certificates (`decide +kernel`) use instead the
computable forms below, defined with the binary logarithm `Nat.log2`:

* `CollatzPosDens.ceilLog3Nat j = if j = 0 then 0 else log₂(3^j) + 1`;
* `CollatzPosDens.barrierRb b s = 2b + B((s-b)₊) - B((b-s)₊)`, the centred barrier `H_{b,r_b}(s)`.

## Main definitions

* `CollatzPosDens.ceilLog3Nat`: the computable form of `B(j)`.
* `CollatzPosDens.barrierRb`: the computable form of `H_{b,r_b}(s)`.

## Implementation notes

This file imports nothing, so that the certificate modules which evaluate these functions stay
light. The bridges `CollatzPosDens.ceilLog3_eq_ceilLog3Nat` and
`CollatzPosDens.barrier_rb_eq_barrierRb` are proved next to `ceilLog3` and `barrier`.
-/

@[expose] public section

namespace CollatzPosDens

/-- Computable form of `B(j) = ⌈j log₂ 3⌉` (see `ceilLog3_eq_ceilLog3Nat`). -/
def ceilLog3Nat (j : Nat) : Nat := if j = 0 then 0 else Nat.log2 (3 ^ j) + 1

/-- Computable form of the centred barrier `H_{b,r_b}(s) = 2b + B((s-b)₊) - B((b-s)₊)`
(see `barrier_rb_eq_barrierRb`). -/
def barrierRb (b s : Nat) : Int := 2 * (b : Int) + ceilLog3Nat (s - b) - ceilLog3Nat (b - s)

end CollatzPosDens
