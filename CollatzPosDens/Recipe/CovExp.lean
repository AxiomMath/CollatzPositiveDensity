/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Tactic.Positivity

/-!
# The coverage exponent `Λ_cov`

This file defines the coverage exponent, the natural number
$$\Lambda_{\mathrm{cov}} := 2^{352} \in \mathbb{N},$$
whose power `2 ^ Λ_cov` is the coverage constant.

## Main definitions

* `CollatzPosDens.covExp`: the coverage exponent `Λ_cov := 2 ^ 352`.

## Main results

* `CollatzPosDens.covExp_def`: `Λ_cov = 2 ^ 352`.
* `CollatzPosDens.covExp_pos`: `0 < Λ_cov`.

## Implementation notes

`covExp` is irreducible, so that elaboration never evaluates the closed power `2 ^ 352`; the
formula `covExp_def` keeps it in symbolic form.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The coverage exponent** `Λ_cov := 2 ^ 352 ∈ ℕ`, the binary logarithm of the coverage
constant. -/
@[collatz_pos_dens "def_cov_exp", irreducible]
def covExp : ℕ := 2 ^ 352

/-- The defining formula `Λ_cov = 2 ^ 352`. -/
theorem covExp_def : covExp = 2 ^ 352 := by
  unfold covExp
  rfl

/-- The coverage exponent is positive. -/
theorem covExp_pos : 0 < covExp := by
  rw [covExp_def]
  positivity

end CollatzPosDens
