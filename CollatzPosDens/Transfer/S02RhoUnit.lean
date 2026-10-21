/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Theta

/-!
# The entry weights lie in the half-open unit interval

The entry weights `thetaEn i = (1 - dEntry) ^ i = (77 / 100) ^ i` are powers of a ratio in
`(0, 1]`, so `0 < thetaEn i ≤ 1` for every `i : ℕ`.

## Main results

* `CollatzPosDens.thetaEn_pos_and_le_one`: `0 < thetaEn i` and `thetaEn i ≤ 1` for every `i`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.10.
-/

@[expose] public section

namespace CollatzPosDens

/-- Every entry weight lies in the half-open unit interval: `0 < thetaEn i ≤ 1`. -/
@[collatz_pos_dens "lem_s02_rho_unit"]
theorem thetaEn_pos_and_le_one (i : ℕ) : 0 < thetaEn i ∧ thetaEn i ≤ 1 :=
  thetaEn_eq i ▸ ⟨pow_pos (by norm_num) i, pow_le_one₀ (by norm_num) (by norm_num)⟩

end CollatzPosDens
