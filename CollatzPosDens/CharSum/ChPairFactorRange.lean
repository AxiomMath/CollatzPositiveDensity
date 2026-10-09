/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPairFactor
public import CollatzPosDens.Characters.FxCharacterAbs

/-!
# The range of the pair factor

Fix `n : ℕ` and a frequency `ξ : ResidueGroup n`. For all `j : ℕ` and `s b : ℤ`, the pair
factor satisfies `0 ≤ chPairFactor n ξ j s b ≤ 1`. If `b ≤ 1` the value is `1`. If `b ≥ 2` it is
`1 / (b - 1)` times the modulus of a sum of `b - 1` complex numbers of modulus `1` (values of a
character); this modulus is nonnegative and, by the triangle inequality, at most `b - 1`.

## Main results

* `CollatzPosDens.chPairFactor_mem_Icc`: `chPairFactor n ξ j s b ∈ [0, 1]`.

## Implementation notes

The bound holds for every `j : ℕ`, including `j = 0`, so no hypothesis `j ≥ 1` is imposed.

## References

* [Mazur, *Collatz positive density*], §7.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The pair factor takes values in `[0, 1]`: `0 ≤ chPairFactor n ξ j s b ≤ 1`. -/
@[collatz_pos_dens "lem_ch_pair_factor_range"]
theorem chPairFactor_mem_Icc (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s b : ℤ) :
    chPairFactor n ξ j s b ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨chPairFactor_nonneg n ξ j s b, chPairFactor_le_one n ξ j s b⟩

end CollatzPosDens
