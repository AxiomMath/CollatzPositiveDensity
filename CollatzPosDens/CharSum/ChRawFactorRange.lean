/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChRawFactor

/-!
# The range of the raw factor

Fix `n : ℕ` and a frequency `ξ ∈ G_n`. For every point `p` and every integer `c`, the raw factor
satisfies `0 ≤ φ_c(p) ≤ 1`. If `c ≤ 1` the value is `1`. If `c ≥ 2` it is
`Φ_{c-1}(ϑ(p))`, which is `1 / (c - 1)` times the modulus of a sum of `c - 1` complex numbers of
modulus `1`; this is nonnegative and, by the triangle inequality, at most `1`.

## Main results

* `CollatzPosDens.chRawFactor_mem_Icc`: `φ_c(p) ∈ [0, 1]`.

## Implementation notes

The raw factor is defined for every `p : ℤ × ℤ` and the bound holds for all of them, not only
for `p ∈ 𝒫`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The raw factor takes values in `[0, 1]`: `0 ≤ φ_c(p) ≤ 1`. -/
@[collatz_pos_dens "lem_ch_raw_factor_range"]
theorem chRawFactor_mem_Icc (n : ℕ) (ξ : ResidueGroup n) (c : ℤ) (p : ℤ × ℤ) :
    chRawFactor n ξ c p ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨chRawFactor_nonneg n ξ c p, chRawFactor_le_one n ξ c p⟩

end CollatzPosDens
