/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.BlackSet.BkClaimIii

/-!
# Rightward propagation of small angles

Let `(j, l) ∈ 𝒫`, `m ∈ ℕ` and `ε < 1/19`. If `|ϑ(j, l)| ≤ ε` and `|ϑ(j + k, l - 1)| ≤ ε` for
every `1 ≤ k ≤ m`, then `|ϑ(j + m, l)| ≤ ε`.

By induction on `k = 0, …, m` one shows `|ϑ(j + k, l)| ≤ ε`. For `k ≥ 1` the point `(j + k, l)`
has first coordinate at least `2`, its west neighbour `(j + k - 1, l)` and south neighbour
`(j + k, l - 1)` have angle at most `ε` in absolute value, and `18 ε + ε = 19 ε < 1`;
`CollatzPosDens.two_mul_bkTheta_eq_of_west_of_south` then gives
`|ϑ(j + k, l)| = |ϑ(j + k, l - 1)| / 2 ≤ ε`.

## Main results

* `CollatzPosDens.abs_bkTheta_add_right_le`: rightward propagation.

## Implementation notes

The source assumes `0 ≤ ε < 1/19`; the lower bound is not needed (for `ε < 0` the hypothesis
`|ϑ(j, l)| ≤ ε` is never satisfied), so it is omitted.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Rightward propagation.** Let `(j, l) ∈ 𝒫`, `m ∈ ℕ` and `ε < 1/19`. If `|ϑ(j, l)| ≤ ε` and
`|ϑ(j + k, l - 1)| ≤ ε` for every `1 ≤ k ≤ m`, then `|ϑ(j + m, l)| ≤ ε`. -/
@[collatz_pos_dens "lem_bk_prop_right"]
theorem abs_bkTheta_add_right_le (n : ℕ) (ξ : ResidueGroup n) {j l : ℤ}
    (hp : (j, l) ∈ bkPoints) (m : ℕ) {ε : ℝ} (hε : ε < 1 / 19)
    (h₀ : |bkTheta n ξ (j, l)| ≤ ε)
    (hs : ∀ k : ℕ, 1 ≤ k → k ≤ m → |bkTheta n ξ (j + k, l - 1)| ≤ ε) :
    |bkTheta n ξ (j + m, l)| ≤ ε := by
  have hj : 1 ≤ j := mem_bkPoints_mk.1 hp
  induction m with
  | zero => simpa using h₀
  | succ m ih =>
    have hw := ih fun k hk hkm => hs k hk (by omega)
    have hw' : |bkTheta n ξ ((j + ((m + 1 : ℕ) : ℤ)) - 1, l)| ≤ ε := by
      convert hw using 4; push_cast; ring
    have hS := hs (m + 1) (by omega) le_rfl
    have h2 := two_mul_bkTheta_eq_of_west_of_south n ξ (j := j + ((m + 1 : ℕ) : ℤ)) (l := l)
      (by omega) (by linarith) hw' hS
    have hε0 : 0 ≤ ε := (abs_nonneg _).trans h₀
    have : |bkTheta n ξ (j + ((m + 1 : ℕ) : ℤ), l)| =
        |bkTheta n ξ (j + ((m + 1 : ℕ) : ℤ), l - 1)| / 2 := by
      rw [← h2, abs_mul, abs_two]; ring
    rw [this]
    linarith

end CollatzPosDens
