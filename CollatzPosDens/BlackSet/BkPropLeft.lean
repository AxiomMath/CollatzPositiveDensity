/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.BlackSet.BkClaimIi

/-!
# Leftward propagation of small angles along a row

Let `(j, l) ∈ 𝒫`, `m ∈ ℕ` and `ε < 1/11`. If `|ϑ(j + m, l)| ≤ ε` and `|ϑ(j + k, l - 1)| ≤ ε`
for every `0 ≤ k < m`, then `|ϑ(j, l)| ≤ ε`. The proof is a downward induction on
`k = m, m - 1, …, 0`: at each step `CollatzPosDens.two_mul_bkTheta_eq_of_east_of_south`, applied at
`(j + k, l)` with `A₀ = B₀ = ε` (so that `2 ε + 9 ε = 11 ε < 1`), gives
`|ϑ(j + k, l)| = |ϑ(j + k, l - 1)| / 2 ≤ ε / 2 ≤ ε`.

## Main results

* `CollatzPosDens.abs_bkTheta_le_of_row_east`: leftward propagation along a row.

## Implementation notes

The source also assumes `0 ≤ ε`; this is not needed, since it follows from either hypothesis
`|ϑ(·)| ≤ ε`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Leftward propagation.** If `(j, l) ∈ 𝒫`, `ε < 1/11`, `|ϑ(j + m, l)| ≤ ε` and
`|ϑ(j + k, l - 1)| ≤ ε` for every `k < m`, then `|ϑ(j, l)| ≤ ε`. -/
@[collatz_pos_dens "lem_bk_prop_left"]
theorem abs_bkTheta_le_of_row_east (n : ℕ) (ξ : ResidueGroup n) {j l : ℤ}
    (hp : (j, l) ∈ bkPoints) (m : ℕ) {ε : ℝ} (hε : ε < 1 / 11)
    (hm : |bkTheta n ξ (j + m, l)| ≤ ε)
    (hbelow : ∀ k : ℕ, k < m → |bkTheta n ξ (j + k, l - 1)| ≤ ε) :
    |bkTheta n ξ (j, l)| ≤ ε := by
  induction m generalizing j with
  | zero => simpa using hm
  | succ m ih =>
    rw [mem_bkPoints_mk] at hp
    have h₁ : |bkTheta n ξ (j + 1, l)| ≤ ε := by
      refine ih (mem_bkPoints_mk.2 (by omega)) ?_ fun k hk => ?_
      · convert hm using 4; push_cast; ring
      · convert hbelow (k + 1) (by omega) using 4; push_cast; ring
    have h₀ : |bkTheta n ξ (j, l - 1)| ≤ ε := by simpa using hbelow 0 (by omega)
    have h2 := two_mul_bkTheta_eq_of_east_of_south n ξ (mem_bkPoints_mk.2 hp)
      (A₀ := ε) (B₀ := ε) (by linarith) h₁ h₀
    have hε0 : 0 ≤ ε := (abs_nonneg _).trans h₀
    have : |2 * bkTheta n ξ (j, l)| ≤ ε := by rw [h2]; exact h₀
    rw [abs_mul, abs_two] at this
    linarith

end CollatzPosDens
