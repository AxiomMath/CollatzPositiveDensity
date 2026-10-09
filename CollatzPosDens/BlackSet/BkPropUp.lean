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
# Small angles propagate upwards along a column with small angles

Let `(j, l) ∈ 𝒫`, `m ∈ ℕ` and `ε < 1/11`. If `|ϑ(j, l)| ≤ ε` and `|ϑ(j + 1, l + k)| ≤ ε` for
every `1 ≤ k ≤ m`, then `|ϑ(j, l + m)| ≤ ε`.

The proof is an induction on `m`. At each step,
`CollatzPosDens.two_mul_bkTheta_eq_of_east_of_south` is applied at `(j, l + k)`, with east
neighbour `(j + 1, l + k)`, south neighbour `(j, l + k - 1)` and `A₀ = B₀ = ε` (admissible since
`2 ε + 9 ε = 11 ε < 1`); it gives `2 ϑ(j, l + k) = ϑ(j, l + k - 1)`, so
`|ϑ(j, l + k)| = |ϑ(j, l + k - 1)| / 2 ≤ ε`.

## Main results

* `CollatzPosDens.abs_bkTheta_add_le_of_east`: the upward propagation.

## Implementation notes

The hypothesis `0 ≤ ε` of the paper's statement is omitted, since it follows from
`|ϑ(j, l)| ≤ ε`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Upward propagation.** Let `(j, l) ∈ 𝒫`, `m ∈ ℕ` and `ε < 1/11`. If `|ϑ(j, l)| ≤ ε` and
`|ϑ(j + 1, l + k)| ≤ ε` for every `1 ≤ k ≤ m`, then `|ϑ(j, l + m)| ≤ ε`. -/
@[collatz_pos_dens "lem_bk_prop_up"]
theorem abs_bkTheta_add_le_of_east (n : ℕ) (ξ : ResidueGroup n) {j l : ℤ} (m : ℕ)
    (hp : (j, l) ∈ bkPoints) {ε : ℝ} (hε : ε < 1 / 11) (h₀ : |bkTheta n ξ (j, l)| ≤ ε)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ m → |bkTheta n ξ (j + 1, l + k)| ≤ ε) :
    |bkTheta n ξ (j, l + m)| ≤ ε := by
  induction m with
  | zero => simpa using h₀
  | succ m ih =>
    have hm : |bkTheta n ξ (j, l + m)| ≤ ε :=
      ih fun k hk₁ hk₂ => h k hk₁ (Nat.le_succ_of_le hk₂)
    have he := h (m + 1) (Nat.le_add_left 1 m) le_rfl
    have hp' : (j, l + ((m + 1 : ℕ) : ℤ)) ∈ bkPoints := mem_bkPoints_mk.2 (mem_bkPoints_mk.1 hp)
    have hs : l + ((m + 1 : ℕ) : ℤ) - 1 = l + m := by push_cast; ring
    have key := two_mul_bkTheta_eq_of_east_of_south n ξ hp' (A₀ := ε) (B₀ := ε)
      (by linarith) he (by rw [hs]; exact hm)
    rw [hs] at key
    have hε0 : 0 ≤ ε := (abs_nonneg _).trans h₀
    have h2 := congrArg abs key
    rw [abs_mul, abs_two] at h2
    linarith

end CollatzPosDens
