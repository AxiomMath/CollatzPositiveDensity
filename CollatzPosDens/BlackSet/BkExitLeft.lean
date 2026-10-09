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
# Leftward recovery along the row above a triangle

Let `(k₀, l) ∈ 𝒫`, `m ≥ 1` and `ε ≤ 1/27`. Suppose `|ϑ(k₀ + m, l)| ≤ 8 ε`,
`|ϑ(k₀, l - 1)| ≤ ε` and `|ϑ(k₀ + k, l - 1)| ≤ 1/27` for `1 ≤ k ≤ m - 1`. Then
`2 ϑ(k₀, l) = ϑ(k₀, l - 1)`.

With `A₀ = max (8 ε) (1/54)` and `B₀ = 1/27` we have `2 A₀ + 9 B₀ < 1`. Walking leftwards from
`k = m - 1` down to `k = 0`, `CollatzPosDens.two_mul_bkTheta_eq_of_east_of_south` at
`(k₀ + k, l)` turns the bound `|ϑ(k₀ + k + 1, l)| ≤ A₀` into `2 ϑ(k₀ + k, l) = ϑ(k₀ + k, l - 1)`,
hence `|ϑ(k₀ + k, l)| ≤ 1/54 ≤ A₀`, which feeds the next step.

## Main results

* `CollatzPosDens.two_mul_bkTheta_eq_of_exit_left`: if `|ϑ(k₀ + m, l)| ≤ 8 ε` and the row below
  is small, then `2 ϑ(k₀, l) = ϑ(k₀, l - 1)`.

## Implementation notes

No hypothesis `0 ≤ ε` is assumed: it follows from `|ϑ(k₀, l - 1)| ≤ ε`. The offset `m` is a
natural number with `1 ≤ m`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.7.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Leftward recovery along the row above a triangle.** If `(k₀, l) ∈ 𝒫`, `1 ≤ m`,
`ε ≤ 1/27`, `|ϑ(k₀ + m, l)| ≤ 8 ε`, `|ϑ(k₀, l - 1)| ≤ ε` and `|ϑ(k₀ + k, l - 1)| ≤ 1/27` for
`1 ≤ k ≤ m - 1`, then `2 ϑ(k₀, l) = ϑ(k₀, l - 1)`. -/
@[collatz_pos_dens "lem_bk_exit_left"]
theorem two_mul_bkTheta_eq_of_exit_left (n : ℕ) (ξ : ResidueGroup n) {k₀ l : ℤ}
    (hp : (k₀, l) ∈ bkPoints) {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : ε ≤ 1 / 27)
    (hE : |bkTheta n ξ (k₀ + m, l)| ≤ 8 * ε) (hS : |bkTheta n ξ (k₀, l - 1)| ≤ ε)
    (hrow : ∀ k : ℕ, 1 ≤ k → k ≤ m - 1 → |bkTheta n ξ (k₀ + k, l - 1)| ≤ 1 / 27) :
    2 * bkTheta n ξ (k₀, l) = bkTheta n ξ (k₀, l - 1) := by
  rw [mem_bkPoints_mk] at hp
  set A₀ : ℝ := max (8 * ε) (1 / 54) with hA₀
  have hAB : 2 * A₀ + 9 * (1 / 27 : ℝ) < 1 := by
    rcases max_cases (8 * ε) (1 / 54 : ℝ) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [hA₀, h] <;> linarith
  have key : ∀ d : ℕ, d ≤ m - 1 → |bkTheta n ξ (k₀ + ((m - d : ℕ) : ℤ), l)| ≤ A₀ := by
    intro d
    induction d with
    | zero => intro _; rw [Nat.sub_zero]; exact hE.trans (le_max_left _ _)
    | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      set k : ℕ := m - (d + 1) with hk
      have hk1 : 1 ≤ k := by omega
      have hpk : (k₀ + (k : ℤ), l) ∈ bkPoints := mem_bkPoints_mk.2 (by omega)
      have heast : k₀ + (k : ℤ) + 1 = k₀ + ((m - d : ℕ) : ℤ) := by
        rw [hk]; push_cast [show d + 1 ≤ m by omega, show d ≤ m by omega]; ring
      have h2 := two_mul_bkTheta_eq_of_east_of_south n ξ hpk hAB (A₀ := A₀)
        (by rw [heast]; exact hprev) (hrow k hk1 (by omega))
      have hs := hrow k hk1 (by omega)
      have : |bkTheta n ξ (k₀ + (k : ℤ), l)| ≤ 1 / 54 := by
        rw [← h2, abs_mul, abs_two] at hs; linarith
      exact this.trans (le_max_right _ _)
  have h1 := key (m - 1) le_rfl
  have hm1 : ((m - (m - 1) : ℕ) : ℤ) = 1 := by omega
  rw [hm1] at h1
  exact two_mul_bkTheta_eq_of_east_of_south n ξ (mem_bkPoints_mk.2 hp) hAB h1 (hS.trans hε)

end CollatzPosDens
