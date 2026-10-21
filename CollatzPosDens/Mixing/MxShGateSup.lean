/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShGate
public import CollatzPosDens.Mixing.MxShHeadMeasure
public import CollatzPosDens.Mixing.MxShMultSup
public import CollatzPosDens.Mixing.MxShShellWidth

/-!
# Supremum bound for a gate

Let `n ≥ 1`, `d, j ∈ ℕ` and `y ∈ G_n`. Then
$$3^n\,\Gamma^{\mathrm{sh}}_{n,d,j}(y) < W_j + 2.$$

Write `H = H^{sh}_n` and `N = H - 1`. The shell is `I^{sh}_j = [α_j, α_j + W_j)`, so the exposed
patterns `Hd^{sh}_n(d, j)` are `d`-element subsets of `{1, …, N}` with offsets in a window of
length `W_j`, and the multiplicity bound for such windows gives
$$3^n\,\Gamma^{\mathrm{sh}}_{n,d,j}(y) \le 3^n 2^{-N}\bigl(2^N W_j 3^{-n} + 1\bigr)
  = W_j + 2 \cdot 3^n 2^{-H}.$$
Finally `3^n ≤ 2^H` by the definition of `H`, and `3^n ≠ 2^H` since `3^n` is odd and `2^H` is even
(`H ≥ 1`), so `3^n 2^{-H} < 1`.

## Main results

* `CollatzPosDens.pow_three_lt_two_pow_shHeight`: `3^n < 2^{H^{sh}_n}` for `n ≥ 1`.
* `CollatzPosDens.pow_three_mul_shHeadMeasure_lt`: the bound `3^n Γ^sh_{n,d,j}(y) < W_j + 2`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §12.11.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For `n ≥ 1`, `3^n < 2^{H^{sh}_n}`: the inequality `3^n ≤ 2^{H^{sh}_n}` is strict by parity. -/
theorem pow_three_lt_two_pow_shHeight {n : ℕ} (hn : 1 ≤ n) : 3 ^ n < 2 ^ shHeight n := by
  refine lt_of_le_of_ne (pow_three_le_two_pow_shHeight n) fun h => ?_
  have hodd : Odd (3 ^ n) := Odd.pow (by decide)
  have heven : Even (2 ^ shHeight n) :=
    (Nat.even_pow).2 ⟨even_two, (Nat.one_le_iff_ne_zero.1 (one_le_shHeight hn))⟩
  rw [h] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) heven

/-- **Supremum bound for a gate.** For `n ≥ 1`, `d, j ∈ ℕ` and `y ∈ G_n`,
`3^n Γ^sh_{n,d,j}(y) < W_j + 2`. -/
@[collatz_pos_dens "lem_mx_sh_gate_sup"]
theorem pow_three_mul_shHeadMeasure_lt {n : ℕ} (hn : 1 ≤ n) (d j : ℕ) (y : ResidueGroup n) :
    3 ^ n * shHeadMeasure n d j y < shShellWidth j + 2 := by
  set H := shHeight n with hHdef
  have hH : 1 ≤ H := one_le_shHeight hn
  obtain ⟨α, -, hshell⟩ := mxShShell_eq_Ico_shShellWidth j
  have hoff : ∀ β ∈ shRetainedHeads n d j, α ≤ (setOffset β : ℝ) ∧
      (setOffset β : ℝ) < α + shShellWidth j := fun β hβ => by
    have h := setOffset_mem_mxShShell_of_mem_shRetainedHeads hβ
    rw [hshell] at h
    exact h
  have hcount := card_filter_dyadicRed_setOffset_le n (H - 1) d
    (fun β hβ => ⟨subset_Icc_of_mem_shRetainedHeads hβ, card_eq_of_mem_shRetainedHeads hβ⟩)
    (by positivity) hoff y
  have hlt : (3 : ℝ) ^ n < 2 ^ H := by exact_mod_cast pow_three_lt_two_pow_shHeight hn
  have hpow : (2 : ℝ) ^ H = 2 * 2 ^ (H - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  set C := (#{β ∈ shRetainedHeads n d j |
    dyadicRed n ⟨setOffset β, setOffset_mem_dyadicRationals β⟩ = y} : ℝ)
  have hΓ : ((3 ^ n * shHeadMeasure n d j y : ℚ) : ℝ) = 3 ^ n * ((2 : ℝ) ^ (H - 1))⁻¹ * C := by
    rw [shHeadMeasure_def]
    push_cast
    ring
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have h2 : (0 : ℝ) < 2 ^ (H - 1) := by positivity
  have key : 3 ^ n * ((2 : ℝ) ^ (H - 1))⁻¹ * C < shShellWidth j + 2 := by
    rw [mul_assoc, ← div_eq_inv_mul, mul_div_assoc', div_lt_iff₀ h2]
    calc 3 ^ n * C ≤ 3 ^ n * (2 ^ (H - 1) * shShellWidth j * 3⁻¹ ^ n + 1) := by gcongr
      _ = 2 ^ (H - 1) * shShellWidth j + 3 ^ n := by
        rw [inv_pow]
        field_simp
      _ < (shShellWidth j + 2) * 2 ^ (H - 1) := by nlinarith
  exact_mod_cast hΓ ▸ key

end CollatzPosDens
