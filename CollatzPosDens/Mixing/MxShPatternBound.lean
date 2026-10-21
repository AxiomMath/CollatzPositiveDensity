/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring

/-!
# Patterns of the first positions are nearly fair

Let $N, d, q, b \in \mathbb N$ with $q < N$, $d \le N$ and $b \le \min(q, d)$, and let $M$ be a
real number with $M \ge \max(d, N - d)$. Then
$$\binom{N-q}{d-b} (N-q)^q \le \binom N d M^q.$$
Read probabilistically: among the $d$-subsets of $\{1, \dots, N\}$, the proportion whose trace on
the first $q$ positions is a prescribed pattern with $b$ elements is at most
$(M / (N - q))^q$.

## Main results

* `CollatzPosDens.choose_sub_mul_pow_le_choose_mul_pow`: the inequality above.

## Implementation notes

All differences are truncated subtractions of natural numbers, cast to `ℝ` after subtracting;
the hypotheses make each of them a genuine difference.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Patterns of the first positions are nearly fair: if `q < N`, `d ≤ N`, `b ≤ q`, `b ≤ d` and
`M ≥ max d (N - d)`, then `C(N - q, d - b) * (N - q) ^ q ≤ C(N, d) * M ^ q`. -/
@[collatz_pos_dens "lem_mx_sh_pattern_bound"]
theorem choose_sub_mul_pow_le_choose_mul_pow {N d q b : ℕ} {M : ℝ} (hqN : q < N) (hdN : d ≤ N)
    (hbq : b ≤ q) (hbd : b ≤ d) (hdM : (d : ℝ) ≤ M) (hNdM : ((N - d : ℕ) : ℝ) ≤ M) :
    ((N - q).choose (d - b) : ℝ) * ((N - q : ℕ) : ℝ) ^ q ≤ (N.choose d : ℝ) * M ^ q := by
  induction q generalizing N d b with
  | zero =>
    obtain rfl : b = 0 := by omega
    simp
  | succ q ih =>
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have hM : 0 ≤ M := le_trans (Nat.cast_nonneg _) hdM
    have hsub : N + 1 - (q + 1) = N - q := by omega
    have hcast : ((N - q : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    rw [hsub, pow_succ, pow_succ M, ← mul_assoc, ← mul_assoc]
    rcases b with _ | b
    · rcases Nat.eq_or_lt_of_le hdN with rfl | hdN'
      · rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp only [Nat.cast_zero, zero_mul]
        positivity
      have hdN' : d ≤ N := by omega
      have ih' := ih (N := N) (d := d) (b := 0) (by omega) hdN' (by omega) (by omega) hdM
        (le_trans (by exact_mod_cast (by omega)) hNdM)
      have key : (N.choose d : ℝ) * ((N + 1 : ℕ) : ℝ) =
          ((N + 1).choose d : ℝ) * ((N + 1 - d : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_mul_succ_eq N d
      calc ((N - q).choose (d - 0) : ℝ) * ((N - q : ℕ) : ℝ) ^ q * ((N - q : ℕ) : ℝ)
          ≤ (N.choose d : ℝ) * M ^ q * ((N + 1 : ℕ) : ℝ) := by
            gcongr
        _ = ((N + 1).choose d : ℝ) * ((N + 1 - d : ℕ) : ℝ) * M ^ q := by
            rw [← key]; ring
        _ ≤ ((N + 1).choose d : ℝ) * M * M ^ q := by gcongr
        _ = ((N + 1).choose d : ℝ) * M ^ q * M := by ring
    · obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      have ih' := ih (N := N) (d := d) (b := b) (by omega) (by omega) (by omega) (by omega)
        (le_trans (by exact_mod_cast (by omega)) hdM)
        (le_trans (by exact_mod_cast (by omega)) hNdM)
      have hdb : d + 1 - (b + 1) = d - b := by omega
      have key : ((N + 1 : ℕ) : ℝ) * (N.choose d : ℝ) =
          ((N + 1).choose (d + 1) : ℝ) * ((d + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq N d
      rw [hdb]
      calc ((N - q).choose (d - b) : ℝ) * ((N - q : ℕ) : ℝ) ^ q * ((N - q : ℕ) : ℝ)
          ≤ (N.choose d : ℝ) * M ^ q * ((N + 1 : ℕ) : ℝ) := by gcongr
        _ = ((N + 1).choose (d + 1) : ℝ) * ((d + 1 : ℕ) : ℝ) * M ^ q := by
            rw [← key]; ring
        _ ≤ ((N + 1).choose (d + 1) : ℝ) * M * M ^ q := by gcongr
        _ = ((N + 1).choose (d + 1) : ℝ) * M ^ q * M := by ring

end CollatzPosDens
