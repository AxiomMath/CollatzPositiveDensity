/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Admissible

/-!
# Inverse orbits along admissible words are positive and odd

If `R` is a positive odd integer and the word `w = (a₁, …, a_d)` is admissible from `R`, then
every term `R_i`, `0 ≤ i ≤ d`, of the inverse orbit of `R` along `w` is a positive odd integer.

The proof is by induction on `i`: if `R_{i-1}` is a positive odd integer and `R_i` is an integer,
then `3 R_i = 2 ^ {a_i} R_{i-1} - 1` is odd and at least `1`, since `a_i ≥ 1`; hence `R_i` is odd
and positive.

## Main results

* `CollatzPosDens.Admissible.exists_inverseOrbit_eq_pos_odd`: every term of the inverse orbit of
  a positive odd integer along an admissible word is a positive odd integer.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- If `R` is a positive odd integer and `w` is admissible from `R`, then every term `R_i`,
`i ≤ |w|`, of the inverse orbit of `R` along `w` is a positive odd integer. -/
@[collatz_pos_dens "lem_inverse_orbit_odd"]
theorem Admissible.exists_inverseOrbit_eq_pos_odd {R : ℤ} {w : Word}
    (hw : Admissible R w) (hpos : 0 < R) (hodd : Odd R) {i : ℕ} (hi : i ≤ w.length) :
    ∃ m : ℤ, inverseOrbit w R i = m ∧ 0 < m ∧ Odd m := by
  induction i with
  | zero => exact ⟨R, by simp, hpos, hodd⟩
  | succ i ih =>
    obtain ⟨m, hm, hmpos, hmodd⟩ := ih (Nat.le_of_succ_le hi)
    obtain ⟨n, hn⟩ := admissible_iff_exists_int.mp hw (i + 1) hi
    refine ⟨n, hn, ?_⟩
    have hlt : i < w.length := hi
    rw [inverseOrbit_succ w R hlt, hm, invStep] at hn
    set a : ℕ := (w[i] : ℕ) with ha
    have ha1 : 1 ≤ a := w[i].pos
    have h3 : (3 * n : ℤ) = 2 ^ a * m - 1 := by
      have : ((3 * n : ℤ) : ℚ) = ((2 ^ a * m - 1 : ℤ) : ℚ) := by
        push_cast
        rw [← hn]
        ring
      exact_mod_cast this
    have heven : Even ((2 : ℤ) ^ a * m) :=
      (Int.even_pow.mpr ⟨even_two, by omega⟩).mul_right m
    have hodd3 : Odd (3 * n) := by
      rw [h3]
      exact heven.sub_odd odd_one
    refine ⟨?_, (Int.odd_mul.mp hodd3).2⟩
    have h2 : (2 : ℤ) ≤ 2 ^ a * m := by
      have : (2 : ℤ) ≤ 2 ^ a := by
        calc (2 : ℤ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha1
      nlinarith
    omega

end CollatzPosDens
