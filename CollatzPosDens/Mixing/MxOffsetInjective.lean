/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Maps.WordDetermined

/-!
# Injectivity of the offset on words of a fixed length

For a nonempty word `w`, the rational number `2^{A(w)} off(w)` is an odd integer, so the
`2`-adic valuation of `off(w)` is `-A(w)`. Consequently two words `u, u'` of the same length
with `off(u) = off(u')` have the same valuation sum; subtracting the common last term
`3^{d-1} 2^{-A(u)}` and inducting on the length shows `u = u'`.

## Main results

* `CollatzPosDens.exists_odd_off_mul_two_pow_valSum`: for `w ≠ ∅`, `off(w) 2^{A(w)}` is an odd
  natural number.
* `CollatzPosDens.off_injective_of_length_eq`: words of equal length with equal offsets are
  equal.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For a nonempty word `w`, `off(w) 2^{A(w)}` is an odd natural number. -/
theorem exists_odd_off_mul_two_pow_valSum {w : Word} (hw : w ≠ []) :
    ∃ N : ℕ, Odd N ∧ off w * 2 ^ Word.valSum w = N := by
  induction w with
  | nil => exact absurd rfl hw
  | cons a w ih =>
    rcases eq_or_ne w [] with rfl | hw'
    · refine ⟨1, odd_one, ?_⟩
      simp [Word.valSum_cons]
    · obtain ⟨N, hN, hoff⟩ := ih hw'
      have hA : 1 ≤ Word.valSum w := by
        have := Word.length_le_valSum w
        have := List.length_pos_of_ne_nil hw'
        omega
      refine ⟨2 ^ Word.valSum w + 3 * N, ?_, ?_⟩
      · exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_odd
          (by simpa using (by decide : Odd 3).mul hN)
      · rw [off_cons, Word.valSum_cons, pow_add]
        push_cast
        rw [← hoff]
        field_simp

/-- Two odd numerators over powers of two describe the same rational only for equal powers. -/
private theorem pow_eq_of_odd_div_two_pow {N N' A A' : ℕ} (hN : Odd N) (hN' : Odd N')
    (h : (N : ℚ) / 2 ^ A = N' / 2 ^ A') : A = A' := by
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have key : (2 : ℤ) ^ A' * N = 2 ^ A * N' := by
    have : (((2 : ℤ) ^ A' * N : ℤ) : ℚ) = ((2 ^ A * N' : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  exact (eq_and_eq_of_two_pow_mul_eq hN.natCast hN'.natCast key).1.symm

/-- **Injectivity of the offset on words of a fixed length.** If `u, u'` are words of the same
length with `off(u) = off(u')`, then `u = u'`. -/
@[collatz_pos_dens "lem_mx_offset_injective"]
theorem off_injective_of_length_eq {u u' : Word} (hlen : u.length = u'.length)
    (hoff : off u = off u') : u = u' := by
  induction u using List.reverseRecOn generalizing u' with
  | nil => exact (List.length_eq_zero_iff.1 hlen.symm).symm
  | append_singleton u a ih =>
    rcases List.eq_nil_or_concat' u' with rfl | ⟨u', a', rfl⟩
    · simp at hlen
    · simp only [List.length_append, List.length_singleton, add_left_inj] at hlen
      -- the valuation sums agree
      obtain ⟨N, hN, hN₁⟩ := exists_odd_off_mul_two_pow_valSum (w := u ++ [a]) (by simp)
      obtain ⟨N', hN', hN₁'⟩ := exists_odd_off_mul_two_pow_valSum (w := u' ++ [a']) (by simp)
      have hA : Word.valSum (u ++ [a]) = Word.valSum (u' ++ [a']) := by
        refine pow_eq_of_odd_div_two_pow hN hN' ?_
        rw [← hN₁, ← hN₁', hoff]
        field_simp
      -- subtract the common last term
      have hu : off u = off u' := by
        have e := off_append u [a]
        have e' := off_append u' [a']
        simp only [Word.valSum_append, Word.valSum_singleton] at hA
        simp only [off_cons, off_nil, mul_zero, add_zero, mul_one] at e e'
        rw [Word.weight, Word.valSum, div_eq_mul_inv] at e
        rw [Word.weight, Word.valSum, div_eq_mul_inv] at e'
        have h2 : (2 : ℚ) ^ ((u.map (↑) : List ℕ).sum) * 2 ^ (a : ℕ) =
            2 ^ ((u'.map (↑) : List ℕ).sum) * 2 ^ (a' : ℕ) := by
          rw [← pow_add, ← pow_add]
          exact congrArg (fun n : ℕ => (2 : ℚ) ^ n) hA
        have last : (3 : ℚ) ^ u.length * ((2 : ℚ) ^ ((u.map (↑) : List ℕ).sum))⁻¹ *
              ((2 : ℚ) ^ (a : ℕ))⁻¹ =
            (3 : ℚ) ^ u'.length * ((2 : ℚ) ^ ((u'.map (↑) : List ℕ).sum))⁻¹ *
              ((2 : ℚ) ^ (a' : ℕ))⁻¹ := by
          rw [hlen, mul_assoc, mul_assoc, ← mul_inv, ← mul_inv, h2]
        linarith [e, e', hoff, last]
      have huu := ih hlen hu
      subst huu
      simp only [Word.valSum_append, Word.valSum_singleton, add_right_inj] at hA
      rw [PNat.coe_inj.1 hA]

end CollatzPosDens
