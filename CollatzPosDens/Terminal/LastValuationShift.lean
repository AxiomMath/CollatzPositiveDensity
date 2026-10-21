/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.Ring
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Admissible
public import CollatzPosDens.Maps.ConcatAdmissible

/-!
# Shifting the last valuation of an admissible word

Let `w = (a₁, …, a_d)`, `d ≥ 1`, be admissible from `R` with source `x = src(w, R)`, and for
`i ≥ 0` let `w^{+i} = (a₁, …, a_{d-1}, a_d + 2i)`. Then `w^{+i}` is admissible from `R` and
`src(w^{+i}, R) = 4 ^ i x + (4 ^ i - 1) / 3`. The two inverse orbits agree up to index `d - 1`,
and from `3x + 1 = 2 ^ {a_d} R_{d-1}` the last term of the new orbit is
`(4 ^ i (3x + 1) - 1) / 3 = 4 ^ i x + (4 ^ i - 1) / 3`, an integer because `4 ≡ 1 [MOD 3]`.

## Main definitions

* `CollatzPosDens.shiftLastLetter a i`: the letter `a + 2i`.

## Main results

* `CollatzPosDens.src_shiftLastLetter`: `src(w^{+i}, R) = 4 ^ i src(w, R) + (4 ^ i - 1) / 3`.
* `CollatzPosDens.admissible_append_shiftLastLetter_iff`: `w^{+i}` is admissible from `R` iff `w`
  is (both directions use `4 ≡ 1 [MOD 3]`).
* `CollatzPosDens.Admissible.shiftLastLetter`: `w^{+i}` is admissible from `R` whenever `w` is.

## Implementation notes

A nonempty word is written `u ++ [a]`, with `u = (a₁, …, a_{d-1})` and `a = a_d`, so `w^{+i}`
is `u ++ [shiftLastLetter a i]`. Neither oddness nor positivity of `R`
is needed, so the results hold for every rational `R`, and the formula for the source holds with
no admissibility assumption at all.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The letter `a + 2i`, the last letter of the shifted word `w^{+i}`. -/
def shiftLastLetter (a : ℕ+) (i : ℕ) : ℕ+ := ⟨a + 2 * i, Nat.add_pos_left a.pos _⟩

/-- The value of the shifted letter `a + 2i` as a natural number. -/
@[simp] lemma coe_shiftLastLetter (a : ℕ+) (i : ℕ) :
    (shiftLastLetter a i : ℕ) = a + 2 * i := rfl

/-- Raising the last letter of a word by `2i` changes its source `x` to
`4 ^ i x + (4 ^ i - 1) / 3`. -/
@[collatz_pos_dens "lem_last_valuation_shift"]
theorem src_shiftLastLetter (u : Word) (a : ℕ+) (i : ℕ) (R : ℚ) :
    src (u ++ [shiftLastLetter a i]) R = 4 ^ i * src (u ++ [a]) R + (4 ^ i - 1) / 3 := by
  simp only [src_concat, invStep, coe_shiftLastLetter, pow_add, pow_mul]
  ring

/-- From an integer `n`, the one-letter word `[b]` is admissible iff `3 ∣ 2 ^ b n - 1`. -/
theorem admissible_singleton_intCast_iff (n : ℤ) (b : ℕ+) :
    Admissible n [b] ↔ (3 : ℤ) ∣ 2 ^ (b : ℕ) * n - 1 := by
  have hstep : invStep b n = ((2 ^ (b : ℕ) * n - 1 : ℤ) : ℚ) / ((3 : ℤ) : ℚ) := by
    simp [invStep]
  rw [← Rat.den_div_intCast_eq_one_iff _ 3 (by norm_num), ← hstep]
  refine ⟨fun h => by simpa [inverseOrbit] using h 1 le_rfl, fun h i hi => ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hi) with rfl | rfl
  · simp
  · simpa [inverseOrbit] using h

/-- From an integer `n`, the one-letter word `[a + 2i]` is admissible iff `[a]` is, since
`4 ≡ 1 [MOD 3]`. -/
theorem admissible_singleton_shiftLastLetter_iff (n : ℤ) (a : ℕ+) (i : ℕ) :
    Admissible n [shiftLastLetter a i] ↔ Admissible n [a] := by
  rw [admissible_singleton_intCast_iff, admissible_singleton_intCast_iff, coe_shiftLastLetter]
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (4 : ℤ) 1 i
  have hsplit : (2 : ℤ) ^ ((a : ℕ) + 2 * i) * n - 1 =
      (4 ^ i - 1 ^ i) * (2 ^ (a : ℕ) * n) + (2 ^ (a : ℕ) * n - 1) := by
    rw [pow_add, pow_mul]; norm_num; ring
  rw [hsplit, hc]
  exact dvd_add_right ⟨c * (2 ^ (a : ℕ) * n), by ring⟩

/-- Raising the last letter by `2i` does not change admissibility: `u ++ [a + 2i]` is admissible
from `R` iff `u ++ [a]` is. -/
theorem admissible_append_shiftLastLetter_iff {R : ℚ} {u : Word} {a : ℕ+} (i : ℕ) :
    Admissible R (u ++ [CollatzPosDens.shiftLastLetter a i]) ↔ Admissible R (u ++ [a]) := by
  rw [admissible_append, admissible_append]
  refine and_congr_right fun hu => ?_
  obtain ⟨n, hn⟩ : ∃ n : ℤ, src u R = n :=
    ⟨_, (Rat.coe_int_num_of_den_eq_one hu.den_src_eq_one).symm⟩
  rw [hn]
  exact admissible_singleton_shiftLastLetter_iff n a i

/-- If `w = u ++ [a]` is admissible from `R`, then so is `w^{+i} = u ++ [a + 2i]`. -/
@[collatz_pos_dens "lem_last_valuation_shift"]
theorem Admissible.shiftLastLetter {R : ℚ} {u : Word} {a : ℕ+} (h : Admissible R (u ++ [a]))
    (i : ℕ) : Admissible R (u ++ [CollatzPosDens.shiftLastLetter a i]) :=
  (admissible_append_shiftLastLetter_iff i).2 h

end CollatzPosDens
