/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02HDef
public import CollatzPosDens.Transfer.S02Schedule

/-!
# Clearing counts of a schedule

For `ι : FIndex`, write `p_i := schedule ι i`, `r_* := rStar ι`, `P_* := pStar ι` and
`h_*(u) := windowLength ι u`. The `i`th clearing block starts at the time `a_i`, where `a_0 := 0`
and `a_i := p_{i-1} + 1` for `1 ≤ i ≤ r_*`. It ends at the time `min(p_i, P_* - 1 - h_*(p_i))`, an
integer which may be negative. The clearing count is the number of integer times in the block,
$$n^{\mathrm{cl}}_i := \max\bigl(0,\ \min(p_i,\ P_* - 1 - h_*(p_i)) - a_i + 1\bigr) \in ℕ .$$
When `p_i + h_*(p_i) + 1 ≤ P_*` the minimum is `p_i`, so `n^cl_0 = p_0 + 1` and
`n^cl_{i+1} = p_{i+1} - p_i`; when `P_* ≤ a_i + h_*(p_i)` the block is empty and `n^cl_i = 0`.

## Main definitions

* `CollatzPosDens.clearStart`: the first time `a_i` of the `i`th clearing block.
* `CollatzPosDens.clearCount`: the clearing count `n^cl_i`.

## Main results

* `CollatzPosDens.natCast_clearCount`: `n^cl_i = max(0, min(p_i, P_* - 1 - h_*(p_i)) - a_i + 1)`
  in `ℤ`.
* `CollatzPosDens.clearCount_le`: `n^cl_i ≤ p_i + 1 - a_i`.
* `CollatzPosDens.clearCount_of_le`: if `p_i + h_*(p_i) + 1 ≤ P_*` then `n^cl_i = p_i + 1 - a_i`.
* `CollatzPosDens.clearCount_zero_of_le`: if `p_0 + h_*(p_0) + 1 ≤ P_*` then `n^cl_0 = p_0 + 1`.
* `CollatzPosDens.clearCount_succ_of_le`: if `p_{i+1} + h_*(p_{i+1}) + 1 ≤ P_*` then
  `n^cl_{i+1} = p_{i+1} - p_i`.
* `CollatzPosDens.clearCount_eq_zero_of_le`: if `P_* ≤ a_i + h_*(p_i)` then `n^cl_i = 0`.

## Implementation notes

The clearing blocks are indexed by `0 ≤ i ≤ r_*(ι)` (`CollatzPosDens.rStar`). Both `clearStart`
and `clearCount` are total functions on `ℕ`, given by the same formulas for every `i`, including
`i > r_*`. The maximum with `0` of an integer is `Int.toNat`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The first time of the `i`th clearing block: `a_0 := 0` and `a_{i+1} := p_i(ι) + 1`. -/
def clearStart (ι : FIndex) : ℕ → ℕ
  | 0 => 0
  | i + 1 => schedule ι i + 1

/-- The `0`th clearing block starts at time `0`. -/
@[simp]
theorem clearStart_zero (ι : FIndex) : clearStart ι 0 = 0 := rfl

/-- The `(i+1)`st clearing block starts at time `p_i(ι) + 1`. -/
@[simp]
theorem clearStart_succ (ι : FIndex) (i : ℕ) : clearStart ι (i + 1) = schedule ι i + 1 := rfl

/-- The `i`th clearing block starts no later than `p_i(ι) + 1`, its last possible time plus
one. -/
theorem clearStart_le_schedule_add_one (ι : FIndex) (i : ℕ) :
    clearStart ι i ≤ schedule ι i + 1 := by
  cases i with
  | zero => simp
  | succ i => simpa using (schedule_lt_schedule_succ ι i).le

/-- The clearing count
`n^cl_i(ι) := max(0, min(p_i(ι), P_*(ι) - 1 - h_*(ι, p_i(ι))) - a_i + 1) ∈ ℕ`, the number of
integer times of the `i`th clearing block. -/
@[collatz_pos_dens "def_s02_clear_count"]
noncomputable def clearCount (ι : FIndex) (i : ℕ) : ℕ :=
  (min (schedule ι i : ℤ) ((pStar ι : ℤ) - 1 - windowLength ι (schedule ι i)) -
    clearStart ι i + 1).toNat

/-- The clearing count `n^cl_i(ι)` is the `Int.toNat` of
`min(p_i, P_* - 1 - h_*(p_i)) - a_i + 1`. -/
theorem clearCount_def (ι : FIndex) (i : ℕ) :
    clearCount ι i =
      (min (schedule ι i : ℤ) ((pStar ι : ℤ) - 1 - windowLength ι (schedule ι i)) -
        clearStart ι i + 1).toNat :=
  rfl

/-- The clearing count as a maximum in `ℤ`:
`n^cl_i(ι) = max(0, min(p_i, P_* - 1 - h_*(p_i)) - a_i + 1)`. -/
theorem natCast_clearCount (ι : FIndex) (i : ℕ) :
    (clearCount ι i : ℤ) =
      max 0 (min (schedule ι i : ℤ) ((pStar ι : ℤ) - 1 - windowLength ι (schedule ι i)) -
        clearStart ι i + 1) := by
  rw [clearCount_def, Int.toNat_eq_max, max_comm]

/-- The clearing count is at most the length `p_i + 1 - a_i` of the time range `[a_i, p_i]`. -/
theorem clearCount_le (ι : FIndex) (i : ℕ) :
    clearCount ι i ≤ schedule ι i + 1 - clearStart ι i := by
  have h := natCast_clearCount ι i
  have ha := clearStart_le_schedule_add_one ι i
  have hm := min_le_left (schedule ι i : ℤ) ((pStar ι : ℤ) - 1 - windowLength ι (schedule ι i))
  have hle : (clearCount ι i : ℤ) ≤ ((schedule ι i + 1 - clearStart ι i : ℕ) : ℤ) := by
    rw [h, Nat.cast_sub ha]
    push_cast
    exact max_le (by omega) (by omega)
  exact_mod_cast hle

/-- If `p_i + h_*(p_i) + 1 ≤ P_*`, the minimum is `p_i` and `n^cl_i(ι) = p_i + 1 - a_i`. -/
theorem clearCount_of_le {ι : FIndex} {i : ℕ}
    (h : schedule ι i + windowLength ι (schedule ι i) + 1 ≤ pStar ι) :
    clearCount ι i = schedule ι i + 1 - clearStart ι i := by
  have hc := natCast_clearCount ι i
  have ha := clearStart_le_schedule_add_one ι i
  rw [min_eq_left (by omega)] at hc
  omega

/-- If `p_0 + h_*(p_0) + 1 ≤ P_*`, then `n^cl_0(ι) = p_0 + 1`. -/
theorem clearCount_zero_of_le {ι : FIndex}
    (h : schedule ι 0 + windowLength ι (schedule ι 0) + 1 ≤ pStar ι) :
    clearCount ι 0 = schedule ι 0 + 1 := by
  simpa using clearCount_of_le h

/-- If `p_{i+1} + h_*(p_{i+1}) + 1 ≤ P_*`, then `n^cl_{i+1}(ι) = p_{i+1} - p_i`. -/
theorem clearCount_succ_of_le {ι : FIndex} {i : ℕ}
    (h : schedule ι (i + 1) + windowLength ι (schedule ι (i + 1)) + 1 ≤ pStar ι) :
    clearCount ι (i + 1) = schedule ι (i + 1) - schedule ι i := by
  rw [clearCount_of_le h, clearStart_succ]
  omega

/-- If `P_* ≤ a_i + h_*(p_i)`, the `i`th clearing block is empty and `n^cl_i(ι) = 0`. -/
theorem clearCount_eq_zero_of_le {ι : FIndex} {i : ℕ}
    (h : pStar ι ≤ clearStart ι i + windowLength ι (schedule ι i)) :
    clearCount ι i = 0 := by
  have hc := natCast_clearCount ι i
  have := min_le_right (schedule ι i : ℤ) ((pStar ι : ℤ) - 1 - windowLength ι (schedule ι i))
  rw [max_eq_left (by omega)] at hc
  omega

end CollatzPosDens
