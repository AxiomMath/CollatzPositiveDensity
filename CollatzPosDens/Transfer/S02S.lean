/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02K
public import CollatzPosDens.Transfer.S02Schedule
public import CollatzPosDens.Transfer.Rstar

/-!
# The interval sizes `S_i` of the trace schedule

For a Fourier index `ι ∈ {o, b}` and `0 ≤ i ≤ r_*(ι)`, the `i`-th interval size of the trace
schedule is the natural number
$$\mathsf S_i(ι) := K_{*,i}(ι)\,(p_i(ι) + 1),$$
where `K_{*,i}(ι)` is the `i`-th size factor and `p_i(ι)` the `i`-th schedule position. Since
`K_{*,i}(ι) ≥ 268`, each `S_i(ι)` is positive and exceeds `p_i(ι)`.

## Main definitions

* `CollatzPosDens.sStar`: the interval size `S_i(ι) = K_{*,i}(ι) (p_i(ι) + 1)`.

## Main results

* `CollatzPosDens.sStar_def`: the defining formula `S_i = K_{*,i} (p_i + 1)`.
* `CollatzPosDens.sStar_cast`: the same formula in any semiring, e.g. in `ℝ`.
* `CollatzPosDens.sStar_pos`: `0 < S_i`.
* `CollatzPosDens.le_sStar`: `268 (p_i(ι) + 1) ≤ S_i(ι)`.
* `CollatzPosDens.schedule_lt_sStar`: `p_i < S_i`.

## Implementation notes

The interval sizes are only meaningful for `0 ≤ i ≤ r_*(ι)`. The definition is total on `ℕ`,
since both `K_{*,i}` and `p_i` are; its values at `i > r_*` are never used.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The interval sizes of the trace schedule at the index `ι`:
`S_i(ι) := K_{*,i}(ι) (p_i(ι) + 1)`, for `0 ≤ i ≤ r_*(ι)`. -/
@[collatz_pos_dens "def_s02_S"]
def sStar (ι : FIndex) (i : ℕ) : ℕ := Kstar ι i * (schedule ι i + 1)

/-- The defining formula `S_i(ι) = K_{*,i}(ι) (p_i(ι) + 1)`. -/
theorem sStar_def (ι : FIndex) (i : ℕ) : sStar ι i = Kstar ι i * (schedule ι i + 1) := rfl

/-- The defining formula of `S_i(ι)`, cast to a semiring (typically `ℝ`). -/
theorem sStar_cast {R : Type*} [Semiring R] (ι : FIndex) (i : ℕ) :
    (sStar ι i : R) = (Kstar ι i : R) * ((schedule ι i : R) + 1) := by
  rw [sStar_def, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- Every interval size is positive. -/
theorem sStar_pos (ι : FIndex) (i : ℕ) : 0 < sStar ι i :=
  Nat.mul_pos (Kstar_pos ι i) (Nat.succ_pos _)

/-- The interval size is at least `268 (p_i(ι) + 1)`, since `K_{*,i}(ι) ≥ 268`. -/
theorem le_sStar (ι : FIndex) (i : ℕ) : 268 * (schedule ι i + 1) ≤ sStar ι i :=
  Nat.mul_le_mul_right _ (le_Kstar ι i)

/-- The schedule position `p_i(ι)` is strictly smaller than the interval size `S_i(ι)`. -/
theorem schedule_lt_sStar (ι : FIndex) (i : ℕ) : schedule ι i < sStar ι i := by
  have := le_sStar ι i
  omega

end CollatzPosDens
