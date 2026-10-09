/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.FirstCrossing.Scales

/-!
# The terminal shift `u_{n,X}(R)`

For `n ≥ 0`, a real `X > 0` and a real `R > 0`, the terminal shift `u_{n,X}(R)` is the least
natural number `u` with `2^u L_{b_n}(R) ≥ X`, where `L_b` is the lower scale and `b_n` the
`n`-th scale. For a central history `h ∈ 𝓗_n(M)` one abbreviates `u_h := u_{n,X}(R_h)`, with
`R_h` the endpoint of `h`.

## Main definitions

* `CollatzPosDens.terminalShift`: the terminal shift `u_{n,X}(R)`.
* `CollatzPosDens.historyShift`: the shift `u_h = u_{n,X}(R_h)` of a history.

## Main results

* `CollatzPosDens.exists_terminalShift`: some `u` satisfies `X ≤ 2^u L_{b_n}(R)` when `R > 0`.
* `CollatzPosDens.le_two_pow_terminalShift_mul`: `X ≤ 2^{u_{n,X}(R)} L_{b_n}(R)` when `R > 0`.
* `CollatzPosDens.lt_of_lt_terminalShift`: below `u_{n,X}(R)` the inequality fails.
* `CollatzPosDens.terminalShift_le_iff`: `u_{n,X}(R) ≤ u ↔ X ≤ 2^u L_{b_n}(R)` when `R > 0`.
* `CollatzPosDens.terminalShift_eq_zero_of_le`: `u_{n,X}(R) = 0` when `X ≤ L_{b_n}(R)`.

## Implementation notes

The shift is defined as the infimum of `{u | X ≤ 2^u L_{b_n}(R)}` for all `X R : ℝ`, so it is a
total function; when the set is empty (which can only happen if `R ≤ 0`) the value is `0`.
The positivity of `R` is a hypothesis of the lemmas that need the set to be nonempty; the
positivity of `X` is never needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The terminal shift `u_{n,X}(R)`: the least `u ∈ ℕ` with `X ≤ 2^u L_{b_n}(R)`, or `0` if
there is no such `u` (which can only happen when `R ≤ 0`). -/
@[collatz_pos_dens "def_terminal_shift"]
noncomputable def terminalShift (n : ℕ) (X R : ℝ) : ℕ :=
  sInf {u : ℕ | X ≤ 2 ^ u * lowerScale (scale n) R}

/-- The shift `u_h = u_{n,X}(R_h)` of a history `h` of generation `n` from `M`, where `R_h` is
the endpoint of `h`. -/
@[collatz_pos_dens "def_terminal_shift"]
noncomputable abbrev historyShift (n : ℕ) (X : ℝ) (M : ℚ) (h : Fin n → Word) : ℕ :=
  terminalShift n X (historyEndpoint M h : ℝ)

/-- The terminal shift `u_{n,X}(R)` is the infimum of `{u ∈ ℕ | X ≤ 2^u L_{b_n}(R)}`. -/
theorem terminalShift_def (n : ℕ) (X R : ℝ) :
    terminalShift n X R = sInf {u : ℕ | X ≤ 2 ^ u * lowerScale (scale n) R} := rfl

/-- For `R > 0` some shift `u` satisfies `X ≤ 2^u L_{b_n}(R)`. -/
theorem exists_terminalShift (n : ℕ) (X : ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ u : ℕ, X ≤ 2 ^ u * lowerScale (scale n) R := by
  have hL := lowerScale_pos (scale n) hR
  obtain ⟨u, hu⟩ := pow_unbounded_of_one_lt (X / lowerScale (scale n) R) one_lt_two
  exact ⟨u, ((div_lt_iff₀ hL).1 hu).le⟩

/-- The terminal shift satisfies its defining inequality `X ≤ 2^{u_{n,X}(R)} L_{b_n}(R)`. -/
theorem le_two_pow_terminalShift_mul (n : ℕ) (X : ℝ) {R : ℝ} (hR : 0 < R) :
    X ≤ 2 ^ terminalShift n X R * lowerScale (scale n) R :=
  Nat.sInf_mem (exists_terminalShift n X hR)

/-- Minimality: for `u < u_{n,X}(R)` one has `2^u L_{b_n}(R) < X`. -/
theorem lt_of_lt_terminalShift {n u : ℕ} {X R : ℝ} (hu : u < terminalShift n X R) :
    2 ^ u * lowerScale (scale n) R < X :=
  lt_of_not_ge (Nat.notMem_of_lt_sInf hu)

/-- For `R > 0`, `u_{n,X}(R) ≤ u` exactly when `X ≤ 2^u L_{b_n}(R)`. -/
theorem terminalShift_le_iff {n u : ℕ} {X R : ℝ} (hR : 0 < R) :
    terminalShift n X R ≤ u ↔ X ≤ 2 ^ u * lowerScale (scale n) R := by
  refine ⟨fun h => (le_two_pow_terminalShift_mul n X hR).trans ?_, fun h => Nat.sInf_le h⟩
  have hL := lowerScale_pos (scale n) hR
  gcongr
  · norm_num

/-- The terminal shift vanishes when `X ≤ L_{b_n}(R)`. -/
theorem terminalShift_eq_zero_of_le {n : ℕ} {X R : ℝ} (h : X ≤ lowerScale (scale n) R) :
    terminalShift n X R = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (by simpa using h))

end CollatzPosDens
