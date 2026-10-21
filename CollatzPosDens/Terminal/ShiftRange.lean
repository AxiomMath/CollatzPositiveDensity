/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.History
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.TerminalShift
public import CollatzPosDens.Terminal.UpperScale

/-!
# The range of the terminal shift

Let `X` be admissible for generation `j` at the target `t`, let `h ∈ 𝓗_j(t)`, `b = b_j` and
`u = u_h`. Then `0 ≤ u ≤ 2 r_b`. Indeed, admissibility gives
`L_b(R_h) < X ≤ U_b(R_h) = 2^{2 r_b} L_b(R_h)`, which forces `L_b(R_h) > 0` and `2 r_b > 0`;
hence `2 r_b` is a natural exponent satisfying the defining inequality of `u_h`, and `u_h ≤ 2 r_b`
by minimality.

## Main results

* `CollatzPosDens.IsAdmissibleScale.historyShift_mem_Icc`: `0 ≤ u_h ≤ 2 r_{b_j}`.

## Implementation notes

The shift `u_h` is a natural number while `r_b` is an integer, so the bound is stated in `ℤ`.
In [mazur2026] the target `t` is an odd positive integer; the argument uses neither the oddness
nor the positivity of `t`, nor that of the endpoint `R_h`: admissibility alone forces
`L_{b_j}(R_h) > 0`. The target is therefore an arbitrary rational, as in
`CollatzPosDens.centralHistories`. A history of generation `j` is a tuple `(w₀, …, w_{j-1})`,
indexed by `Fin j`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §17.1.
-/

@[expose] public section

namespace CollatzPosDens

namespace IsAdmissibleScale

variable {t : ℚ} {j : ℕ} {X : ℝ}

/-- If `X` is admissible for generation `j` and `h ∈ 𝓗_j(t)`, then the terminal shift
`u_h` satisfies `0 ≤ u_h ≤ 2 r_{b_j}`. -/
@[collatz_pos_dens "lem_shift_range"]
theorem historyShift_mem_Icc (hX : IsAdmissibleScale t j X) {h : Fin j → Word}
    (hh : h ∈ centralHistories t j) :
    (historyShift j X t h : ℤ) ∈ Set.Icc 0 (2 * rb (scale j)) := by
  set L := lowerScale (scale j) (historyEndpoint t h : ℝ)
  have hlow : L < X := hX.lowerScale_lt hh
  have hup : X ≤ (2 : ℝ) ^ (2 * rb (scale j)) * L := by
    simpa [upperScale_def] using hX.le_upperScale hh
  have hpow : (0 : ℝ) < 2 ^ (2 * rb (scale j)) := by positivity
  have hLpos : 0 < L := by nlinarith [hX.pos]
  have hone : (1 : ℝ) < 2 ^ (2 * rb (scale j)) := by nlinarith
  have hr : 0 < 2 * rb (scale j) := (one_lt_zpow_iff_right₀ one_lt_two).1 hone
  lift 2 * rb (scale j) to ℕ using hr.le with k
  rw [zpow_natCast] at hup
  exact ⟨Int.natCast_nonneg _, Nat.cast_le.2 (Nat.sInf_le hup)⟩

end IsAdmissibleScale

end CollatzPosDens
