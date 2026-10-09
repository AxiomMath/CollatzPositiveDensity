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

Let `X` be admissible for generation `n` from the seed `M`, let `h ∈ 𝓗_n(M)`, `b = b_n` and
`u = u_h`. Then `0 ≤ u ≤ 2 r_b`. Indeed, admissibility gives
`L_b(R_h) < X ≤ U_b(R_h) = 2^{2 r_b} L_b(R_h)`, which forces `L_b(R_h) > 0` and `2 r_b > 0`;
hence `2 r_b` is a natural exponent satisfying the defining inequality of `u_h`, and `u_h ≤ 2 r_b`
by minimality.

## Main results

* `CollatzPosDens.IsAdmissibleScale.historyShift_mem_Icc`: `0 ≤ u_h ≤ 2 r_{b_n}`.

## Implementation notes

The shift `u_h` is a natural number while `r_b` is an integer, so the bound is stated in `ℤ`.
The source takes `M` to be an odd positive integer; the argument uses neither the oddness nor
the positivity of `M`, nor that of the endpoint `R_h`: admissibility alone forces
`L_{b_n}(R_h) > 0`. The seed is therefore an arbitrary rational, as in
`CollatzPosDens.centralHistories`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace IsAdmissibleScale

variable {M : ℚ} {n : ℕ} {X : ℝ}

/-- If `X` is admissible for generation `n` and `h ∈ 𝓗_n(M)`, then the terminal shift
`u_h` satisfies `0 ≤ u_h ≤ 2 r_{b_n}`. -/
@[collatz_pos_dens "lem_shift_range"]
theorem historyShift_mem_Icc (hX : IsAdmissibleScale M n X) {h : Fin n → Word}
    (hh : h ∈ centralHistories M n) :
    (historyShift n X M h : ℤ) ∈ Set.Icc 0 (2 * rb (scale n)) := by
  set L := lowerScale (scale n) (historyEndpoint M h : ℝ)
  have hlow : L < X := hX.lowerScale_lt hh
  have hup : X ≤ (2 : ℝ) ^ (2 * rb (scale n)) * L := by
    simpa [upperScale_def] using hX.le_upperScale hh
  have hpow : (0 : ℝ) < 2 ^ (2 * rb (scale n)) := by positivity
  have hLpos : 0 < L := by nlinarith [hX.pos]
  have hone : (1 : ℝ) < 2 ^ (2 * rb (scale n)) := by nlinarith
  have hr : 0 < 2 * rb (scale n) := (one_lt_zpow_iff_right₀ one_lt_two).1 hone
  lift 2 * rb (scale n) to ℕ using hr.le with k
  rw [zpow_natCast] at hup
  exact ⟨Int.natCast_nonneg _, Nat.cast_le.2 (Nat.sInf_le hup)⟩

end IsAdmissibleScale

end CollatzPosDens
