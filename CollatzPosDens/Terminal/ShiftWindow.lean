/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.TerminalShift

/-!
# The terminal shift window

Let `X` be admissible for generation `n` from the seed `M`, let `h ∈ 𝓗_n(M)`, `b = b_n` and
`u = u_h`. Then `X ≤ 2^u L_b(R_h) < 2X`.

The lower bound is the defining property of `u`. Since `X` is admissible, `L_b(R_h) < X`, so
`u = 0` does not satisfy the defining inequality; hence `u ≥ 1` and, by minimality,
`2^{u-1} L_b(R_h) < X`, that is `2^u L_b(R_h) < 2X`.

## Main results

* `CollatzPosDens.IsAdmissibleScale.historyEndpoint_pos`: `R_h > 0` for `h ∈ 𝓗_n(M)`.
* `CollatzPosDens.IsAdmissibleScale.shift_window`: `X ≤ 2^{u_h} L_{b_n}(R_h) < 2X`.

## Implementation notes

The seed is an arbitrary `M : ℚ` rather than an odd positive integer; the statement holds in
that generality. The positivity `R_h > 0`, needed for `u_h` to satisfy its defining inequality,
is derived from admissibility: `0 < X ≤ U_{b_n}(R_h) = U_{b_n}(1) R_h`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §18.
-/

@[expose] public section

namespace CollatzPosDens

namespace IsAdmissibleScale

variable {M : ℚ} {n : ℕ} {X : ℝ}

/-- If `X` is admissible for generation `n`, the endpoint `R_h` of every central history
`h ∈ 𝓗_n(M)` is positive. -/
theorem historyEndpoint_pos (hX : IsAdmissibleScale M n X) {h : Fin n → Word}
    (hh : h ∈ centralHistories M n) : (0 : ℝ) < historyEndpoint M h := by
  by_contra! hR
  have hU := hX.le_upperScale hh
  rw [upperScale_eq_mul] at hU
  have h1 : 0 < upperScale (scale n) 1 := upperScale_pos _ one_pos
  have : upperScale (scale n) 1 * (historyEndpoint M h : ℝ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h1.le hR
  linarith [hX.pos]

/-- **Shift window.** If `X` is admissible for generation `n` and `h ∈ 𝓗_n(M)`, then with
`b = b_n` and `u = u_h` one has `X ≤ 2^u L_b(R_h) < 2X`. -/
@[collatz_pos_dens "lem_s06_shift_window"]
theorem shift_window (hX : IsAdmissibleScale M n X) {h : Fin n → Word}
    (hh : h ∈ centralHistories M n) :
    X ≤ 2 ^ historyShift n X M h * lowerScale (scale n) (historyEndpoint M h) ∧
      2 ^ historyShift n X M h * lowerScale (scale n) (historyEndpoint M h) < 2 * X := by
  have hR := hX.historyEndpoint_pos hh
  refine ⟨le_two_pow_terminalShift_mul n X hR, ?_⟩
  have hL := hX.lowerScale_lt hh
  obtain hu | hu := Nat.eq_zero_or_pos (historyShift n X M h)
  · rw [hu, pow_zero, one_mul]
    linarith [hX.pos]
  · have hlt : 2 ^ (historyShift n X M h - 1) *
        lowerScale (scale n) (historyEndpoint M h) < X :=
      lt_of_lt_terminalShift (Nat.sub_lt hu one_pos)
    obtain ⟨k, hk⟩ : ∃ k, historyShift n X M h = k + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hu).symm⟩
    rw [hk, Nat.add_sub_cancel] at hlt
    rw [hk, pow_succ]
    linarith

end IsAdmissibleScale

end CollatzPosDens
