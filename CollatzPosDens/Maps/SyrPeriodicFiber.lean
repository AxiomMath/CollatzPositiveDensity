/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.SyrPeriodic
public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Syracuse-periodic integers with a common image

Two Syracuse-periodic integers with the same Syracuse image are equal: if `S^j(M) = M` and
`S^{j'}(M') = M'` with `j, j' ≥ 1`, then both are fixed by `S^n` for `n = j j'`, and
`M = S^{n-1}(S M) = S^{n-1}(S M') = M'`.

## Main results

* `CollatzPosDens.SyrPeriodic.eq_of_collatzAccel_eq`: if `M` and `M'` are Syracuse-periodic and
  `collatzAccel M = collatzAccel M'`, then `M = M'`.

## Implementation notes

The argument uses nothing about the Syracuse map: it holds for any self-map, and the positivity
and oddness hypotheses of Mazur's statement are not needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Two Syracuse-periodic integers with the same Syracuse image are equal. -/
@[collatz_pos_dens "lem_syr_periodic_fiber"]
theorem SyrPeriodic.eq_of_collatzAccel_eq {M M' : ℕ} (hM : SyrPeriodic M)
    (hM' : SyrPeriodic M') (h : collatzAccel M = collatzAccel M') : M = M' := by
  obtain ⟨j, hj, hjM⟩ := hM
  obtain ⟨j', hj', hjM'⟩ := hM'
  have h1 : Function.IsPeriodicPt collatzAccel (j * j') M :=
    Function.IsPeriodicPt.mul_const hjM j'
  have h2 : Function.IsPeriodicPt collatzAccel (j * j') M' := by
    rw [mul_comm]; exact Function.IsPeriodicPt.mul_const hjM' j
  obtain ⟨n, hn⟩ : ∃ n, j * j' = n + 1 :=
    ⟨j * j' - 1, (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega)))).symm⟩
  rw [hn] at h1 h2
  rw [← h1.eq, ← h2.eq, Function.iterate_succ_apply, Function.iterate_succ_apply, h]

end CollatzPosDens
