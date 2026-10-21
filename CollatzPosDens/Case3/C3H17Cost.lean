/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.StoppingTrace.TrCapFactor

/-!
# The height-seventeen future cost

For integers `h` and reals `z` the future cost `cf_h(z)` is defined by downward recursion on `h`:
`cf_h(z) = 1` for `h ≥ 15`, and for `h ≤ 14`
`cf_h(z) = 1 - ∑_{d=2}^{17-h} ϖ(d) [1 - Φ^cap_d(z / 2^{h+d}) · R_d]`,
where `R_d = cf_{h+d}(9z)` if `d ∉ {4, 5}` and `h + d ≤ 15`, and `R_d = 1` otherwise. Here `ϖ` is
the Pascal weight `CollatzPosDens.varpi` and `Φ^cap_d` the capped packet factor
`CollatzPosDens.trCapFactor`.

## Main definitions

* `CollatzPosDens.c3H17Cost`: the future cost `cf_h(z)`.

## Main results

* `CollatzPosDens.c3H17Cost_of_le`: `cf_h(z) = 1` for `h ≥ 15`.
* `CollatzPosDens.c3H17Cost_of_lt`: the recursion for `h < 15`.

## Implementation notes

The index `h` ranges over all of `ℤ`; for `h ≤ 0`, where [mazur2026] defines no value, the same
recursion is used. The recursion terminates because every recursive call is at `h + d` with
`d ≥ 2` and `h + d ≤ 15`, so `15 - h` decreases.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The height-seventeen future cost: `cf_h(z) = 1` for `h ≥ 15`, and otherwise
`cf_h(z) = 1 - ∑_{d=2}^{17-h} ϖ(d) [1 - Φ^cap_d(z / 2^{h+d}) · R_d]` with
`R_d = cf_{h+d}(9z)` if `d ∉ {4, 5}` and `h + d ≤ 15`, and `R_d = 1` otherwise. -/
@[collatz_pos_dens "def_c3_h17_cost"]
noncomputable def c3H17Cost (h : ℤ) (z : ℝ) : ℝ :=
  if 15 ≤ h then 1
  else
    1 - ∑ d ∈ (Finset.Icc (2 : ℤ) (17 - h)).attach,
      varpi d * (1 - trCapFactor d (z / (2 : ℝ) ^ (h + d)) *
        if (d : ℤ) ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Cost (h + d) (9 * z) else 1)
termination_by (15 - h).toNat
decreasing_by
  have := d.2
  simp only [Finset.mem_Icc] at this
  omega

/-- The future cost is `1` from height `15` on. -/
theorem c3H17Cost_of_le {h : ℤ} (hh : 15 ≤ h) (z : ℝ) : c3H17Cost h z = 1 := by
  rw [c3H17Cost]
  simp [hh]

/-- The recursion defining the future cost below height `15`. -/
theorem c3H17Cost_of_lt {h : ℤ} (hh : h < 15) (z : ℝ) :
    c3H17Cost h z =
      1 - ∑ d ∈ Finset.Icc (2 : ℤ) (17 - h),
        varpi d * (1 - trCapFactor d (z / (2 : ℝ) ^ (h + d)) *
          if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Cost (h + d) (9 * z) else 1) := by
  rw [c3H17Cost, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    Finset.sum_attach _ (fun d : ℤ => varpi d * (1 - trCapFactor d (z / (2 : ℝ) ^ (h + d)) *
      if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Cost (h + d) (9 * z) else 1))]

end CollatzPosDens
