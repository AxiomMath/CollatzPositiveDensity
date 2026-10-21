/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17Cost
public import CollatzPosDens.Case3.C3CapRange
public import CollatzPosDens.Renewal.RnPascalTotal

/-!
# Range of the height-seventeen future cost

For every integer `h` and real `z`, the future cost `cf_h(z)` (`CollatzPosDens.c3H17Cost`) lies
in the unit interval `[0, 1]`.

The proof is by downward induction on `h`. For `h ≥ 15` the value is `1`. For `h ≤ 14`, every
capped packet factor `Φ^cap_d(·)` lies in `[0, 1]` (`CollatzPosDens.trCapFactor_mem_Icc`) and every
second factor lies in `[0, 1]` by the induction hypothesis, so every bracket
`1 - Φ^cap_d(z / 2^{h+d}) · R_d` lies in `[0, 1]`. Since `ϖ ≥ 0` and the Pascal weights have total
mass `1` (`CollatzPosDens.hasSum_varpi`), the weighted sum of the brackets lies in `[0, 1]`, hence
so does `cf_h(z)`.

## Main results

* `CollatzPosDens.c3H17Cost_mem_Icc`: `0 ≤ cf_h(z) ≤ 1`.

## Implementation notes

The bound is often stated only for `h ≥ 1`; it holds, with the same proof, for every integer `h`,
and is stated so here.

## References

* [Mazur, *Collatz positive density*], §10.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The height-seventeen future cost lies in the unit interval: `0 ≤ cf_h(z) ≤ 1`. -/
@[collatz_pos_dens "lem_c3_h17_cost_range"]
theorem c3H17Cost_mem_Icc (h : ℤ) (z : ℝ) : c3H17Cost h z ∈ Set.Icc (0 : ℝ) 1 := by
  induction hn : (15 - h).toNat using Nat.strong_induction_on generalizing h z with
  | _ n ih =>
  rcases le_or_gt 15 h with hh | hh
  · rw [c3H17Cost_of_le hh]
    exact ⟨zero_le_one, le_rfl⟩
  rw [c3H17Cost_of_lt hh]
  set s := Finset.Icc (2 : ℤ) (17 - h)
  set f : ℤ → ℝ := fun d => 1 - trCapFactor d (z / (2 : ℝ) ^ (h + d)) *
    if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Cost (h + d) (9 * z) else 1 with hf
  have hb : ∀ d ∈ s, f d ∈ Set.Icc (0 : ℝ) 1 := by
    intro d hd
    have hds := (Finset.mem_Icc.mp hd)
    have hR : (if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Cost (h + d) (9 * z) else 1)
        ∈ Set.Icc (0 : ℝ) 1 := by
      split_ifs with hc
      · exact ih (15 - (h + d)).toNat (by omega) (h + d) (9 * z) rfl
      · exact ⟨zero_le_one, le_rfl⟩
    obtain ⟨hc0, hc1⟩ := trCapFactor_mem_Icc d (z / (2 : ℝ) ^ (h + d))
    obtain ⟨hR0, hR1⟩ := hR
    refine ⟨?_, ?_⟩
    · simp only [hf]
      nlinarith
    · simp only [hf]
      nlinarith
  have hsum0 : 0 ≤ ∑ d ∈ s, varpi d * f d :=
    Finset.sum_nonneg fun d hd => mul_nonneg (varpi_nonneg d) (hb d hd).1
  have hsum1 : ∑ d ∈ s, varpi d * f d ≤ 1 :=
    calc ∑ d ∈ s, varpi d * f d ≤ ∑ d ∈ s, varpi d :=
          Finset.sum_le_sum fun d hd => mul_le_of_le_one_right (varpi_nonneg d) (hb d hd).2
      _ ≤ 1 := sum_le_hasSum s (fun d _ => varpi_nonneg d) hasSum_varpi
  exact ⟨by linarith, by linarith⟩

end CollatzPosDens
