/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02ScheduleValues

/-!
# An upper bound on the final time `P_*`

The final time is `P_*(ι) = p_{r_*(ι)}(ι) + 1`. At the original index `r_*(o) = 10` and
`p_{10}(o) = 17140454471732661035095372255`, so `P_*(o) = 17140454471732661035095372256`; at the
bootstrap index `r_*(b) = 3` and `p_3(b) = 63701994`, so `P_*(b) = 63701995`. Both are below
`2^{94} = 19807040628566084398385987584`, so `P_*(ι) < 2^{94}` for every `ι`.

## Main results

* `CollatzPosDens.pStar_o`, `CollatzPosDens.pStar_b`: the exact values of `P_*(o)` and `P_*(b)`.
* `CollatzPosDens.pStar_lt_two_pow`: `P_*(ι) < 2^{94}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The exact value of the final time `P_*(o) = p_{10}(o) + 1`. -/
theorem pStar_o : pStar .o = 17140454471732661035095372256 := by
  have h : schedule .o 10 = 17140454471732661035095372255 := by
    simpa using congrArg (fun l : List ℕ => l.getD 10 0) schedule_values_o
  rw [pStar_def, rStar_o, h]

/-- The exact value of the final time `P_*(b) = p_3(b) + 1`. -/
theorem pStar_b : pStar .b = 63701995 := by
  have h : schedule .b 3 = 63701994 := by
    simpa using congrArg (fun l : List ℕ => l.getD 3 0) schedule_values_b
  rw [pStar_def, rStar_b, h]

/-- **Upper size of the final time.** `P_*(ι) < 2^{94}` for every index `ι`. -/
@[collatz_pos_dens "lem_s02_P_upper"]
theorem pStar_lt_two_pow (ι : FIndex) : pStar ι < 2 ^ 94 := by
  cases ι
  · rw [pStar_o]
    norm_num
  · rw [pStar_b]
    norm_num

end CollatzPosDens
