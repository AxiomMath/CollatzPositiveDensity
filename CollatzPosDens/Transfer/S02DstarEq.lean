/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Dstar
public import CollatzPosDens.Transfer.S02PBits
public import CollatzPosDens.Transfer.S02ROmegaValue

/-!
# The descent threshold equals the scale threshold

At each Fourier parameter index `ι ∈ {o, b}` the descent threshold `D_*(ι)` is the maximum of
`D_bad(ι)` and `D_sc(ι)`. We show that this maximum is attained by the scale threshold:
`D_*(ι) = D_sc(ι)`.

From the exact values of `P_*(ι)` and `R_Ω(ι)`, the scale thresholds
`D_sc(o) = 2 + P_*(o) + ⌈2 R_Ω(o)^2 / 3⌉` and `D_sc(b) = 2 + P_*(b) + ⌈R_Ω(b)^2 / 2⌉` are the
explicit integers (`R_Ω(o)^2` is divisible by `3` and `R_Ω(b)^2` is even, so both ceilings are
exact quotients)
$$D_{\mathrm{sc}}(\mathrm o) = 1260064847115131240228229351654462380561780602,\qquad
  D_{\mathrm{sc}}(\mathrm b) = 267725467120047,$$
of binary lengths `150` and `48`; so `2^149 ≤ D_sc(o)` and `2^47 ≤ D_sc(b)`. The other entry
`D_bad(ι) = 2^21 (P_*(ι) + 64)` is smaller: it is below `2^116` (from `P_*(ι) < 2^94`) and, for
`ι = b`, equal to `2^21 · 63702059 = 133592900435968 < 2^47`.

## Main results

* `CollatzPosDens.Dsc_o`, `CollatzPosDens.Dsc_b`: the exact values of `D_sc(ι)`.
* `CollatzPosDens.two_pow_149_le_Dsc_o`, `CollatzPosDens.two_pow_47_le_Dsc`:
  `2^149 ≤ D_sc(o)` and `2^47 ≤ D_sc(ι)`.
* `CollatzPosDens.Dbad_b`: the exact value of `D_bad(b)`.
* `CollatzPosDens.Dbad_lt_two_pow`, `CollatzPosDens.Dbad_b_lt_two_pow`:
  `D_bad(ι) < 2^116` and `D_bad(b) < 2^47`.
* `CollatzPosDens.Dbad_lt_Dsc`: `D_bad(ι) < D_sc(ι)`.
* `CollatzPosDens.Dstar_eq_Dsc`: `D_*(ι) = D_sc(ι)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The exact value of the scale threshold `D_sc(o) = 2 + P_*(o) + ⌈2 R_Ω(o)^2 / 3⌉`, an integer
of binary length `150`. -/
theorem Dsc_o : Dsc .o = 1260064847115131240228229351654462380561780602 := by
  rw [Dsc_o_def, omegaFar_def, ROmega_value_o, pStar_o]
  norm_num

/-- The exact value of the scale threshold `D_sc(b) = 2 + P_*(b) + ⌈R_Ω(b)^2 / 2⌉
= 2 + 63701995 + 267725403418050`, an integer of binary length `48`. -/
theorem Dsc_b : Dsc .b = 267725467120047 := by
  rw [Dsc_b_def, omegaFar_def, ROmega_value_b, pStar_b]
  norm_num

/-- `2^149 ≤ D_sc(o)`. -/
theorem two_pow_149_le_Dsc_o : 2 ^ 149 ≤ Dsc .o := by
  rw [Dsc_o]
  norm_num

/-- `2^47 ≤ D_sc(ι)` for every index `ι`. -/
theorem two_pow_47_le_Dsc (ι : FIndex) : 2 ^ 47 ≤ Dsc ι := by
  cases ι
  · exact (Nat.pow_le_pow_right (by norm_num) (by norm_num)).trans two_pow_149_le_Dsc_o
  · rw [Dsc_b]
    norm_num

/-- `D_bad(ι) < 2^116` for every index `ι`. -/
theorem Dbad_lt_two_pow (ι : FIndex) : Dbad ι < 2 ^ 116 := by
  have hp := pStar_lt_two_pow ι
  rw [Dbad_def]
  calc 2 ^ 21 * (pStar ι + 64) < 2 ^ 21 * (2 ^ 94 + 64) :=
        Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right hp 64) (by norm_num)
    _ ≤ 2 ^ 116 := by norm_num

/-- The exact value `D_bad(b) = 2^21 (P_*(b) + 64) = 2^21 · 63702059 = 133592900435968`. -/
theorem Dbad_b : Dbad .b = 133592900435968 := by
  rw [Dbad_def, pStar_b]
  norm_num

/-- `D_bad(b) < 2^47`, from `P_*(b) + 64 = 63702059 < 2^26`. -/
theorem Dbad_b_lt_two_pow : Dbad .b < 2 ^ 47 := by
  rw [Dbad_b]
  norm_num

/-- `D_bad(ι) < D_sc(ι)` for every index `ι`. -/
theorem Dbad_lt_Dsc (ι : FIndex) : Dbad ι < Dsc ι := by
  cases ι
  · exact (Dbad_lt_two_pow .o).trans_le
      ((Nat.pow_le_pow_right (by norm_num) (by norm_num)).trans two_pow_149_le_Dsc_o)
  · exact Dbad_b_lt_two_pow.trans_le (two_pow_47_le_Dsc .b)

/-- **The descent threshold is the scale threshold.** `D_*(ι) = D_sc(ι)` for every index
`ι`. -/
@[collatz_pos_dens "lem_s02_Dstar_eq"]
theorem Dstar_eq_Dsc (ι : FIndex) : Dstar ι = Dsc ι :=
  le_antisymm (Dstar_le_iff.2 ⟨(Dbad_lt_Dsc ι).le, le_rfl⟩) (Dsc_le_Dstar ι)

end CollatzPosDens
