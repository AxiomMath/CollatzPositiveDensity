/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDirectCertificateData9a

/-!
# The direct-entry certificate at `ω = 9`: the cell `(1, 1)`, residues `5` to `37`

This file checks cells of the direct-entry certificate for the pair `(ω, p) = (9, 4)` used in
`CollatzPosDens.exists_trTreeCost_trWhitePolicy_sub_trTailGain_lt`. Every odd `m < 2^{12}` is
given a bisection shape (`CollatzPosDens.TrDirectCertificate.Shape`) of `[-1/3, 1/3]`: by default
the two halves of `[-1/3, 1/3]`, and for the 16 values of `m` listed in
`CollatzPosDens.TrDirectCertificate.excNine` a finer one. For the accepted cell `(1, 1)` of the
default shape and each odd residue `ρ` with `5 ≤ ρ ≤ 37`, the check
`CollatzPosDens.TrDirectCertificate.cellCheck` holds for every odd `m < 2^{12}` with
`m ≡ ρ (mod 64)` whose shape has that cell, each residue class in its own declaration.

## References

* [Mazur, *Collatz positive density*], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrDirectCertificate

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 5 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_5 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 5 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 7 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_7 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 7 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 9 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_9 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 9 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 11 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_11 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 11 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 13 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_13 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 13 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 15 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_15 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 15 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 17 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_17 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 17 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 19 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_19 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 19 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 21 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_21 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 21 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 23 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_23 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 23 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 25 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_25 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 25 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 27 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_27 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 27 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 29 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_29 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 29 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 31 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_31 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 31 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 33 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_33 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 33 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 35 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_35 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 35 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 37 (mod 64)` whose shape has the accepted cell `(1, 1)`. -/
theorem cellCheck_nine_1_1_37 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 37 (1, 1) dfltNine excNine) = true := by
  decide +kernel

end TrDirectCertificate

end CollatzPosDens
