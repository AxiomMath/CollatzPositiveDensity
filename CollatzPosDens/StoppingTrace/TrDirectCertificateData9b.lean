/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDirectCertificateData9a

/-!
# The direct-entry certificate at `ω = 9`: the cells `(1, 0)` for `ρ ≥ 35` and `(1, 1)` for `ρ ≤ 3`

This file checks cells of the direct-entry certificate for the pair `(ω, p) = (9, 4)` (see
`CollatzPosDens.exists_trTreeCost_trWhitePolicy_sub_trTailGain_lt`), with the shapes
`CollatzPosDens.TrDirectCertificate.dfltNine` and `CollatzPosDens.TrDirectCertificate.excNine`.
For the accepted cell `(1, 0)` of the default shape and each odd residue `35 ≤ ρ < 64`, and for
the accepted cell `(1, 1)` and each odd residue `ρ ≤ 3`, the check
`CollatzPosDens.TrDirectCertificate.cellCheck` of all odd `m < 2^{12}` with `m ≡ ρ (mod 64)`
whose shape contains that cell is carried out by the kernel, in its own declaration.

## References

* [Mazur, *Collatz positive density*], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrDirectCertificate

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 35 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_35 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 35 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 37 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_37 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 37 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 39 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_39 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 39 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 41 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_41 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 41 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 43 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_43 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 43 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 45 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_45 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 45 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 47 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_47 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 47 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 49 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_49 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 49 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 51 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_51 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 51 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 53 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_53 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 53 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 55 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_55 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 55 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 57 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_57 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 57 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 59 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_59 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 59 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 61 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_61 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 61 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 0)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 63 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_0_63 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 63 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 1)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 1 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_1_1 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 1 (1, 1) dfltNine excNine) = true := by
  decide +kernel

/-- The cell `(1, 1)` passes `cellCheck` for every odd `m < 2^{12}` with `m ≡ 3 (mod 64)`
whose shape contains it. -/
theorem cellCheck_nine_1_1_3 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 1
      (mList 4 6 3 (1, 1) dfltNine excNine) = true := by
  decide +kernel

end TrDirectCertificate

end CollatzPosDens
