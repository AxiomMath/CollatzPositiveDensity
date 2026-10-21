/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDirectCertificateData6a

/-!
# The direct-entry certificate at `ω = 6`, continued

This file checks cells of the direct-entry certificate for the pair `(ω, p) = (6, 4)`
(see `CollatzPosDens.exists_trTreeCost_trWhitePolicy_sub_trTailGain_lt`). Every odd `m < 2^{12}`
is given the bisection shape (`CollatzPosDens.TrDirectCertificate.Shape`) of `[-1/3, 1/3]` into
its two halves, the list `CollatzPosDens.TrDirectCertificate.excSix` of exceptions being empty.
For each accepted cell `(D, k)` and each residue class of `m` modulo `64`, the check
`CollatzPosDens.TrDirectCertificate.cellCheck` of all the `m` concerned is carried out by the
kernel, in its own declaration.

## References

* [Mazur, *Collatz positive density*], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrDirectCertificate

/-- The check `cellCheck` of the cell `(1, 0)` holds for every odd `m < 2^{12}` with
`m ≡ 45 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_0_45 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 45 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 0)` holds for every odd `m < 2^{12}` with
`m ≡ 47 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_0_47 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 47 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 0)` holds for every odd `m < 2^{12}` with
`m ≡ 49 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_0_49 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 49 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 0)` holds for every odd `m < 2^{12}` with
`m ≡ 51 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_0_51 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 51 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 0)` holds for every odd `m < 2^{12}` with
`m ≡ 53 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_0_53 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 53 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 0)` holds for every odd `m < 2^{12}` with
`m ≡ 55 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_0_55 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 55 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 0)` holds for every odd `m < 2^{12}` with
`m ≡ 57 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_0_57 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 57 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 0)` holds for every odd `m < 2^{12}` with
`m ≡ 59 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_0_59 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 59 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 0)` holds for every odd `m < 2^{12}` with
`m ≡ 61 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_0_61 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 61 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 0)` holds for every odd `m < 2^{12}` with
`m ≡ 63 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_0_63 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 63 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 1)` holds for every odd `m < 2^{12}` with
`m ≡ 1 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_1_1 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 1 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 1)` holds for every odd `m < 2^{12}` with
`m ≡ 3 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_1_3 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 3 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 1)` holds for every odd `m < 2^{12}` with
`m ≡ 5 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_1_5 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 5 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 1)` holds for every odd `m < 2^{12}` with
`m ≡ 7 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_1_7 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 7 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 1)` holds for every odd `m < 2^{12}` with
`m ≡ 9 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_1_9 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 9 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 1)` holds for every odd `m < 2^{12}` with
`m ≡ 11 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_1_11 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 11 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 1)` holds for every odd `m < 2^{12}` with
`m ≡ 13 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_1_13 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 13 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 1)` holds for every odd `m < 2^{12}` with
`m ≡ 15 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_1_15 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 15 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 1)` holds for every odd `m < 2^{12}` with
`m ≡ 17 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_1_17 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 17 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 1)` holds for every odd `m < 2^{12}` with
`m ≡ 19 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_1_19 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 19 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(1, 1)` holds for every odd `m < 2^{12}` with
`m ≡ 21 (mod 64)` whose shape for `ω = 6` has this cell. -/
theorem cellCheck_six_1_1_21 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 21 (1, 1) dfltSix excSix) = true := by
  decide +kernel

end TrDirectCertificate

end CollatzPosDens
