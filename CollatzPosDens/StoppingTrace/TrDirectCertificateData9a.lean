/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDirectCertificateSound

/-!
# The direct-entry certificate at `ω = 9`: the cell `(1, 0)`, residues `1` to `33` modulo `64`

This file checks cells of the direct-entry certificate for the pair `(ω, p) = (9, 4)`
(see `CollatzPosDens.exists_trTreeCost_trWhitePolicy_sub_trTailGain_lt`). Every odd `m < 2^{12}`
is given a bisection shape (`CollatzPosDens.TrDirectCertificate.Shape`) of `[-1/3, 1/3]`: by
default the two halves of `[-1/3, 1/3]`, and for the 16 values of `m` listed in
`CollatzPosDens.TrDirectCertificate.excNine` a finer one. For each accepted cell `(D, k)` of the
default shape and each residue class of `m` modulo `64`, and for each other accepted cell, the
check `CollatzPosDens.TrDirectCertificate.cellCheck` of all the `m` concerned is carried out by
the kernel, in its own declaration.

## References

* [Mazur, *Collatz positive density*], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrDirectCertificate

/-- The default shape for `ω = 9`. -/
def dfltNine : Shape := (.node .leaf .leaf)

/-- The odd `m < 2^{12}` whose shape is not the default one, with their shapes. -/
def excNine : List (ℕ × Shape) := [(151, (.node .leaf (.node .leaf .leaf))),
    (361, (.node (.node .leaf .leaf) .leaf)), (663, (.node .leaf (.node .leaf .leaf))),
    (873, (.node (.node .leaf .leaf) .leaf)), (1175, (.node .leaf (.node .leaf .leaf))),
    (1385, (.node (.node .leaf .leaf) .leaf)), (1687, (.node .leaf (.node .leaf .leaf))),
    (1897, (.node (.node .leaf .leaf) .leaf)), (2199, (.node .leaf (.node .leaf .leaf))),
    (2409, (.node (.node .leaf .leaf) .leaf)), (2711, (.node .leaf (.node .leaf .leaf))),
    (2921, (.node (.node .leaf .leaf) .leaf)), (3223, (.node .leaf (.node .leaf .leaf))),
    (3433, (.node (.node .leaf .leaf) .leaf)), (3735, (.node .leaf (.node .leaf .leaf))),
    (3945, (.node (.node .leaf .leaf) .leaf))]

/-- The shape of `m` for `ω = 9`. -/
def shapeNine (m : ℕ) : Shape := shapeOf dfltNine excNine m

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 1 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_1 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 1 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 3 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_3 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 3 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 5 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_5 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 5 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 7 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_7 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 7 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 9 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_9 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 9 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 11 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_11 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 11 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 13 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_13 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 13 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 15 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_15 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 15 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 17 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_17 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 17 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 19 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_19 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 19 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 21 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_21 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 21 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 23 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_23 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 23 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 25 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_25 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 25 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 27 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_27 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 27 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 29 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_29 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 29 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 31 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_31 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 31 (1, 0) dfltNine excNine) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` for `ω = 9` holds for every odd `m < 2^{12}` with
`m ≡ 33 (mod 64)` whose shape has this cell. -/
theorem cellCheck_nine_1_0_33 :
    cellCheck 9 4 800801 204800000 29899046684530910365 1 0
      (mList 4 6 33 (1, 0) dfltNine excNine) = true := by
  decide +kernel

end TrDirectCertificate

end CollatzPosDens
