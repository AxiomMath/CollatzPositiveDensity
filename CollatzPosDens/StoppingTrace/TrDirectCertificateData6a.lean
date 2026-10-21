/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDirectCertificateSound

/-!
# The direct-entry certificate at `ω = 6`: the cell `(1, 0)` for `m < 64`

This file checks cells of the direct-entry certificate for the pair `(ω, p) = (6, 4)` (see
`CollatzPosDens.exists_trTreeCost_trWhitePolicy_sub_trTailGain_lt`). Every odd `m < 2^{12}` is
given a bisection shape (`CollatzPosDens.TrDirectCertificate.Shape`) of `[-1/3, 1/3]`: the
default shape `CollatzPosDens.TrDirectCertificate.dfltSix`, the two halves of `[-1/3, 1/3]`,
except for the values of `m` listed in `CollatzPosDens.TrDirectCertificate.excSix`, of which
there are none. For the accepted cell `(1, 0)` of the default shape and each odd residue
`ρ < 44`, the check `CollatzPosDens.TrDirectCertificate.cellCheck` of all odd `m < 2^{12}` with
`m ≡ ρ (mod 64)` is carried out by the kernel, in its own declaration.

## Main definitions

* `CollatzPosDens.TrDirectCertificate.dfltSix`: The default shape for `ω = 6`.
* `CollatzPosDens.TrDirectCertificate.excSix`: The odd `m < 2^{12}` with a non-default shape.
* `CollatzPosDens.TrDirectCertificate.shapeSix`: The shape of `m` for `ω = 6`.

## References

* [Mazur, *Collatz positive density*], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrDirectCertificate

/-- The default shape for `ω = 6`. -/
def dfltSix : Shape := (.node .leaf .leaf)

/-- The odd `m < 2^{12}` whose shape is not the default one, with their shapes. -/
def excSix : List (ℕ × Shape) := []

/-- The shape of `m` for `ω = 6`. -/
def shapeSix (m : ℕ) : Shape := shapeOf dfltSix excSix m

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 1 (mod 64)`. -/
theorem cellCheck_six_1_0_1 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 1 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 3 (mod 64)`. -/
theorem cellCheck_six_1_0_3 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 3 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 5 (mod 64)`. -/
theorem cellCheck_six_1_0_5 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 5 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 7 (mod 64)`. -/
theorem cellCheck_six_1_0_7 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 7 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 9 (mod 64)`. -/
theorem cellCheck_six_1_0_9 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 9 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 11 (mod 64)`. -/
theorem cellCheck_six_1_0_11 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 11 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 13 (mod 64)`. -/
theorem cellCheck_six_1_0_13 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 13 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 15 (mod 64)`. -/
theorem cellCheck_six_1_0_15 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 15 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 17 (mod 64)`. -/
theorem cellCheck_six_1_0_17 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 17 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 19 (mod 64)`. -/
theorem cellCheck_six_1_0_19 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 19 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 21 (mod 64)`. -/
theorem cellCheck_six_1_0_21 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 21 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 23 (mod 64)`. -/
theorem cellCheck_six_1_0_23 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 23 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 25 (mod 64)`. -/
theorem cellCheck_six_1_0_25 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 25 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 27 (mod 64)`. -/
theorem cellCheck_six_1_0_27 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 27 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 29 (mod 64)`. -/
theorem cellCheck_six_1_0_29 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 29 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 31 (mod 64)`. -/
theorem cellCheck_six_1_0_31 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 31 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 33 (mod 64)`. -/
theorem cellCheck_six_1_0_33 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 33 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 35 (mod 64)`. -/
theorem cellCheck_six_1_0_35 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 35 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 37 (mod 64)`. -/
theorem cellCheck_six_1_0_37 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 37 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 39 (mod 64)`. -/
theorem cellCheck_six_1_0_39 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 39 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 41 (mod 64)`. -/
theorem cellCheck_six_1_0_41 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 41 (1, 0) dfltSix excSix) = true := by
  decide +kernel

/-- The cell `(1, 0)` of the default shape passes `cellCheck` for every odd `m < 2^{12}`
with `m ≡ 43 (mod 64)`. -/
theorem cellCheck_six_1_0_43 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 0
      (mList 4 6 43 (1, 0) dfltSix excSix) = true := by
  decide +kernel

end TrDirectCertificate

end CollatzPosDens
