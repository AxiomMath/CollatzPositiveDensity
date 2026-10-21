/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Seed.S05JointCertExistsG

/-!
# The offset-law table of the joint certificate: kernel check of the indices 3072 to 4607

The checker `CollatzPosDens.jointCertGCheckAt` of the offset-law table holds at the indices
`3072 ≤ k ≤ 4607`, in ranges of at most `128` indices, each evaluated by the kernel.

## Main results

* `CollatzPosDens.jointCertGRangeOK_3072`: the indices `3072` to `3583`.
* `CollatzPosDens.jointCertGRangeOK_3584`: the indices `3584` to `4095`.
* `CollatzPosDens.jointCertGRangeOK_4096`: the indices `4096` to `4607`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The offset-law table passes the checker at the indices `3072` to `3583`. -/
theorem jointCertGRangeOK_3072 : JointCertGRangeOK 3072 3584 :=
  ((((jointCertGRangeOK_of_checkRange (lo := 3072) (n := 128) (by decide +kernel)).trans
    (jointCertGRangeOK_of_checkRange (lo := 3200) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 3328) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 3456) (n := 128) (by decide +kernel)))

/-- The offset-law table passes the checker at the indices `3584` to `4095`. -/
theorem jointCertGRangeOK_3584 : JointCertGRangeOK 3584 4096 :=
  ((((jointCertGRangeOK_of_checkRange (lo := 3584) (n := 128) (by decide +kernel)).trans
    (jointCertGRangeOK_of_checkRange (lo := 3712) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 3840) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 3968) (n := 128) (by decide +kernel)))

/-- The offset-law table passes the checker at the indices `4096` to `4607`. -/
theorem jointCertGRangeOK_4096 : JointCertGRangeOK 4096 4608 :=
  ((((jointCertGRangeOK_of_checkRange (lo := 4096) (n := 128) (by decide +kernel)).trans
    (jointCertGRangeOK_of_checkRange (lo := 4224) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 4352) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 4480) (n := 128) (by decide +kernel)))

end CollatzPosDens
