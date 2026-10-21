/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Seed.S05JointCertExistsG

/-!
# The offset-law table of the joint certificate: kernel check of the indices 4608 to 6198

The checker `CollatzPosDens.jointCertGCheckAt` of the offset-law table holds at the indices
`4608 ≤ k ≤ 6198`, in ranges of at most `128` indices, each evaluated by the kernel.

## Main results

* `CollatzPosDens.jointCertGRangeOK_4608`: the indices `4608` to `5119`.
* `CollatzPosDens.jointCertGRangeOK_5120`: the indices `5120` to `5631`.
* `CollatzPosDens.jointCertGRangeOK_5632`: the indices `5632` to `6198`.

## References

* [Mazur, *Collatz positive density*], §16.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The offset-law table passes the checker at the indices `4608` to `5119`. -/
theorem jointCertGRangeOK_4608 : JointCertGRangeOK 4608 5120 :=
  ((((jointCertGRangeOK_of_checkRange (lo := 4608) (n := 128) (by decide +kernel)).trans
    (jointCertGRangeOK_of_checkRange (lo := 4736) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 4864) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 4992) (n := 128) (by decide +kernel)))

/-- The offset-law table passes the checker at the indices `5120` to `5631`. -/
theorem jointCertGRangeOK_5120 : JointCertGRangeOK 5120 5632 :=
  ((((jointCertGRangeOK_of_checkRange (lo := 5120) (n := 128) (by decide +kernel)).trans
    (jointCertGRangeOK_of_checkRange (lo := 5248) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 5376) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 5504) (n := 128) (by decide +kernel)))

/-- The offset-law table passes the checker at the indices `5632` to `6198`. -/
theorem jointCertGRangeOK_5632 : JointCertGRangeOK 5632 6199 :=
  (((((jointCertGRangeOK_of_checkRange (lo := 5632) (n := 128) (by decide +kernel)).trans
    (jointCertGRangeOK_of_checkRange (lo := 5760) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 5888) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 6016) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 6144) (n := 55) (by decide +kernel)))

end CollatzPosDens
