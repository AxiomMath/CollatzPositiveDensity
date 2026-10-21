/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Seed.S05JointCertExistsG

/-!
# The offset-law table of the joint certificate: kernel check of the indices 1536 to 3071

The checker `CollatzPosDens.jointCertGCheckAt` of the offset-law table holds at the indices
`1536 ≤ k ≤ 3071`, in ranges of at most `128` indices, each evaluated by the kernel.

## Main results

* `CollatzPosDens.jointCertGRangeOK_1536`: the indices `1536` to `2047`.
* `CollatzPosDens.jointCertGRangeOK_2048`: the indices `2048` to `2559`.
* `CollatzPosDens.jointCertGRangeOK_2560`: the indices `2560` to `3071`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The offset-law table passes the checker at the indices `1536` to `2047`. -/
theorem jointCertGRangeOK_1536 : JointCertGRangeOK 1536 2048 :=
  ((((jointCertGRangeOK_of_checkRange (lo := 1536) (n := 128) (by decide +kernel)).trans
    (jointCertGRangeOK_of_checkRange (lo := 1664) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 1792) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 1920) (n := 128) (by decide +kernel)))

/-- The offset-law table passes the checker at the indices `2048` to `2559`. -/
theorem jointCertGRangeOK_2048 : JointCertGRangeOK 2048 2560 :=
  ((((jointCertGRangeOK_of_checkRange (lo := 2048) (n := 128) (by decide +kernel)).trans
    (jointCertGRangeOK_of_checkRange (lo := 2176) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 2304) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 2432) (n := 128) (by decide +kernel)))

/-- The offset-law table passes the checker at the indices `2560` to `3071`. -/
theorem jointCertGRangeOK_2560 : JointCertGRangeOK 2560 3072 :=
  ((((jointCertGRangeOK_of_checkRange (lo := 2560) (n := 128) (by decide +kernel)).trans
    (jointCertGRangeOK_of_checkRange (lo := 2688) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 2816) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 2944) (n := 128) (by decide +kernel)))

end CollatzPosDens
