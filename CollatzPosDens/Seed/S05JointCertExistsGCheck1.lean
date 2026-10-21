/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Seed.S05JointCertExistsG

/-!
# Kernel check of the offset-law table at the indices 0 to 1535

The checker `CollatzPosDens.jointCertGCheckAt` of the offset-law table holds at the indices
`0 ≤ k ≤ 1535`, in ranges of at most `128` indices, each evaluated by the kernel.

## Main results

* `CollatzPosDens.jointCertGRangeOK_0`: the checker holds at the indices `0` to `511`.
* `CollatzPosDens.jointCertGRangeOK_512`: the checker holds at the indices `512` to `1023`.
* `CollatzPosDens.jointCertGRangeOK_1024`: the checker holds at the indices `1024` to `1535`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The offset-law table passes the checker at the indices `0` to `511`. -/
theorem jointCertGRangeOK_0 : JointCertGRangeOK 0 512 :=
  ((((jointCertGRangeOK_of_checkRange (lo := 0) (n := 128) (by decide +kernel)).trans
    (jointCertGRangeOK_of_checkRange (lo := 128) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 256) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 384) (n := 128) (by decide +kernel)))

/-- The offset-law table passes the checker at the indices `512` to `1023`. -/
theorem jointCertGRangeOK_512 : JointCertGRangeOK 512 1024 :=
  ((((jointCertGRangeOK_of_checkRange (lo := 512) (n := 128) (by decide +kernel)).trans
    (jointCertGRangeOK_of_checkRange (lo := 640) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 768) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 896) (n := 128) (by decide +kernel)))

/-- The offset-law table passes the checker at the indices `1024` to `1535`. -/
theorem jointCertGRangeOK_1024 : JointCertGRangeOK 1024 1536 :=
  ((((jointCertGRangeOK_of_checkRange (lo := 1024) (n := 128) (by decide +kernel)).trans
    (jointCertGRangeOK_of_checkRange (lo := 1152) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 1280) (n := 128) (by decide +kernel))).trans
    (jointCertGRangeOK_of_checkRange (lo := 1408) (n := 128) (by decide +kernel)))

end CollatzPosDens
