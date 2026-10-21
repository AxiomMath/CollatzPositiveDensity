/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrTreeDatum
public import CollatzPosDens.StoppingTrace.TrWhitePolicy
public import CollatzPosDens.StoppingTrace.TrZeroCutoff

/-!
# The gap-zero policies form tree data

For every integer `m` and all reals `a`, `b`, the pair `(cut⁰, W^{0,12,14}_{m,a,b})` of the
gap-zero cutoff `cut⁰(h) = min {12, 17 - h}` and the white-test policy `W^{0,12,14}_{m,a,b}` is a
tree datum of height `17`.

Every triple `(r, h, c)` of `W^{0,12,14}_{m,a,b}` has `2 ≤ c ≤ 12` and `h + c ≤ 14`. Hence
`c ≤ min {12, 14 - h} ≤ cut⁰(h)`; at the root `cut⁰(0) = 12 ≤ 16, 17`; and since
`h + c ≤ 14 ≤ 17`, the reached depth `h + c` has `cut⁰(h + c) ≤ 12 ≤ 16` and
`h + c + cut⁰(h + c) ≤ 17`.

## Main definitions

* `CollatzPosDens.trZeroDatum m a b`: the tree datum `(cut⁰, W^{0,12,14}_{m,a,b})` of height `17`.

## Main results

* `CollatzPosDens.trZeroDatum_cut`, `CollatzPosDens.trZeroDatum_W`: its cutoff is `cut⁰` and its
  policy is `W^{0,12,14}_{m,a,b}`.

## Implementation notes

A tree datum is a structure carrying its cutoff and policy, so the statement that
`(cut⁰, W^{0,12,14}_{m,a,b})` is a tree datum of height `17` is the construction
`CollatzPosDens.trZeroDatum` together with the two `rfl` lemmas identifying its fields. No
hypothesis `a ≤ b` is needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every integer `m` and all reals `a`, `b`, the pair `(cut⁰, W^{0,12,14}_{m,a,b})` is a
tree datum of height `17`. -/
@[collatz_pos_dens "lem_tr_zero_datum"]
noncomputable def trZeroDatum (m : ℤ) (a b : ℝ) : TreeDatum 17 where
  cut := trZeroCutoff
  W := trWhitePolicy 0 12 14 m a b
  isBoundedPolicy := isBoundedPolicy_trWhitePolicy 0 12 14 m a b
  le_cut p hp := by
    have h1 := le_of_mem_trWhitePolicy hp
    have h2 := add_le_of_mem_trWhitePolicy hp
    rw [trZeroCutoff_eq_min]
    omega
  cut_zero_le_sixteen := by decide
  cut_zero_le := by decide
  cut_add_le_sixteen p _ := (trZeroCutoff_le_twelve _).trans (by norm_num)
  add_add_cut_le p hp := by
    have h2 := add_le_of_mem_trWhitePolicy hp
    exact add_trZeroCutoff_le_seventeen (by omega)

/-- The cutoff of `trZeroDatum m a b` is `trZeroCutoff`. -/
@[simp]
theorem trZeroDatum_cut (m : ℤ) (a b : ℝ) : (trZeroDatum m a b).cut = trZeroCutoff := rfl

/-- The policy of `trZeroDatum m a b` is `trWhitePolicy 0 12 14 m a b`. -/
@[simp]
theorem trZeroDatum_W (m : ℤ) (a b : ℝ) :
    (trZeroDatum m a b).W = trWhitePolicy 0 12 14 m a b := rfl

end CollatzPosDens
