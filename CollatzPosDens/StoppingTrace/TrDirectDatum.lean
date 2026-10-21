/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrTreeDatum
public import CollatzPosDens.StoppingTrace.TrWhitePolicy

/-!
# The direct positive policies form tree data

For `ω, p ∈ ℕ`, an integer `m` and reals `a`, `b`, the pair `(8, W^{ω,8,ω+p}_{m,a,b})` of the
constant cutoff `8` and the white-test policy `W^{ω,8,ω+p}_{m,a,b}` is a tree datum of height
`ω + p + 8`. Indeed `W = W^{ω,8,ω+p}_{m,a,b}` is a bounded policy whose triples `(r, h, c)` have
`2 ≤ c ≤ 8` and `h + c ≤ ω + p`, so (i) `c ≤ 8`; (ii) `8 ≤ 16` and `8 ≤ ω + p + 8`; and
(iii) `8 ≤ 16` and `h + c + 8 ≤ ω + p + 8`.

The direct positive policies are those with `(ω, p)` among `(1, 4)`, `(6, 4)`, `(9, 4)`,
`(13, 1)`, `(16, 1)`, with `a ≤ b`; the construction needs neither restriction.

## Main definitions

* `CollatzPosDens.trDirectDatum ω p m a b`: the tree datum `(8, W^{ω,8,ω+p}_{m,a,b})` of height
  `ω + p + 8`.

## Main results

* `CollatzPosDens.exists_trDirectDatum`: `(8, W^{ω,8,ω+p}_{m,a,b})` is a tree datum of height
  `ω + p + 8`, for all `ω, p ∈ ℕ`, `m ∈ ℤ` and reals `a`, `b`.

## Implementation notes

A tree datum is data (`CollatzPosDens.TreeDatum`), so "the pair `(8, W)` is a tree datum of
height `H`" is stated as the existence of a `TreeDatum H` with cutoff `fun _ => 8` and policy
`W`. The statement holds for every pair `(ω, p)` and all reals `a`, `b`, and is stated so.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The tree datum `(8, W^{ω,8,ω+p}_{m,a,b})` of height `ω + p + 8`: the constant cutoff `8`
and the white-test policy `W^{ω,8,ω+p}_{m,a,b}`. -/
noncomputable def trDirectDatum (ω p : ℕ) (m : ℤ) (a b : ℝ) : TreeDatum (ω + p + 8) where
  cut _ := 8
  W := trWhitePolicy ω 8 (ω + p : ℕ) m a b
  isBoundedPolicy := isBoundedPolicy_trWhitePolicy _ _ _ _ _ _
  le_cut q hq := by
    have := le_of_mem_trWhitePolicy hq
    omega
  cut_zero_le_sixteen := by norm_num
  cut_zero_le := by omega
  cut_add_le_sixteen _ _ := by norm_num
  add_add_cut_le q hq := by
    have := add_le_of_mem_trWhitePolicy hq
    omega

/-- The cutoff of `trDirectDatum` is the constant `8`. -/
@[simp]
theorem trDirectDatum_cut (ω p : ℕ) (m : ℤ) (a b : ℝ) :
    (trDirectDatum ω p m a b).cut = fun _ => 8 := rfl

/-- The policy of `trDirectDatum` is the white-test policy `W^{ω,8,ω+p}_{m,a,b}`. -/
@[simp]
theorem trDirectDatum_W (ω p : ℕ) (m : ℤ) (a b : ℝ) :
    (trDirectDatum ω p m a b).W = trWhitePolicy ω 8 (ω + p : ℕ) m a b := rfl

/-- For all `ω, p ∈ ℕ`, every integer `m` and all reals `a`, `b`, the pair
`(8, W^{ω,8,ω+p}_{m,a,b})` is a tree datum of height `ω + p + 8`. In particular this holds for
the direct positive pairs `(ω, p) ∈ {(1, 4), (6, 4), (9, 4), (13, 1), (16, 1)}` and `a ≤ b`. -/
@[collatz_pos_dens "lem_tr_direct_datum"]
theorem exists_trDirectDatum (ω p : ℕ) (m : ℤ) (a b : ℝ) :
    ∃ D : TreeDatum (ω + p + 8),
      D.cut = (fun _ => 8) ∧ D.W = trWhitePolicy ω 8 (ω + p : ℕ) m a b :=
  ⟨trDirectDatum ω p m a b, rfl, rfl⟩

end CollatzPosDens
