/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDirectCertificateData1
public import CollatzPosDens.StoppingTrace.TrDirectCertificateData6
public import CollatzPosDens.StoppingTrace.TrDirectCertificateData9
public import CollatzPosDens.StoppingTrace.TrDirectCertificateData13
public import CollatzPosDens.StoppingTrace.TrDirectCertificateData16
public import CollatzPosDens.StoppingTrace.TrDirectDatum

/-!
# The direct-entry certificate

For every pair `(ω, p)` among `(1, 4)`, `(6, 4)`, `(9, 4)`, `(13, 1)`, `(16, 1)`, every odd
integer `m` with `0 < m < 2^{p+8}` and every real `β` with `|β| ≤ 1/3`, there are reals `a ≤ β ≤ b`
in `[-1/3, 1/3]` such that
`F^{8,W}_{0,0}(2^ω m + β) - T^{root}_{ω,8} < 77/100`, where `F` is the tree cost
`CollatzPosDens.trTreeCost` with the constant cutoff `8`, `W = W^{ω,8,ω+p}_{m,a,b}` is the
white-test policy `CollatzPosDens.trWhitePolicy` (so that `(8, W)` is the tree datum
`CollatzPosDens.trDirectDatum`), and `T^{root}_{ω,8}` is the root packet correction
`CollatzPosDens.trTailGain`.

The proof is a finite computation. A cell `[a, b] ⊆ [-1/3, 1/3]` has centre `u` and half-width
`δ`. For a cell, the Lipschitz bound `CollatzPosDens.abs_trTreeCost_sub_le` gives
`F^{8,W}_{0,0}(2^ω m + β) ≤ F^{8,W}_{0,0}(2^ω m + u) + L δ`, where `L` bounds the Lipschitz
constant `CollatzPosDens.trTreeLip` of the policy of all triples `(r, h, c)` with `2 ≤ c ≤ 8` and
`h + c ≤ ω + p`, which contains `W` (`CollatzPosDens.trTreeLip_mono`). The value at the centre is
bounded state by state by the one-node bound `CollatzPosDens.trTreeCost_le_of_node_bound`, each
capped factor `Φ^cap_c` at a rational point being bounded through its pair sum
(`CollatzPosDens.trCapFactor_le_of_pairSum_le`) and the cosine bound on a quarter turn
(`CollatzPosDens.abs_cos_two_pi_sub_cosTaylorSum_le`), in natural-number arithmetic on the scale
`2^64` (`CollatzPosDens.TrDirectCertificate.cellCheck`).

For each `m` the cells start from `[-1/3, 1/3]` if `ω = 1`, from its two halves if `ω ∈ {6, 9}`
and from its four quarters if `ω ∈ {13, 16}`; a cell that is not accepted is replaced by its two
halves, which happens for `136`, `16` and `16` values of `m` when `ω` is `1`, `9` and `16`. The
least margin of an accepted cell below `77/100 + T^{root}_{ω,8}` is about `1.39 · 10^{-5}` (at
`ω = 16`). The entries at the points `9^r (2^ω m + u) / 2^n` depend on `m` only modulo
`2^{n-ω}`; they are computed once for each residue class, along a recursion that splits the
values of `m` bit by bit. The checks are carried out by the kernel, in one declaration for each
pair, each accepted cell and each residue class of `m`
(`CollatzPosDens.TrDirectCertificate.cellGood_one` and its analogues for the other pairs).

## Main results

* `CollatzPosDens.exists_trTreeCost_trWhitePolicy_sub_trTailGain_lt`: the direct-entry
  certificate.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open TrDirectCertificate

/-- **The direct-entry certificate.** For every pair `(ω, p)` among `(1, 4)`, `(6, 4)`,
`(9, 4)`, `(13, 1)`, `(16, 1)`, every odd integer `m` with `0 < m < 2^{p+8}` and every real `β`
with `|β| ≤ 1/3`, there are reals `a, b` with `-1/3 ≤ a ≤ β ≤ b ≤ 1/3` such that
`F^{8,W^{ω,8,ω+p}_{m,a,b}}_{0,0}(2^ω m + β) - T^{root}_{ω,8} < 77/100`. -/
@[collatz_pos_dens "lem_tr_direct_certificate"]
theorem exists_trTreeCost_trWhitePolicy_sub_trTailGain_lt {ω p : ℕ}
    (hωp : (ω, p) ∈ [(1, 4), (6, 4), (9, 4), (13, 1), (16, 1)]) {m : ℤ} (hm : Odd m)
    (hm0 : 0 < m) (hm1 : m < 2 ^ (p + 8)) {β : ℝ} (hβ : |β| ≤ 1 / 3) :
    ∃ a b : ℝ, -1 / 3 ≤ a ∧ a ≤ β ∧ β ≤ b ∧ b ≤ 1 / 3 ∧
      trTreeCost (fun _ => 8) (trWhitePolicy ω 8 (ω + p : ℕ) m a b) 0 0 (2 ^ ω * m + β) -
        trTailGain ω 8 < 77 / 100 := by
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hωp
  rcases hωp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact exists_of_cellGood shapeOne cellGood_one hm hm0 hm1 hβ
  · exact exists_of_cellGood shapeSix cellGood_six hm hm0 hm1 hβ
  · exact exists_of_cellGood shapeNine cellGood_nine hm hm0 hm1 hβ
  · exact exists_of_cellGood shapeThirteen cellGood_thirteen hm hm0 hm1 hβ
  · exact exists_of_cellGood shapeSixteen cellGood_sixteen hm hm0 hm1 hβ

end CollatzPosDens
