/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Mixing.MxGood
public import CollatzPosDens.Mixing.MxHeadGate
public import CollatzPosDens.Mixing.MxSliceGate
public import CollatzPosDens.Mixing.MxGateUnion
public import CollatzPosDens.Mixing.MxHeadSumBound

/-!
# The good words are covered by the slice gates

For every integer `n ≥ 2^80000`, every good word lies in the gate union: `Gd_n ⊆ 𝒰_n`.

Let `w ∈ Gd_n` and let `i` be an index witnessing goodness. With `k = i - 1`, `h = w_{≤ i}`
and `l = A(h)`, the three conditions of the head gate `Hd(n, k, l)` hold: the window
condition, the crossing `A(h_{≤ k}) ≤ Lv_n < A(h) = l` and the product condition
`2^l off(h) < 3^n` are those of `Gd_n`. So `w ∈ Sl(n, k, l)` with `k < n`, and the bound on
valuation sums of heads gives `l < 4n`.

## Main results

* `CollatzPosDens.mxGood_subset_mxGateUnion`: `Gd_n ⊆ 𝒰_n` for `n ≥ 2^80000`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Gate cover.** For every integer `n ≥ 2^80000`, every good word lies in the gate union:
`Gd_n ⊆ 𝒰_n`. -/
@[collatz_pos_dens "lem_mx_gate_cover"]
theorem mxGood_subset_mxGateUnion {n : ℕ} (hn : 2 ^ 80000 ≤ n) : mxGood n ⊆ mxGateUnion n := by
  intro w hw
  obtain ⟨hlen, i, hi1, hin, ⟨hlo, hhi⟩, hle, hlt, hprod⟩ := mem_mxGood.mp hw
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hhead : w.take (k + 1) ∈ mxHeadGate n k (Word.valSum (w.take (k + 1))) := by
    refine mem_mxHeadGate.mpr ⟨?_, ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩,
      ⟨?_, hlt, rfl⟩, hprod⟩
    · rw [List.length_take, hlen]
      omega
    · rw [List.take_take, min_eq_left (Nat.le_succ k)]
      simpa using hle
  exact mem_mxGateUnion.mpr
    ⟨k, by omega, _, lt_four_mul_of_mem_mxHeadGate hn hhead, hlen, hhead⟩

end CollatzPosDens
