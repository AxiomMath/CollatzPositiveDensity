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
public import CollatzPosDens.Mixing.MxHeadWindow
public import CollatzPosDens.Transfer.Log3Bounds

/-!
# The good words are covered by the slice gates

Every good word lies in the gate union: `Gd_n ⊆ 𝒰_n`.

Let `w ∈ Gd_n` and let `i` be an index witnessing goodness. With `k = i - 1`, `h = w_{≤ i}`
and `l = A(h)`, the four conditions of the head gate `Hd(n, k, l)` hold: the window
condition and the crossing `A(h_{≤ k}) ≤ Lv_n < A(h) = l` and the overshoot bound are those
of `Gd_n`, and `off(h) ≤ off(w) ≤ n^{4609/4096}` because the offset of a prefix is a partial
sum of the nonnegative terms whose total is `off(w)`. So `w ∈ Sl(n, k, l)` with `k < n`, and
the head window together with `log₂ 3 ≤ 317/200` gives `l < n log₂ 3 < 2n`.

## Main results

* `CollatzPosDens.mxGood_subset_mxGateUnion`: `Gd_n ⊆ 𝒰_n`.

## Implementation notes

The source assumes `n ≥ 2^{131072}`; the argument uses only `log₂ n ≥ 0`, which holds for
every natural number `n` (with `log₂ 0 = 0`), so the inclusion is stated for every `n`.
The monotonicity of the offset under taking prefixes is derived from the concatenation
formula `off(uv) = off(u) + 3^{|u|} 2^{-A(u)} off(v)` and `off(v) ≥ 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Gate cover.** Every good word lies in the gate union: `Gd_n ⊆ 𝒰_n`. -/
@[collatz_pos_dens "lem_mx_gate_cover"]
theorem mxGood_subset_mxGateUnion (n : ℕ) : mxGood n ⊆ mxGateUnion n := by
  intro w hw
  obtain ⟨hlen, hoff, i, hi1, hin, ⟨hlo, hhi⟩, hle, hlt, hover⟩ := mem_mxGood.mp hw
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hhead : w.take (k + 1) ∈ mxHeadGate n k (Word.valSum (w.take (k + 1))) := by
    refine mem_mxHeadGate.mpr ⟨?_, ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩,
      ⟨?_, hlt, rfl⟩, hover, ?_⟩
    · rw [List.length_take, hlen]
      omega
    · rw [List.take_take, min_eq_left (Nat.le_succ k)]
      simpa using hle
    · refine le_trans ?_ hoff
      exact_mod_cast off_take_le w (k + 1)
  refine mem_mxGateUnion.mpr ⟨k, by omega, _, ?_, hlen, hhead⟩
  have hwin := mxHeadGate_add_logb_lt hhead
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  have hlog3 := logb_two_three_bounds.2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : (Word.valSum (w.take (k + 1)) : ℝ) < 2 * n := by nlinarith
  exact_mod_cast this

end CollatzPosDens
