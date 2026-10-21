/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShFreshWord
public import CollatzPosDens.Mixing.MxShPartialSumsOffset

/-!
# The binary-clock offset identity

Let `N ∈ ℕ` and `w` a word with `d = |Ex_N(w)| < |w|`. The offset of `w` splits at the clock
position `N` into the offset of the exposed pattern and a rescaled offset of the fresh word:
$$\mathrm{off}(w) = \operatorname{Of}(\mathrm{Ex}_N(w)) + 3^{d}\, 2^{-N}\,
  \mathrm{off}(\mathrm{Fr}_N(w)).$$
Writing `w = u a r` with `A(u) ≤ N < A(u) + a`, one has `Ex_N(w) = Pt(u)`, whose offset is
`off(u)`, and `Fr_N(w) = (A(u) + a - N, r)`; the identity is then the concatenation rule
`off(u v) = off(u) + 3^{|u|} 2^{-A(u)} off(v)` together with `2^{-A(u)} 2^{-a} = 2^{-N}
2^{-(A(u) + a - N)}`.

## Main results

* `CollatzPosDens.Word.off_eq_setOffset_exposedPattern_add`: the binary-clock offset identity.

## Implementation notes

The identity is also the splitting `CollatzPosDens.setOffset_eq_add` of the set offset at
`q = N`, applied to `S = Pt(w)`; the proof here uses instead the concatenation rule
`CollatzPosDens.off_append` for the word offset at the decomposition `w = u a r`, which avoids
describing `Pt(Fr_N(w))`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace Word

open Finset

/-- **The binary-clock offset identity.** If `|Ex_N(w)| < |w|`, then
`off(w) = Of(Ex_N(w)) + 3^{|Ex_N(w)|} 2^{-N} off(Fr_N(w))`. -/
@[collatz_pos_dens "lem_mx_sh_clock_offset"]
theorem off_eq_setOffset_exposedPattern_add {N : ℕ} {w : Word}
    (h : #(exposedPattern N w) < w.length) :
    off w = setOffset (exposedPattern N w) +
      (3 : ℚ) ^ #(exposedPattern N w) * ((2 : ℚ) ^ N)⁻¹ * off (fresh N w) := by
  obtain ⟨u, a, r, rfl, hu, ha⟩ := exists_eq_append_cons_of_card_exposedPattern_lt h
  rw [fresh_append_cons r hu ha, exposedPattern_append_cons r hu ha, card_partialSums,
    ← off_eq_setOffset_partialSums, off_append, off_cons, off_cons, coe_toPNat'_valSum_add_sub ha,
    weight]
  obtain ⟨e, he⟩ : ∃ e, valSum u + a = N + e := ⟨valSum u + a - N, by omega⟩
  have hpow : ((2 : ℚ) ^ valSum u)⁻¹ * ((2 : ℚ) ^ (a : ℕ))⁻¹ =
      ((2 : ℚ) ^ N)⁻¹ * ((2 : ℚ) ^ (valSum u + a - N))⁻¹ := by
    rw [← mul_inv, ← mul_inv, ← pow_add, ← pow_add, he, Nat.add_sub_cancel_left]
  rw [div_eq_mul_inv, mul_assoc _ ((2 : ℚ) ^ valSum u)⁻¹, ← mul_assoc ((2 : ℚ) ^ valSum u)⁻¹,
    hpow, mul_assoc _ ((2 : ℚ) ^ N)⁻¹, mul_assoc ((2 : ℚ) ^ N)⁻¹]

end Word

end CollatzPosDens
