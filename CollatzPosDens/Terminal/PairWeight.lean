/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.AffineIdentity
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Maps.OffsetBound
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.Terminal.SourceWindow
public import CollatzPosDens.Terminal.UnweightedMass

/-!
# The weight of a counted pair

Let `M` be a good seed, `n ≥ 0`, let `X` be admissible for generation `n`, and let `(h, w)` be a
counted pair of `Υ_{n,X}(M)`. Then `ω(h) ω(w) ≤ M / X`.

With `x = src(w, R_h)` and `c = ŵ(h) w`, one has `src(c, M) = x` and `ω(c) = ω(h) ω(w)`, so the
affine identity gives `M = ω(h) ω(w) x + off(c) ≥ ω(h) ω(w) x`. The source window gives
`x ≥ X > 0`, whence `ω(h) ω(w) ≤ M / x ≤ M / X`.

## Main results

* `CollatzPosDens.weight_mul_weight_le_div_of_odd`: the bound, for an odd integer seed
  `M ≥ 16^{b₀}`.
* `CollatzPosDens.GoodSeed.weight_mul_weight_le_div`: the bound, for a good seed.

## Implementation notes

Of the good-seed conditions, the argument uses only that `M` is odd with `M ≥ 16^{b₀}` (through
the source window); the general statement is recorded under these hypotheses. Nonnegativity of
the offset holds for every word, so the nonemptiness of `w` is not needed. The weight `ω(h)` of
a history is the weight of its concatenated word `ŵ(h)`. The bound is stated in `ℝ`, where the
scale `X` lives.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {X : ℝ}

/-- **Weight of a counted pair**, for an odd integer seed `M ≥ 16^{b₀}`: if `X` is admissible
for generation `n` and `(h, w)` is a counted pair of `Υ_{n,X}(M)`, then `ω(h) ω(w) ≤ M / X`. -/
theorem weight_mul_weight_le_div_of_odd {M : ℤ} (hodd : Odd M) (hM : 16 ^ scale 0 ≤ M)
    (hX : IsAdmissibleScale M n X) {h : Fin n → Word} {w : Word}
    (hp : (h, w) ∈ unweightedMassPairs n X M) :
    ((concatWord h).weight : ℝ) * (w.weight : ℝ) ≤ (M : ℝ) / X := by
  obtain ⟨z, hz⟩ := exists_intCast_src_of_mem_unweightedMassPairs hp
  have hzX : X ≤ (z : ℝ) :=
    (sources_subset_Ico_of_odd hodd hM hX ⟨z, src_mem_sources hp hz, rfl⟩).1
  have hXpos : 0 < X := hX.pos
  have haff := eq_weight_mul_src_add_off (concatWord h ++ w) (M : ℚ)
  rw [src_append, ← historyEndpoint_eq_src, hz, Word.weight_append] at haff
  have hMq : (concatWord h).weight * w.weight * (z : ℚ) ≤ M := by
    linarith [off_nonneg (concatWord h ++ w)]
  have hMr : ((concatWord h).weight : ℝ) * (w.weight : ℝ) * (z : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hMq
  have hω : (0 : ℝ) ≤ ((concatWord h).weight : ℝ) * (w.weight : ℝ) := by
    have := Word.weight_pos (concatWord h); have := Word.weight_pos w
    positivity
  rw [le_div_iff₀ hXpos]
  exact (mul_le_mul_of_nonneg_left hzX hω).trans hMr

/-- **Weight of a counted pair.** Let `M` be a good seed, let `X` be admissible for generation
`n`, and let `(h, w)` be a counted pair of `Υ_{n,X}(M)`. Then `ω(h) ω(w) ≤ M / X`. -/
@[collatz_pos_dens "lem_s06_pair_weight"]
theorem GoodSeed.weight_mul_weight_le_div {M : ℕ} (hM : GoodSeed M)
    (hX : IsAdmissibleScale M n X) {h : Fin n → Word} {w : Word}
    (hp : (h, w) ∈ unweightedMassPairs n X M) :
    ((concatWord h).weight : ℝ) * (w.weight : ℝ) ≤ (M : ℝ) / X := by
  have := weight_mul_weight_le_div_of_odd (M := (M : ℤ)) (n := n) (X := X)
    (by exact_mod_cast hM.odd) (by exact_mod_cast hM.lower.le)
  simp only [Int.cast_natCast] at this
  exact this hX hp

end CollatzPosDens
