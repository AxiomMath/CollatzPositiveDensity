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
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.Terminal.SourceWindow
public import CollatzPosDens.Terminal.UnweightedMass

/-!
# The weight of a counted pair

Let `t ≥ t_min` (`targetFloor`, equal to `16^{16544}`) be an odd integer, `j ≥ 0`, let `X` be
admissible for generation `j`, and let `(h, w)` be a counted pair of `Υ_{j,X}(t)`. Then
`ω(h) ω(w) ≤ t / X`.

With `x = src(w, R_h)` and `c = ŵ(h) w`, one has `src(c, t) = x` and `ω(c) = ω(h) ω(w)`, so the
affine identity gives `t = ω(h) ω(w) x + off(c) ≥ ω(h) ω(w) x`. The source window gives
`x ≥ X > 0`, whence `ω(h) ω(w) ≤ t / x ≤ t / X`.

## Main results

* `CollatzPosDens.weight_mul_weight_le_div_of_odd`: the bound, for an odd integer `t ≥ t_min`.
* `CollatzPosDens.GoodSeed.weight_mul_weight_le_div`: the same bound for an `s`-good seed with
  `s ≥ 1`, which is odd and at least `t_min`.

## Implementation notes

Nonnegativity of the offset holds for every word, so the nonemptiness of `w` is not needed. The
weight `ω(h)` of a history is the weight of its concatenated word `ŵ(h)`. The bound is stated in
`ℝ`, where the scale `X` lives.

## References

* [Mazur, *Collatz positive density*], §17.3.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {X : ℝ}

/-- **Weight of a counted pair.** Let `t ≥ targetFloor` be an odd integer, let `j ≥ 0`, let `X` be
admissible for generation `j`, and let `(h, w)` be a counted pair of `Υ_{j,X}(t)`. Then
`ω(h) ω(w) ≤ t / X`. -/
@[collatz_pos_dens "lem_s06_pair_weight"]
theorem weight_mul_weight_le_div_of_odd {j : ℕ} {X : ℝ} {t : ℤ} (hodd : Odd t)
    (ht : (targetFloor : ℤ) ≤ t) (hX : IsAdmissibleScale t j X) {h : Fin j → Word}
    {w : Word}
    (hp : (h, w) ∈ unweightedMassPairs j X t) :
    ((concatWord h).weight : ℝ) * (w.weight : ℝ) ≤ (t : ℝ) / X := by
  obtain ⟨z, hz⟩ := exists_intCast_src_of_mem_unweightedMassPairs hp
  have hzX : X ≤ (z : ℝ) :=
    (sources_subset_Ico_of_odd hodd ht hX ⟨z, src_mem_sources hp hz, rfl⟩).1
  have hXpos : 0 < X := hX.pos
  have haff := eq_weight_mul_src_add_off (concatWord h ++ w) (t : ℚ)
  rw [src_append, ← historyEndpoint_eq_src, hz, Word.weight_append] at haff
  have hMq : (concatWord h).weight * w.weight * (z : ℚ) ≤ t := by
    linarith [off_nonneg (concatWord h ++ w)]
  have hMr : ((concatWord h).weight : ℝ) * (w.weight : ℝ) * (z : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hMq
  have hω : (0 : ℝ) ≤ ((concatWord h).weight : ℝ) * (w.weight : ℝ) := by
    exact mul_nonneg (by exact_mod_cast (Word.weight_pos (concatWord h)).le)
      (by exact_mod_cast (Word.weight_pos w).le)
  rw [le_div_iff₀ hXpos]
  exact (mul_le_mul_of_nonneg_left hzX hω).trans hMr

/-- The weight of a counted pair for an `s`-good seed `M` with `s ≥ 1`: if `X` is admissible for
generation `n` and `(h, w)` is a counted pair of `Υ_{n,X}(M)`, then `ω(h) ω(w) ≤ M / X`. -/
theorem GoodSeed.weight_mul_weight_le_div {s M : ℕ} (hM : GoodSeed s M) (hs : 0 < s)
    (hX : IsAdmissibleScale M n X) {h : Fin n → Word} {w : Word}
    (hp : (h, w) ∈ unweightedMassPairs n X M) :
    ((concatWord h).weight : ℝ) * (w.weight : ℝ) ≤ (M : ℝ) / X := by
  have hfl : targetFloor ≤ M := by
    have h := (hM.two_pow_66176_lt hs).le
    rwa [show (66176 : ℕ) = 4 * 16544 by norm_num, pow_mul, show (2 : ℕ) ^ 4 = 16 by norm_num,
      ← targetFloor_eq] at h
  have := weight_mul_weight_le_div_of_odd (t := (M : ℤ)) (j := n) (X := X)
    (by exact_mod_cast hM.odd) (by exact_mod_cast hfl)
  simp only [Int.cast_natCast] at this
  exact this hX hp

end CollatzPosDens
