/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.DyadicReduction

/-!
# The residue map of a word

For a word `w` of length `d` and `t ∈ ℕ`, the residue map `φ_w : G_t → G_{t+d}` is the
affine map `φ_w(z) = [ω(w)]_{t+d} · z̃ + [off(w)]_{t+d}`, where `z̃ ∈ {0, …, 3^t - 1}`
is the least nonnegative representative of `z`, and `[·]_{t+d}` is the reduction
of dyadic rationals modulo `3^{t+d}`.
Both the weight `ω(w) = 3^d 2^{-A(w)}` and the offset `off(w)` are dyadic rationals.

## Main definitions

* `CollatzPosDens.residueMap w t`: the map `φ_w : G_t → G_{t+|w|}`.

## Main results

* `CollatzPosDens.Word.weight_mem_dyadicRationals`: `ω(w) ∈ ℤ[1/2]`.
* `CollatzPosDens.off_mem_dyadicRationals`: `off(w) ∈ ℤ[1/2]`.
* `CollatzPosDens.dyadicRed_weight`: `[ω(w)]_k = 3^{|w|} (2⁻¹)^{A(w)}`.
* `CollatzPosDens.residueMap_nil`: `φ_∅` is the identity of `G_t`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The weight `ω(w) = 3^{|w|} / 2^{A(w)}` is a dyadic rational. -/
theorem Word.weight_mem_dyadicRationals (w : Word) : w.weight ∈ dyadicRationals := by
  have h := intCast_div_two_pow_mem ((3 : ℤ) ^ w.length) w.valSum
  push_cast at h
  exact h

/-- The offset `off(w)` is a dyadic rational. -/
theorem off_mem_dyadicRationals (w : Word) : off w ∈ dyadicRationals := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [off_cons]
    have h := intCast_div_two_pow_mem 1 (a : ℕ)
    rw [Int.cast_one, one_div] at h
    exact dyadicRationals.mul_mem h (dyadicRationals.add_mem dyadicRationals.one_mem
      (dyadicRationals.mul_mem (by simp) ih))

/-- The residue map `φ_w : G_t → G_{t+d}` of a word `w` of length `d`,
`φ_w(z) = [ω(w)]_{t+d} · z̃ + [off(w)]_{t+d}`, with `z̃ = z.val` the least nonnegative
representative of `z`. -/
@[collatz_pos_dens "def_residue_map"]
noncomputable def residueMap (w : Word) (t : ℕ) (z : ResidueGroup t) :
    ResidueGroup (t + w.length) :=
  dyadicRed (t + w.length) ⟨w.weight, w.weight_mem_dyadicRationals⟩ * (z.val : ResidueGroup _) +
    dyadicRed (t + w.length) ⟨off w, off_mem_dyadicRationals w⟩

/-- Unfolding lemma for `residueMap`. -/
theorem residueMap_apply (w : Word) (t : ℕ) (z : ResidueGroup t) :
    residueMap w t z =
      dyadicRed (t + w.length) ⟨w.weight, w.weight_mem_dyadicRationals⟩ *
          (z.val : ResidueGroup _) +
        dyadicRed (t + w.length) ⟨off w, off_mem_dyadicRationals w⟩ :=
  rfl

/-- The explicit reduction of the weight: `[ω(w)]_k = 3^{|w|} · (2⁻¹)^{A(w)}`. -/
theorem dyadicRed_weight (k : ℕ) (w : Word) :
    dyadicRed k ⟨w.weight, w.weight_mem_dyadicRationals⟩ =
      (3 : ResidueGroup k) ^ w.length * 2⁻¹ ^ w.valSum := by
  have h := dyadicRed_div_two_pow k ((3 : ℤ) ^ w.length) w.valSum
  push_cast at h
  exact h

/-- The reduction of the offset of a concatenation:
`[off(uv)]_k = [off(u)]_k + [ω(u)]_k [off(v)]_k`. -/
theorem dyadicRed_off_append (k : ℕ) (u v : Word) :
    dyadicRed k ⟨off (u ++ v), off_mem_dyadicRationals _⟩ =
      dyadicRed k ⟨off u, off_mem_dyadicRationals u⟩ +
        dyadicRed k ⟨u.weight, u.weight_mem_dyadicRationals⟩ *
          dyadicRed k ⟨off v, off_mem_dyadicRationals v⟩ := by
  have e : (⟨off (u ++ v), off_mem_dyadicRationals _⟩ : dyadicRationals) =
      ⟨off u, off_mem_dyadicRationals u⟩ +
        ⟨u.weight, u.weight_mem_dyadicRationals⟩ * ⟨off v, off_mem_dyadicRationals v⟩ :=
    Subtype.ext (by simp [off_append])
  rw [e, map_add, map_mul]

/-- The residue map of the empty word is the identity of `G_t`. -/
@[simp]
theorem residueMap_nil (t : ℕ) (z : ResidueGroup t) : residueMap [] t z = z := by
  have h1 : dyadicRed t ⟨Word.weight [], Word.weight_mem_dyadicRationals []⟩ = 1 := by
    have : (⟨Word.weight [], Word.weight_mem_dyadicRationals []⟩ : dyadicRationals) = 1 :=
      Subtype.ext (by simp)
    rw [this, map_one]
  have h0 : dyadicRed t ⟨off [], off_mem_dyadicRationals []⟩ = 0 := by
    have : (⟨off [], off_mem_dyadicRationals []⟩ : dyadicRationals) = 0 :=
      Subtype.ext (by simp)
    rw [this, map_zero]
  change dyadicRed t _ * (z.val : ResidueGroup t) + dyadicRed t _ = z
  rw [h1, h0, one_mul, add_zero, ZMod.natCast_zmod_val]

end CollatzPosDens
