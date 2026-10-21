/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.Mixing.MxOffsetTail
public import CollatzPosDens.Seed.S05OffsetCap
public import CollatzPosDens.Seed.S05PrefixOffsetMass

/-!
# Mass of a capped block

For an index `i`, let `𝒞 = 𝒞(b_i, K_i)` be the central family at the scale `b_i = scale i` with
the overshoot cap `K_i = cap i`, and let `M_sel = offsetCap = 2^600`. Then the words of `𝒞` with
offset at most `M_sel` carry almost all of its geometric mass:
$$\mathbf p(\{v ∈ 𝒞 : \mathrm{off}(v) ≤ M_{sel}\}) ≥ \mathbf p(𝒞) - \frac{7}{M_{sel} + 2}.$$

The family `𝒞` is contained in the first-crossing family `𝒲(b_i, r_{b_i}, K_i)`, so it is
prefix-disjoint with all lengths at most `h = h_{b_i}`. Its mass splits as the mass of the words
with `off(v) ≤ M_sel` plus the mass of those with `off(v) > M_sel`. By the offset-mass
comparison for prefix-disjoint families the latter is at most
`𝐩({u ∈ ℤ_{≥1}^h : off(u) > M_sel})`, hence at most
`𝐩({u ∈ ℤ_{≥1}^h : off(u) ≥ M_sel}) ≤ 7 / (M_sel + 2)` by the offset tail bound.

## Main results

* `CollatzPosDens.geomMass_le_geomMass_setOf_off_le_add`: for a prefix-disjoint family `𝒱` of
  bounded length and real `x ≥ 0`, `𝐩(𝒱) ≤ 𝐩({v ∈ 𝒱 : off(v) ≤ x}) + 7 / (x + 2)`.
* `CollatzPosDens.geomMass_centralFamily_sub_le_geomMass_setOf_off_le`: the mass of a capped
  block, `𝐩(𝒞(b_i, K_i)) - 7 / (M_sel + 2) ≤ 𝐩({v ∈ 𝒞(b_i, K_i) : off(v) ≤ M_sel})`.

## Implementation notes

The geometric mass takes values in `[0, ∞]`; the masses here are at most `1`, and the capped
block bound is stated for their real values, where the subtraction is the honest one. The bound
holds for every natural `i`, since `M_sel > 0`, so no range restriction on `i` is imposed.

## References

* [Mazur, *Collatz positive density*], §16.7.
-/

@[expose] public section

open InformationTheory

namespace CollatzPosDens

/-- For a prefix-disjoint family `𝒱` of words of length at most `h` and real `x ≥ 0`,
`𝐩(𝒱) ≤ 𝐩({v ∈ 𝒱 : off(v) ≤ x}) + 7 / (x + 2)`. -/
theorem geomMass_le_geomMass_setOf_off_le_add {V : Set Word} (hV : IsPrefixFree V) {h : ℕ}
    (hlen : ∀ v ∈ V, v.length ≤ h) {x : ℝ} (hx : 0 ≤ x) :
    geomMass V ≤ geomMass {v ∈ V | (off v : ℝ) ≤ x} + ENNReal.ofReal (7 / (x + 2)) := by
  have hsplit : V = {v ∈ V | (off v : ℝ) ≤ x} ∪ {v ∈ V | x < (off v : ℝ)} := by
    ext v
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro hv
      rcases le_or_gt (off v : ℝ) x with h' | h'
      exacts [Or.inl ⟨hv, h'⟩, Or.inr ⟨hv, h'⟩]
    · rintro (⟨hv, -⟩ | ⟨hv, -⟩) <;> exact hv
  calc geomMass V
      ≤ geomMass {v ∈ V | (off v : ℝ) ≤ x} + geomMass {v ∈ V | x < (off v : ℝ)} := by
        conv_lhs => rw [hsplit]
        exact geomMass_union_le _ _
    _ ≤ geomMass {v ∈ V | (off v : ℝ) ≤ x} + ENNReal.ofReal (7 / (x + 2)) := by
        gcongr
        calc geomMass {v ∈ V | x < (off v : ℝ)}
            ≤ geomMass {u : Word | u.length = h ∧ x < (off u : ℝ)} :=
              geomMass_setOf_lt_off_le hV hlen x
          _ ≤ geomMass {u : Word | u.length = h ∧ x ≤ (off u : ℝ)} :=
              geomMass_mono fun u hu => ⟨hu.1, hu.2.le⟩
          _ ≤ ENNReal.ofReal (7 / (x + 2)) := geomMass_offsetTail_le h hx

/-- **Mass of a capped block.** For the central family `𝒞(b_i, K_i)` at the scale `b_i` with
overshoot cap `K_i`, and the offset cap `M_sel = offsetCap = 2^600`,
`𝐩({v ∈ 𝒞(b_i, K_i) : off(v) ≤ M_sel}) ≥ 𝐩(𝒞(b_i, K_i)) - 7 / (M_sel + 2)`, for every
index `i`. -/
@[collatz_pos_dens "lem_s05_capped_block_mass"]
theorem geomMass_centralFamily_sub_le_geomMass_setOf_off_le (i : ℕ) :
    (geomMass (centralFamily (scale i) (cap i))).toReal - 7 / ((offsetCap : ℝ) + 2) ≤
      (geomMass {v ∈ centralFamily (scale i) (cap i) | off v ≤ (offsetCap : ℚ)}).toReal := by
  set C := centralFamily (scale i) (cap i)
  have hsub : C ⊆ firstCrossing (scale i) (rb (scale i)) (cap i) :=
    centralFamily_subset_firstCrossing _ _
  have hV : IsPrefixFree C := fun a ha b hb hab =>
    isPrefixFree_firstCrossing _ _ _ a (hsub ha) b (hsub hb) hab
  have hlen : ∀ v ∈ C, v.length ≤ hb (scale i) := fun v hv =>
    length_le_hb_of_mem_firstCrossing (hsub hv)
  have key := geomMass_le_geomMass_setOf_off_le_add hV hlen (cast_offsetCap_nonneg (R := ℝ))
  have hS : {v ∈ C | off v ≤ (offsetCap : ℚ)} = {v ∈ C | (off v : ℝ) ≤ (offsetCap : ℝ)} := by
    ext v
    simp only [Set.mem_ofPred_eq]
    rw [← Rat.cast_natCast (α := ℝ), Rat.cast_le]
  rw [hS]
  have hfin : geomMass {v ∈ C | (off v : ℝ) ≤ (offsetCap : ℝ)} ≠ ⊤ :=
    ((geomMass_mono fun v hv => hv.1).trans (geomMass_le_one_of_isPrefixFree hV hlen)).trans_lt
      ENNReal.one_lt_top |>.ne
  have h7 : 0 ≤ 7 / ((offsetCap : ℝ) + 2) := by positivity
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩) key
  rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal h7] at this
  linarith

end CollatzPosDens
