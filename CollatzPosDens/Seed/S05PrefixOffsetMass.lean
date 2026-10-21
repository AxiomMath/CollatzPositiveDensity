/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Transfer.PrefixExtension

/-!
# Offset mass of a prefix-disjoint family

Let `𝒱` be a prefix-disjoint set of words, all of length at most `h`, and let `x` be real. Then
`𝐩({v ∈ 𝒱 : off(v) > x}) ≤ 𝐩({u ∈ ℤ_{≥1}^h : off(u) > x})`.

The subfamily `𝒱_x = {v ∈ 𝒱 : off(v) > x}` is again prefix-disjoint with lengths at most `h`,
so by `geomMass_eq_geomMass_setOf_prefix_mem` its mass equals the mass of the words `u` of
length `h` having a prefix in `𝒱_x`. Writing such a word as `u = v z` with `v ∈ 𝒱_x`, the
cocycle identity `off_append`, `off(vz) = off(v) + ω(v) off(z)`, gives `off(u) ≥ off(v) > x`,
since `ω(v) > 0` and `off(z) ≥ 0`. Monotonicity of the geometric mass concludes.

## Main results

* `CollatzPosDens.geomMass_setOf_lt_off_le`: the offset-mass comparison.

## References

* [Mazur, *Collatz positive density*], §16.7.
-/

@[expose] public section

open InformationTheory

namespace CollatzPosDens

/-- **Offset mass of a prefix-disjoint family.** If `𝒱` is a prefix-disjoint set of words, all
of length at most `h`, and `x` is real, then
`𝐩({v ∈ 𝒱 : off(v) > x}) ≤ 𝐩({u ∈ ℤ_{≥1}^h : off(u) > x})`. -/
@[collatz_pos_dens "lem_s05_prefix_offset_mass"]
theorem geomMass_setOf_lt_off_le {V : Set Word} (hV : IsPrefixFree V) {h : ℕ}
    (hlen : ∀ v ∈ V, v.length ≤ h) (x : ℝ) :
    geomMass {v ∈ V | x < (off v : ℝ)} ≤
      geomMass {u : Word | u.length = h ∧ x < (off u : ℝ)} := by
  rw [geomMass_eq_geomMass_setOf_prefix_mem (h := h)
    (fun a ha b hb hab => hV a ha.1 b hb.1 hab) fun v hv => hlen v hv.1]
  refine geomMass_mono ?_
  rintro u ⟨hu, v, ⟨-, hv⟩, z, rfl⟩
  refine ⟨hu, hv.trans_le ?_⟩
  exact_mod_cast off_append v z ▸
    le_add_of_nonneg_right (mul_nonneg (Word.weight_pos v).le (off_nonneg z))

end CollatzPosDens
