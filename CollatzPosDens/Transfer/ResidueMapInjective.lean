/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueMap

/-!
# Injectivity of the residue map

For every word `w` and every `t ∈ ℕ`, the residue map `φ_w : G_t → G_{t+|w|}`
(`CollatzPosDens.residueMap`, with `G_t = ℤ/3^tℤ`) is injective.
Writing `d = |w|` and `A = A(w)` for the valuation sum of `w`, an equality `φ_w(z) = φ_w(z')` gives
`3^d (2⁻¹)^A (z̃ - z̃') = 0` in `G_{t+d}`; multiplying by the unit `2^A` yields
`3^{t+d} ∣ 3^d (z̃ - z̃')`, hence `3^t ∣ z̃ - z̃'`, i.e. `z = z'`.

## Main results

* `CollatzPosDens.residueMap_injective`: `φ_w : G_t → G_{t+|w|}` is injective.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every word `w` and `t ∈ ℕ`, the residue map `φ_w : G_t → G_{t+|w|}` is injective. -/
@[collatz_pos_dens "lem_residue_map_injective"]
theorem residueMap_injective (w : Word) (t : ℕ) : Function.Injective (residueMap w t) := by
  intro z z' h
  rw [residueMap_apply, residueMap_apply, add_left_inj, dyadicRed_weight] at h
  have h2 : (2 : ResidueGroup (t + w.length)) ^ w.valSum * 2⁻¹ ^ w.valSum = 1 :=
    two_pow_mul_inv_two_pow _ _
  have h3 : ((3 ^ w.length * z.val : ℕ) : ResidueGroup (t + w.length)) =
      ((3 ^ w.length * z'.val : ℕ) : ResidueGroup (t + w.length)) := by
    push_cast
    linear_combination (2 : ResidueGroup (t + w.length)) ^ w.valSum * h -
      3 ^ w.length * ((z.val : ResidueGroup (t + w.length)) - z'.val) * h2
  rw [ZMod.natCast_eq_natCast_iff, pow_add, mul_comm (3 ^ t)] at h3
  exact ZMod.val_injective _ <| (Nat.ModEq.mul_left_cancel' (by positivity) h3).eq_of_lt_of_lt
    (ZMod.val_lt z) (ZMod.val_lt z')

end CollatzPosDens
