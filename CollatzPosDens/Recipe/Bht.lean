/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Recipe.Erec
public import CollatzPosDens.Recipe.Jstar

/-!
# The height exponent `B_ht`

This file defines the height exponent
$$B_{\mathrm{ht}} = \mathcal E(J_*) + \lfloor 2\beta(J_*)/3 \rfloor,$$
where `𝓔` is the height exponent recurrence, `β(j) = b_j` are the scales and `J_*` is the final
generation threshold.

## Main definitions

* `CollatzPosDens.heightExponentOf`: the expression `𝓔(J) + ⌊2β(J)/3⌋` at a generation `J`.
* `CollatzPosDens.heightExponent`: the height exponent `B_ht`, its value at `J = J_*`.

## Main results

* `CollatzPosDens.heightExponent_def`: the defining formula of `B_ht`.
* `CollatzPosDens.erec_le_heightExponent`: `𝓔(J_*) ≤ B_ht`.
* `CollatzPosDens.heightExponentOf_monotone`: `J ↦ 𝓔(J) + ⌊2β(J)/3⌋` is monotone.

## Implementation notes

The height exponent is a natural number, since it is used as an exponent of `2`; the floor
`⌊2β(J_*)/3⌋` is natural-number division. Since `J_*` is far too large to be evaluated,
`heightExponent` is irreducible and is meant to be used through `heightExponent_def`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The expression `𝓔(J) + ⌊2β(J)/3⌋` at a generation `J`. The height exponent `B_ht` is its
value at the final generation threshold `J_*`. -/
def heightExponentOf (J : ℕ) : ℕ :=
  erec J + 2 * scale J / 3

/-- The defining formula of `heightExponentOf`. -/
theorem heightExponentOf_def (J : ℕ) : heightExponentOf J = erec J + 2 * scale J / 3 :=
  rfl

/-- `𝓔(J) ≤ heightExponentOf J`. -/
theorem erec_le_heightExponentOf (J : ℕ) : erec J ≤ heightExponentOf J :=
  Nat.le_add_right _ _

/-- `heightExponentOf` is monotone in the generation. -/
theorem heightExponentOf_monotone : Monotone heightExponentOf := fun _ _ h =>
  Nat.add_le_add (erec_monotone h)
    (Nat.div_le_div_right (Nat.mul_le_mul_left 2 (scale_monotone h)))

/-- The height exponent `B_ht = 𝓔(J_*) + ⌊2β(J_*)/3⌋`. -/
@[collatz_pos_dens "def_Bht", irreducible]
noncomputable def heightExponent : ℕ :=
  heightExponentOf finalGenerationThreshold

/-- `B_ht` is `heightExponentOf` at `J_*`. -/
theorem heightExponent_eq_heightExponentOf :
    heightExponent = heightExponentOf finalGenerationThreshold := by
  unfold heightExponent
  rfl

/-- The defining formula `B_ht = 𝓔(J_*) + ⌊2β(J_*)/3⌋`. -/
theorem heightExponent_def :
    heightExponent = erec finalGenerationThreshold + 2 * scale finalGenerationThreshold / 3 :=
  heightExponent_eq_heightExponentOf.trans (heightExponentOf_def _)

/-- `𝓔(J_*) ≤ B_ht`. -/
theorem erec_le_heightExponent : erec finalGenerationThreshold ≤ heightExponent :=
  heightExponent_eq_heightExponentOf ▸ erec_le_heightExponentOf _

/-- `⌊2β(J_*)/3⌋ ≤ B_ht`. -/
theorem scale_div_le_heightExponent : 2 * scale finalGenerationThreshold / 3 ≤ heightExponent :=
  heightExponent_def ▸ Nat.le_add_left _ _

end CollatzPosDens
