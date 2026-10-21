/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Recipe.CovGen
public import CollatzPosDens.Recipe.Erec

/-!
# The height exponent `B_ht`

Let `J_c = 23000` be the coverage generation (`CollatzPosDens.covGen`). The height exponent is
$$B_{\mathrm{ht}} := \mathcal E(J_{\mathrm c})
  + \lfloor 2 b_{J_{\mathrm c}}/3 \rfloor \in \mathbb{N},$$
where `𝓔` is the height exponent recurrence and `b_j` are the scales.

## Main definitions

* `CollatzPosDens.heightExponentOf`: the expression `𝓔(J) + ⌊2b_J/3⌋` at a generation `J`.
* `CollatzPosDens.heightExponent`: the height exponent `B_ht`, its value at `J = J_c`.

## Main results

* `CollatzPosDens.heightExponent_def`: the defining formula of `B_ht`.
* `CollatzPosDens.erec_le_heightExponent`: `𝓔(J_c) ≤ B_ht`.
* `CollatzPosDens.heightExponentOf_monotone`: `J ↦ 𝓔(J) + ⌊2b_J/3⌋` is monotone.

## Implementation notes

The height exponent is a natural number, since it is used as an exponent of `2`; the floor
`⌊2b_{J_c}/3⌋` is natural-number division. Since `𝓔(J_c)` is far too large to be evaluated,
`heightExponent` is irreducible and is meant to be used through `heightExponent_def`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The expression `𝓔(J) + ⌊2b_J/3⌋` at a generation `J`. The height exponent `B_ht` is its
value at the coverage generation `J_c`. -/
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

/-- **The height exponent** `B_ht := 𝓔(J_c) + ⌊2b_{J_c}/3⌋ ∈ ℕ`, where `J_c` is the coverage
generation. -/
@[collatz_pos_dens "def_Bht", irreducible]
def heightExponent : ℕ :=
  heightExponentOf covGen

/-- `B_ht` is `heightExponentOf` at `J_c`. -/
theorem heightExponent_eq_heightExponentOf : heightExponent = heightExponentOf covGen := by
  unfold heightExponent
  rfl

/-- The defining formula `B_ht = 𝓔(J_c) + ⌊2b_{J_c}/3⌋`. -/
theorem heightExponent_def : heightExponent = erec covGen + 2 * scale covGen / 3 :=
  heightExponent_eq_heightExponentOf.trans (heightExponentOf_def _)

/-- `𝓔(J_c) ≤ B_ht`. -/
theorem erec_le_heightExponent : erec covGen ≤ heightExponent :=
  heightExponent_eq_heightExponentOf ▸ erec_le_heightExponentOf _

/-- `⌊2b_{J_c}/3⌋ ≤ B_ht`. -/
theorem scale_div_le_heightExponent : 2 * scale covGen / 3 ≤ heightExponent :=
  heightExponent_def ▸ Nat.le_add_left _ _

end CollatzPosDens
