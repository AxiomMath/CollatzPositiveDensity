/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H
public import CollatzPosDens.Case3.C3FactorReward
public import CollatzPosDens.CharSum.ChQRecursion

/-!
# The one-step identity for `H`

Fix a level `n` and a residue `ξ ∈ G_n`, and let whiteness, the white factor `w`, the renewal
function `Q` and the penalty `H = Q / w` refer to `(n, ξ, ε_*)`. For every `v ∈ 𝒫`,
`H(v) = ∑_{β ∈ 𝔅} bw(β) exp(-z_* rw(v, β)) H(v + bpt(β))`.

Indeed, the renewal recursion gives `Q(v) = w(v) ∑_β bw(β) I(v; β) Q(v + bpt(β))`. Writing
`Q(u) = w(u) H(u)`, each term with `bw(β) ≠ 0` has no nonclosing letter in `{4, 5}`, so
`w(v + bpt(β)) I(v; β) = exp(-z_* rw(v, β))`; the terms with `bw(β) = 0` vanish on both sides.
Dividing by `w(v) > 0` gives the identity.

## Main results

* `CollatzPosDens.c3H_eq_tsum`: the one-step identity for `H`.

## Implementation notes

The alphabet `𝔅` is the subtype of pairs `List ℤ × ℤ` whose closing letter lies in `{4, 5}`,
and the sum over `𝔅` is a `tsum`, as in `CollatzPosDens.chQ_eq_mul_tsum`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **One-step identity for `H`.** For `v ∈ 𝒫`,
`H(v) = ∑_{β ∈ 𝔅} bw(β) exp(-z_* rw(v, β)) H(v + bpt(β))`, all at the threshold `ε_*`. -/
@[collatz_pos_dens "lem_c3_H_step"]
theorem c3H_eq_tsum (n : ℕ) (ξ : ResidueGroup n) {v : ℤ × ℤ} (hv : v ∈ bkPoints) :
    c3H n ξ (epsStar : ℝ) v =
      ∑' β : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
        chBlockWeight β * Real.exp (-(zStar : ℝ) * trReward n ξ v β) *
          c3H n ξ (epsStar : ℝ) (v + chBlockPoint β) := by
  have hw := (chWhiteFactor_pos n ξ (epsStar : ℝ) v).ne'
  have hQ := chQ_eq_mul_tsum n ξ (epsStar : ℝ) hv
  rw [← chWhiteFactor_mul_c3H] at hQ
  refine (mul_left_cancel₀ hw hQ).trans (tsum_congr fun β => ?_)
  by_cases hβ : chBlockWeight β.1 = 0
  · simp [hβ]
  have hc : ∀ a ∈ (β.1).1, a ≠ 4 ∧ a ≠ 5 := fun a ha => by
    by_contra h
    refine hβ (chBlockWeight_eq_zero_of_mem ha ?_)
    by_cases h4 : a = 4
    · simp [h4]
    · have h5 : a = 5 := by tauto
      simp [h5]
  have he : (β.1).2 = 4 ∨ (β.1).2 = 5 := β.2
  rw [← chWhiteFactor_mul_c3H n ξ _ (v + chBlockPoint β.1),
    ← chWhiteFactor_mul_chInternalWeight_eq_exp_trReward n ξ v β.1 hc he]
  ring

end CollatzPosDens
