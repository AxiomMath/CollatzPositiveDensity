/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrE8
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The eighth-order defect underestimates `1 - e^{-t}`

For every real `t > 0`, the eighth-order exponential defect satisfies `E₈(t) < 1 - e^{-t}`;
equivalently, the degree-eight Taylor polynomial `∑_{j=0}^{8} (-t)^j / j!` of `e^{-t}` strictly
exceeds `e^{-t}` for `t > 0`.

## Main results

* `CollatzPosDens.E8_lt_one_sub_exp_neg`: `E₈(t) < 1 - e^{-t}` for `t > 0`.

## Implementation notes

Instead of Taylor's formula with integral remainder, we use the function
`φ(s) = e^{s} (1 - E₈(s))`, whose derivative is `e^{s} s⁸ / 8!` (the Taylor polynomial terms
telescope). Hence `φ` is strictly increasing on `[0, ∞)`, so `φ(t) > φ(0) = 1` for `t > 0`,
which is the claim after multiplying by `e^{-t}`. The two arguments are equivalent: the integral
of `φ'` over `[0, t]` is `e^{t}` times the integral remainder of the Taylor expansion.
-/

@[expose] public section

namespace CollatzPosDens

open Set

/-- The derivative of `s ↦ e^{s} (1 - E₈(s))` is `e^{s} s⁸ / 8!`. -/
private theorem hasDerivAt_exp_mul_one_sub_E8 (s : ℝ) :
    HasDerivAt (fun s => Real.exp s * (1 - E8 s)) (Real.exp s * (s ^ 8 / 40320)) s := by
  have hp : HasDerivAt (fun s : ℝ => 1 - (s - s ^ 2 / 2 + s ^ 3 / 6 - s ^ 4 / 24 + s ^ 5 / 120
      - s ^ 6 / 720 + s ^ 7 / 5040 - s ^ 8 / 40320))
      (-(1 - s + s ^ 2 / 2 - s ^ 3 / 6 + s ^ 4 / 24 - s ^ 5 / 120 + s ^ 6 / 720
        - s ^ 7 / 5040)) s := by
    have := ((((((((hasDerivAt_id s).sub ((hasDerivAt_pow 2 s).div_const 2)).add
      ((hasDerivAt_pow 3 s).div_const 6)).sub ((hasDerivAt_pow 4 s).div_const 24)).add
      ((hasDerivAt_pow 5 s).div_const 120)).sub ((hasDerivAt_pow 6 s).div_const 720)).add
      ((hasDerivAt_pow 7 s).div_const 5040)).sub ((hasDerivAt_pow 8 s).div_const 40320)).const_sub 1
    convert this using 1
    · simp
    · push_cast; ring
  have hE : (fun s => 1 - E8 s) = fun s : ℝ => 1 - (s - s ^ 2 / 2 + s ^ 3 / 6 - s ^ 4 / 24
      + s ^ 5 / 120 - s ^ 6 / 720 + s ^ 7 / 5040 - s ^ 8 / 40320) := by
    funext s; rw [E8_eq]
  have := (Real.hasDerivAt_exp s).mul (hE ▸ hp)
  convert this using 1
  rw [E8_eq]; ring

/-- For every real `t > 0`, `E₈(t) < 1 - e^{-t}`. -/
@[collatz_pos_dens "lem_tr_E8_bound"]
theorem E8_lt_one_sub_exp_neg {t : ℝ} (ht : 0 < t) : E8 t < 1 - Real.exp (-t) := by
  set φ : ℝ → ℝ := fun s => Real.exp s * (1 - E8 s) with hφ
  have hmono : StrictMonoOn φ (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
    · exact fun s _ => (hasDerivAt_exp_mul_one_sub_E8 s).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hasDerivAt_exp_mul_one_sub_E8 s).deriv]
      have : (0 : ℝ) < s := hs
      positivity
  have h := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 ht.le) ht
  simp only [hφ, Real.exp_zero, E8_zero, sub_zero, mul_one] at h
  have hexp : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-t) := Real.exp_pos _
  nlinarith

end CollatzPosDens
