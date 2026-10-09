/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# A cubic lower bound for `exp (-t)`

For every real `t ≥ 0`, `e^{-t} ≥ 1 - t + t²/2 - t³/6`, where the right-hand side is the third
Taylor polynomial of `e^{-t}` at `0`.

The proof iterates the elementary fact that a function vanishing at `0` with nonnegative
derivative on `[0, ∞)` is nonnegative there. Applied successively to
`g₁(t) = e^{-t} - 1 + t`, `g₂(t) = 1 - t + t²/2 - e^{-t}` and
`g₃(t) = e^{-t} - 1 + t - t²/2 + t³/6`, whose derivatives are `1 - e^{-t}`, `g₁` and `g₂`
respectively, it gives `g₃ ≥ 0`, which is the claim.

## Main results

* `CollatzPosDens.cubic_le_exp_neg`: `1 - t + t²/2 - t³/6 ≤ e^{-t}` for `0 ≤ t`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- A function on `ℝ` vanishing at `0` whose derivative is nonnegative on `[0, ∞)` is
nonnegative on `[0, ∞)`. -/
private lemma nonneg_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h0 : f 0 = 0) (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hf x).continuousAt.continuousWithinAt)
      (fun x _ => (hf x).hasDerivWithinAt)
      (fun x hx => hd x (le_of_lt (by simpa using hx)))
  simpa [h0] using hmono (Set.mem_Ici.mpr le_rfl) ht ht

/-- **Cubic lower bound for `exp (-t)`.** For every real `t ≥ 0`,
`e^{-t} ≥ 1 - t + t²/2 - t³/6`. -/
@[collatz_pos_dens "lem_ch_exp_cubic"]
theorem cubic_le_exp_neg {t : ℝ} (ht : 0 ≤ t) :
    1 - t + t ^ 2 / 2 - t ^ 3 / 6 ≤ exp (-t) := by
  have hd : ∀ x, HasDerivAt (fun x => exp (-x)) (-exp (-x)) x := fun x => by
    simpa using (hasDerivAt_neg x).exp
  have h1 : ∀ s, 0 ≤ s → 0 ≤ exp (-s) - 1 + s := fun s hs =>
    nonneg_of_hasDerivAt_nonneg (f := fun x => exp (-x) - 1 + x)
      (f' := fun x => -exp (-x) + 1)
      (fun x => ((hd x).sub_const 1).add (hasDerivAt_id' x))
      (by simp) (fun x hx => by
        have := exp_le_one_iff.mpr (neg_nonpos.mpr hx); linarith) hs
  have h2 : ∀ s, 0 ≤ s → 0 ≤ 1 - s + s ^ 2 / 2 - exp (-s) := fun s hs =>
    nonneg_of_hasDerivAt_nonneg (f := fun x => 1 - x + x ^ 2 / 2 - exp (-x))
      (f' := fun x => -1 + x + exp (-x))
      (fun x => by
        have := (((hasDerivAt_id' x).const_sub 1).add
          ((hasDerivAt_pow 2 x).div_const 2)).sub (hd x)
        convert this using 1; push_cast; ring)
      (by simp) (fun x hx => by have := h1 x hx; linarith) hs
  have h3 := nonneg_of_hasDerivAt_nonneg
      (f := fun x => exp (-x) - 1 + x - x ^ 2 / 2 + x ^ 3 / 6)
      (f' := fun x => -exp (-x) + 1 - x + x ^ 2 / 2)
      (fun x => by
        have := ((((hd x).sub_const 1).add (hasDerivAt_id' x)).sub
          ((hasDerivAt_pow 2 x).div_const 2)).add ((hasDerivAt_pow 3 x).div_const 6)
        convert this using 1; push_cast; ring)
      (by simp) (fun x hx => by have := h2 x hx; linarith) ht
  linarith

end CollatzPosDens
