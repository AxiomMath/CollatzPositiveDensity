/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.Linarith
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.StoppingTrace.TrLive
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrSupportUpward

/-!
# Vertical growth along a live path

Let `o : ℤ × ℤ` and let `β : List (List ℤ × ℤ)` be a list of blocks of length `N`, each with
closing letter `b.2 ≥ 4`, satisfying `TrLive β`. Between times `t ≤ t'` the path `trPath o β`
passes through the blocks of `β` with indices in `[min t N, min t' N)`, so
`bkL (trPath o β t') - bkL (trPath o β t)` is the sum of `bkL (chBlockPoint b)` over those
blocks `b`. Each such block has nonzero `chBlockWeight`, hence `4 ≤ bkL (chBlockPoint b)`, and
therefore `bkL (trPath o β t') - bkL (trPath o β t) ≥ 4 (min t' N - min t N)`.

## Main results

* `CollatzPosDens.trPath_bkL_sub_ge`: the growth bound
  `4 (min t' N - min t N) ≤ bkL (trPath o β t') - bkL (trPath o β t)` for `t ≤ t'`.

## Implementation notes

The inequality is stated in `ℤ`, and the hypothesis on the closing letters is the bound
`∀ b ∈ β, 4 ≤ b.2`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Vertical growth along a live path.** If every block of `β` has closing letter at least
`4` and `TrLive β` holds, then for `t ≤ t'` and `N = β.length`,
`4 (min t' N - min t N) ≤ bkL (trPath o β t') - bkL (trPath o β t)`. -/
@[collatz_pos_dens "lem_tr_path_growth"]
theorem trPath_bkL_sub_ge (o : ℤ × ℤ) {β : List (List ℤ × ℤ)} (hβ : ∀ b ∈ β, 4 ≤ b.2)
    (hlive : TrLive β) {t t' : ℕ} (htt' : t ≤ t') :
    4 * (((min t' β.length : ℕ) : ℤ) - (min t β.length : ℕ)) ≤
      bkL (trPath o β t') - bkL (trPath o β t) := by
  induction t', htt' using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    by_cases hkN : k < β.length
    · rw [trPath_succ o β hkN]
      have h4 : 4 ≤ bkL (chBlockPoint β[k]) :=
        four_le_bkL_chBlockPoint_of_chBlockWeight_ne_zero (hβ _ (List.getElem_mem hkN))
          (hlive _ (List.getElem_mem hkN))
      have : ((min (k + 1) β.length : ℕ) : ℤ) = (min k β.length : ℕ) + 1 := by omega
      simp only [bkL, Prod.snd_add] at ih h4 ⊢
      linarith
    · rw [trPath_of_length_le o β (by omega : β.length ≤ k + 1),
        ← trPath_of_length_le o β (by omega : β.length ≤ k)]
      have : min (k + 1) β.length = min k β.length := by omega
      rw [this]
      exact ih

end CollatzPosDens
