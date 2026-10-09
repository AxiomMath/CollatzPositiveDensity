/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.Lb
public import CollatzPosDens.FirstCrossing.Wb
public import CollatzPosDens.Seed.DepthWidth

/-!
# Central words have depth within `dw(b)` of the level

Every word `w` of the central family `𝒞(b, K)` has length within the depth half-width of the
level: `b - dw(b) ≤ |w| ≤ b + dw(b)`. For `b ≥ 256` this window is part of the definition of
`𝒞(b, K)` (and `dw(b) = wd(b)`); for `b < 256` it follows from the length window
`ℓ_b < |w| ≤ h_b` of the first-crossing family, since `ℓ_b = b - ⌊3b/5⌋`,
`h_b = b + ⌊3b/5⌋` and `dw(b) = ⌊3b/5⌋`.

## Main results

* `CollatzPosDens.centralDepth_length_mem`: the window
  `b - dw(b) ≤ |w| ≤ b + dw(b)`, with the lower end as an integer difference.
* `CollatzPosDens.sub_dw_le_length_of_mem_centralFamily`: the lower end as a truncated difference
  in `ℕ`.

## Implementation notes

The bound holds for every natural number `b` and every `K`, with no lower bound on `b`. The
lower bound is stated in `ℤ` as an integer subtraction; since `dw(b) ≤ b` the truncated `ℕ`
form is equivalent.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A word of the central family `𝒞(b, K)` has length in `[b - dw(b), b + dw(b)]`. -/
@[collatz_pos_dens "lem_s05_central_depth"]
theorem centralDepth_length_mem {b K : ℕ} {w : Word} (hw : w ∈ centralFamily b K) :
    (b : ℤ) - dw b ≤ w.length ∧ w.length ≤ b + dw b := by
  by_cases h : 256 ≤ b
  · rw [dw_of_le h]
    exact ⟨sub_wd_le_length_of_mem_centralFamily h hw, length_le_add_wd_of_mem_centralFamily h hw⟩
  · rw [not_le] at h
    have h1 := lb_lt_length_of_mem_firstCrossing (centralFamily_subset_firstCrossing b K hw)
    have h2 := length_le_hb_of_mem_firstCrossing (centralFamily_subset_firstCrossing b K hw)
    rw [lb_eq] at h1
    rw [hb_eq] at h2
    rw [dw_of_lt h]
    omega

/-- The lower length bound of a central word, as a truncated difference in `ℕ`. -/
theorem sub_dw_le_length_of_mem_centralFamily {b K : ℕ} {w : Word} (hw : w ∈ centralFamily b K) :
    b - dw b ≤ w.length := by
  have := (centralDepth_length_mem hw).1
  omega

end CollatzPosDens
