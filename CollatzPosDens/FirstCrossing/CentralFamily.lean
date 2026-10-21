/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.FirstCrossingFinite
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.FirstCrossing.Width

/-!
# The central family `𝒞(b, K)`

For a level `b` and an overshoot bound `K`, the central family `𝒞(b, K)` is the set of words
`w` of the first-crossing family `𝒲(b, r_b, K)` whose length lies in the window
`b - wd(b) ≤ |w| ≤ b + wd(b)` around `b`.

## Main definitions

* `CollatzPosDens.centralFamily`: the family `𝒞(b, K)`, as a set of words.

## Main results

* `CollatzPosDens.mem_centralFamily`: the defining membership condition.
* `CollatzPosDens.centralFamily_subset_firstCrossing`: `𝒞(b, K) ⊆ 𝒲(b, r_b, K)`.
* `CollatzPosDens.sub_wd_le_length_of_mem_centralFamily`,
  `CollatzPosDens.length_le_add_wd_of_mem_centralFamily`: the two ends of the length window.
* `CollatzPosDens.centralFamily_mono`: `𝒞(b, K)` increases with `K`.
* `CollatzPosDens.centralFamily_finite`: `𝒞(b, K)` is finite.

## Implementation notes

The source takes integers `b ≥ 2` and `K ≥ 0`; here both are natural numbers and the definition
is made for every `b`. The lower end `b - wd(b)` is truncated subtraction in `ℕ`; since
`wd(b) ≤ b` for every `b` (`wd(0) = 0` and `CollatzPosDens.wd_lt_self`) it agrees with the
integer difference. The family is a `Set`, matching `CollatzPosDens.firstCrossing`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §15.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The central family `𝒞(b, K)`: the words `w ∈ 𝒲(b, r_b, K)` with
`b - wd(b) ≤ |w| ≤ b + wd(b)`. -/
@[collatz_pos_dens "def_central_family"]
noncomputable def centralFamily (b K : ℕ) : Set Word :=
  {w | w ∈ firstCrossing b (rb b) K ∧ b - wd b ≤ w.length ∧ w.length ≤ b + wd b}

/-- Membership in the central family `𝒞(b, K)`. -/
theorem mem_centralFamily {b K : ℕ} {w : Word} :
    w ∈ centralFamily b K ↔
      w ∈ firstCrossing b (rb b) K ∧ b - wd b ≤ w.length ∧ w.length ≤ b + wd b :=
  Iff.rfl

/-- The central family is contained in the first-crossing family `𝒲(b, r_b, K)`. -/
theorem centralFamily_subset_firstCrossing (b K : ℕ) :
    centralFamily b K ⊆ firstCrossing b (rb b) K := fun _ hw => hw.1

/-- The integer form of the lower length bound of a word of `𝒞(b, K)`: `b - wd(b) ≤ |w|`. -/
theorem sub_wd_le_length_of_mem_centralFamily {b K : ℕ} {w : Word}
    (hw : w ∈ centralFamily b K) : (b : ℤ) - wd b ≤ w.length := by
  have h1 := hw.2.1
  have h2 : wd b ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact wd_le_floor_sub_one 0
    · exact (wd_lt_self hb).le
  omega

/-- The upper length bound of a word of `𝒞(b, K)`: `|w| ≤ b + wd(b)`. -/
theorem length_le_add_wd_of_mem_centralFamily {b K : ℕ} {w : Word}
    (hw : w ∈ centralFamily b K) : w.length ≤ b + wd b :=
  hw.2.2

/-- The central families increase with the overshoot bound `K`. -/
theorem centralFamily_mono {b K K' : ℕ} (h : K ≤ K') :
    centralFamily b K ⊆ centralFamily b K' := fun _ hw =>
  ⟨firstCrossing_mono h hw.1, hw.2⟩

/-- The central family `𝒞(b, K)` is finite. -/
theorem centralFamily_finite (b K : ℕ) : (centralFamily b K).Finite :=
  (firstCrossing_finite _ _ _).subset (centralFamily_subset_firstCrossing _ _)

end CollatzPosDens
