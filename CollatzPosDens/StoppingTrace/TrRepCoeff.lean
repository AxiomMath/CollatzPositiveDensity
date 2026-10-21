/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrPacketRange
public import CollatzPosDens.StoppingTrace.TrRaw3Cap

/-!
# The replaced crossing coefficients

For `s ∈ ℕ` and a packet `(c, o)` the replaced crossing coefficient `δ^{rep}_{s,c,o}` is the
packet deficit `δ^{pk}_{c,o}` (`CollatzPosDens.trPacketDeficit`), except at three places:
* at `(c, o) = (3, 1)` it is `max {δ^{pk}_{3,1}, 1 - ς_s}`, where `ς_s` is the cap of the
  raw-three crossing factor (`CollatzPosDens.trRaw3Cap`);
* at `(c, o) = (4, 1)` and `s = 12` it is `29/50`;
* at `(c, o) = (4, 1)` and `s = 19` it is `16/25`.

Since `δ^{pk}_{c,o} ∈ [0, 1/2]` and `0 < ς_s ≤ 1`, every replaced coefficient lies in `[0, 1]`.

## Main definitions

* `CollatzPosDens.trRepCoeff s c o`: the replaced crossing coefficient `δ^{rep}_{s,c,o}`.

## Main results

* `CollatzPosDens.trRepCoeff_three_one`, `CollatzPosDens.trRepCoeff_four_one_twelve`,
  `CollatzPosDens.trRepCoeff_four_one_nineteen`, `CollatzPosDens.trRepCoeff_of_ne`: the four
  cases of the definition.
* `CollatzPosDens.trPacketDeficit_le_trRepCoeff`: `δ^{pk}_{c,o} ≤ δ^{rep}_{s,c,o}`.
* `CollatzPosDens.trRepCoeff_mem_Icc`: `δ^{rep}_{s,c,o} ∈ [0, 1]`.

## Implementation notes

The definition is made for all natural numbers `c, o`, without the source's range restrictions
`3 ≤ c ≤ 16`, `1 ≤ o ≤ c`; on that range it agrees with the source. It takes values in `ℚ`, as
do `δ^{pk}` and `ς_s`.

## References

* [Mazur, *Collatz positive density*], §9.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The replaced crossing coefficient
`δ^{rep}_{s,c,o} := max {δ^{pk}_{3,1}, 1 - ς_s}` if `(c,o) = (3,1)`, `29/50` if `(c,o) = (4,1)`
and `s = 12`, `16/25` if `(c,o) = (4,1)` and `s = 19`, and `δ^{pk}_{c,o}` otherwise. -/
@[collatz_pos_dens "def_tr_rep_coeff"]
def trRepCoeff (s c o : ℕ) : ℚ :=
  if c = 3 ∧ o = 1 then max (trPacketDeficit 3 1) (1 - trRaw3Cap s)
  else if c = 4 ∧ o = 1 ∧ s = 12 then 29 / 50
  else if c = 4 ∧ o = 1 ∧ s = 19 then 16 / 25
  else trPacketDeficit c o

/-- At `(c, o) = (3, 1)` the replaced coefficient is `max {δ^{pk}_{3,1}, 1 - ς_s}`. -/
@[simp]
theorem trRepCoeff_three_one (s : ℕ) :
    trRepCoeff s 3 1 = max (trPacketDeficit 3 1) (1 - trRaw3Cap s) := by
  simp [trRepCoeff]

/-- At `(c, o) = (4, 1)` and `s = 12` the replaced coefficient is `29/50`. -/
@[simp]
theorem trRepCoeff_four_one_twelve : trRepCoeff 12 4 1 = 29 / 50 := by
  simp [trRepCoeff]

/-- At `(c, o) = (4, 1)` and `s = 19` the replaced coefficient is `16/25`. -/
@[simp]
theorem trRepCoeff_four_one_nineteen : trRepCoeff 19 4 1 = 16 / 25 := by
  simp [trRepCoeff]

/-- Off the three exceptional cases the replaced coefficient is the packet deficit. -/
theorem trRepCoeff_of_ne {s c o : ℕ} (h₃ : ¬(c = 3 ∧ o = 1))
    (h₄ : ¬(c = 4 ∧ o = 1 ∧ (s = 12 ∨ s = 19))) :
    trRepCoeff s c o = trPacketDeficit c o := by
  unfold trRepCoeff
  split_ifs <;> tauto

/-- For `c ∉ {3, 4}` the replaced coefficient is the packet deficit. -/
theorem trRepCoeff_of_ne_three_of_ne_four {s c o : ℕ} (h₃ : c ≠ 3) (h₄ : c ≠ 4) :
    trRepCoeff s c o = trPacketDeficit c o :=
  trRepCoeff_of_ne (by tauto) (by tauto)

/-- For `o ≠ 1` the replaced coefficient is the packet deficit. -/
theorem trRepCoeff_of_ne_one {s c o : ℕ} (ho : o ≠ 1) :
    trRepCoeff s c o = trPacketDeficit c o :=
  trRepCoeff_of_ne (by tauto) (by tauto)

/-- The replaced coefficient dominates the packet deficit: `δ^{pk}_{c,o} ≤ δ^{rep}_{s,c,o}`. -/
theorem trPacketDeficit_le_trRepCoeff (s c o : ℕ) : trPacketDeficit c o ≤ trRepCoeff s c o := by
  have h41 : trPacketDeficit 4 1 ≤ 1 / 2 := (trPacketDeficit_mem_Icc 4 1).2
  unfold trRepCoeff
  split_ifs with h₁ h₂ h₃
  · obtain ⟨rfl, rfl⟩ := h₁; exact le_max_left _ _
  · obtain ⟨rfl, rfl, -⟩ := h₂; linarith
  · obtain ⟨rfl, rfl, -⟩ := h₃; linarith
  · exact le_rfl

/-- The replaced coefficient is nonnegative. -/
theorem trRepCoeff_nonneg (s c o : ℕ) : 0 ≤ trRepCoeff s c o :=
  (trPacketDeficit_mem_Icc c o).1.trans (trPacketDeficit_le_trRepCoeff s c o)

/-- The replaced coefficient is at most `1`. -/
theorem trRepCoeff_le_one (s c o : ℕ) : trRepCoeff s c o ≤ 1 := by
  have h31 : trPacketDeficit 3 1 ≤ 1 / 2 := (trPacketDeficit_mem_Icc 3 1).2
  have hco : trPacketDeficit c o ≤ 1 / 2 := (trPacketDeficit_mem_Icc c o).2
  have hς := trRaw3Cap_pos s
  unfold trRepCoeff
  split_ifs
  · exact max_le (by linarith) (by linarith)
  · norm_num
  · norm_num
  · linarith

/-- The replaced coefficient lies in `[0, 1]`. -/
theorem trRepCoeff_mem_Icc (s c o : ℕ) : trRepCoeff s c o ∈ Set.Icc 0 1 :=
  ⟨trRepCoeff_nonneg s c o, trRepCoeff_le_one s c o⟩

end CollatzPosDens
