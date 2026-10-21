/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDirectCertificateSound
public import CollatzPosDens.StoppingTrace.TrTailGain

/-!
# The direct-entry certificate at `ω = 13`

This file checks cells of the direct-entry certificate for the pair `(ω, p) = (13, 1)` (see
`CollatzPosDens.exists_trTreeCost_trWhitePolicy_sub_trTailGain_lt`). Every odd `m < 2^{9}` is given
a bisection shape (`CollatzPosDens.TrDirectCertificate.Shape`) of `[-1/3, 1/3]`: by default the
four quarters of `[-1/3, 1/3]`, and for the values of `m` listed in
`CollatzPosDens.TrDirectCertificate.excThirteen` (none at `ω = 13`) a finer one. For each accepted
cell `(D, k)` of the default shape and each residue class of `m` modulo `4`, and for each other
accepted cell, the check `CollatzPosDens.TrDirectCertificate.cellCheck` of all the `m` concerned is
carried out by the kernel, in its own declaration.

## Main results

* `CollatzPosDens.TrDirectCertificate.cellGood_thirteen`: every accepted cell of the shape of every
  odd `m < 2^{9}` is good.

## References

* [Mazur, *Collatz positive density*], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrDirectCertificate

/-- The default shape for `ω = 13`. -/
def dfltThirteen : Shape := (.node (.node .leaf .leaf) (.node .leaf .leaf))

/-- The odd `m < 2^{9}` whose shape is not the default one, with their shapes. -/
def excThirteen : List (ℕ × Shape) := []

/-- The shape of `m` for `ω = 13`. -/
def shapeThirteen (m : ℕ) : Shape := shapeOf dfltThirteen excThirteen m

/-- The check `cellCheck` of the cell `(2, 0)` holds at `ω = 13` for every odd `m < 2^{9}` with
`m ≡ 1 (mod 4)` whose shape has this cell. -/
theorem cellCheck_thirteen_2_0_1 :
    cellCheck 13 1 697807 3276800000 31890970593929087280 2 0
      (mList 1 2 1 (2, 0) dfltThirteen excThirteen) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(2, 0)` holds at `ω = 13` for every odd `m < 2^{9}` with
`m ≡ 3 (mod 4)` whose shape has this cell. -/
theorem cellCheck_thirteen_2_0_3 :
    cellCheck 13 1 697807 3276800000 31890970593929087280 2 0
      (mList 1 2 3 (2, 0) dfltThirteen excThirteen) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(2, 1)` holds at `ω = 13` for every odd `m < 2^{9}` with
`m ≡ 1 (mod 4)` whose shape has this cell. -/
theorem cellCheck_thirteen_2_1_1 :
    cellCheck 13 1 697807 3276800000 31890970593929087280 2 1
      (mList 1 2 1 (2, 1) dfltThirteen excThirteen) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(2, 1)` holds at `ω = 13` for every odd `m < 2^{9}` with
`m ≡ 3 (mod 4)` whose shape has this cell. -/
theorem cellCheck_thirteen_2_1_3 :
    cellCheck 13 1 697807 3276800000 31890970593929087280 2 1
      (mList 1 2 3 (2, 1) dfltThirteen excThirteen) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(2, 2)` holds at `ω = 13` for every odd `m < 2^{9}` with
`m ≡ 1 (mod 4)` whose shape has this cell. -/
theorem cellCheck_thirteen_2_2_1 :
    cellCheck 13 1 697807 3276800000 31890970593929087280 2 2
      (mList 1 2 1 (2, 2) dfltThirteen excThirteen) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(2, 2)` holds at `ω = 13` for every odd `m < 2^{9}` with
`m ≡ 3 (mod 4)` whose shape has this cell. -/
theorem cellCheck_thirteen_2_2_3 :
    cellCheck 13 1 697807 3276800000 31890970593929087280 2 2
      (mList 1 2 3 (2, 2) dfltThirteen excThirteen) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(2, 3)` holds at `ω = 13` for every odd `m < 2^{9}` with
`m ≡ 1 (mod 4)` whose shape has this cell. -/
theorem cellCheck_thirteen_2_3_1 :
    cellCheck 13 1 697807 3276800000 31890970593929087280 2 3
      (mList 1 2 1 (2, 3) dfltThirteen excThirteen) = true := by
  decide +kernel

/-- The check `cellCheck` of the cell `(2, 3)` holds at `ω = 13` for every odd `m < 2^{9}` with
`m ≡ 3 (mod 4)` whose shape has this cell. -/
theorem cellCheck_thirteen_2_3_3 :
    cellCheck 13 1 697807 3276800000 31890970593929087280 2 3
      (mList 1 2 3 (2, 3) dfltThirteen excThirteen) = true := by
  decide +kernel

/-- The Lipschitz bound for `(ω, p) = (13, 1)`. -/
theorem lipB_thirteen : lipB 14 15 0 0 = 31890970593929087280 := by
  decide +kernel

/-- **The cells at `ω = 13`.** For every odd `m < 2^{9}`, every accepted cell of the shape
of `m` is good. -/
theorem cellGood_thirteen : ∀ m : ℕ, m % 2 = 1 → m < 2 ^ (1 + 8) →
    ∀ q ∈ (shapeThirteen m).leaves 0 0, CellGood 13 1 q.1 q.2 m := by
  intro m hodd hlt q hq
  have hT : trTailGain 13 8 = ((697807 : ℕ) : ℝ) / ((3276800000 : ℕ) : ℝ) := by
    rw [trTailGain_thirteen_eight]
    norm_num
  have hL : trTreeLip (fun _ => 8) (allPolicy (13 + 1)) 0 0 ≤
      ((31890970593929087280 : ℕ) : ℝ) / one := by
    have := trTreeLip_allPolicy_le (13 + 1) 15 0 0 (by norm_num)
    rwa [lipB_thirteen] at this
  have key : ∀ (a ρ : ℕ) (q : ℕ × ℕ), a ≤ 1 + 8 →
      cellCheck 13 1 697807 3276800000 31890970593929087280 q.1 q.2
        (mList 1 a ρ q dfltThirteen excThirteen) = true →
      1 ≤ ρ → m % 2 ^ a = ρ → q ∈ (shapeThirteen m).leaves 0 0 → CellGood 13 1 q.1 q.2 m :=
    fun a ρ q ha hc hρ hmρ hq => cellGood_of_cellCheck (by norm_num) hT hL hc
      (fun _ h => pos_of_mem_mList hρ h) m (mem_mList ha hlt (by omega) hmρ hq)
  have hQ := mem_of_mem_leaves_shapeOf
      (Q := [(2, 0), (2, 1), (2, 2), (2, 3)])
      (by decide +kernel) (by decide +kernel) hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl
  · have hρlt : m % 2 ^ 2 < 4 := Nat.mod_lt _ (by norm_num)
    have hρodd : m % 2 ^ 2 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num)]
      exact hodd
    generalize hr : m % 2 ^ 2 = ρ at hρlt hρodd
    obtain rfl | rfl
      : ρ = 1 ∨ ρ = 3 := by omega
    · exact key 2 1 (2, 0) (by norm_num) cellCheck_thirteen_2_0_1 (by norm_num) hr hq
    · exact key 2 3 (2, 0) (by norm_num) cellCheck_thirteen_2_0_3 (by norm_num) hr hq
  · have hρlt : m % 2 ^ 2 < 4 := Nat.mod_lt _ (by norm_num)
    have hρodd : m % 2 ^ 2 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num)]
      exact hodd
    generalize hr : m % 2 ^ 2 = ρ at hρlt hρodd
    obtain rfl | rfl
      : ρ = 1 ∨ ρ = 3 := by omega
    · exact key 2 1 (2, 1) (by norm_num) cellCheck_thirteen_2_1_1 (by norm_num) hr hq
    · exact key 2 3 (2, 1) (by norm_num) cellCheck_thirteen_2_1_3 (by norm_num) hr hq
  · have hρlt : m % 2 ^ 2 < 4 := Nat.mod_lt _ (by norm_num)
    have hρodd : m % 2 ^ 2 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num)]
      exact hodd
    generalize hr : m % 2 ^ 2 = ρ at hρlt hρodd
    obtain rfl | rfl
      : ρ = 1 ∨ ρ = 3 := by omega
    · exact key 2 1 (2, 2) (by norm_num) cellCheck_thirteen_2_2_1 (by norm_num) hr hq
    · exact key 2 3 (2, 2) (by norm_num) cellCheck_thirteen_2_2_3 (by norm_num) hr hq
  · have hρlt : m % 2 ^ 2 < 4 := Nat.mod_lt _ (by norm_num)
    have hρodd : m % 2 ^ 2 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num)]
      exact hodd
    generalize hr : m % 2 ^ 2 = ρ at hρlt hρodd
    obtain rfl | rfl
      : ρ = 1 ∨ ρ = 3 := by omega
    · exact key 2 1 (2, 3) (by norm_num) cellCheck_thirteen_2_3_1 (by norm_num) hr hq
    · exact key 2 3 (2, 3) (by norm_num) cellCheck_thirteen_2_3_3 (by norm_num) hr hq

end TrDirectCertificate

end CollatzPosDens
