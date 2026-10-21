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
# The direct-entry certificate at `ω = 16`

This file checks cells of the direct-entry certificate for the pair `(ω, p) = (16, 1)`, which
bounds the tree cost of the white policy below the tail gain. Every odd `m < 2^{9}` is given a
bisection shape (`CollatzPosDens.TrDirectCertificate.Shape`) of `[-1/3, 1/3]`: by default the four
quarters of `[-1/3, 1/3]`, and for the 16 values of `m` listed in
`CollatzPosDens.TrDirectCertificate.excSixteen` a finer one. For each accepted cell `(D, k)` of the
default shape and each residue class of `m` modulo `4`, and for each other accepted cell, the check
`CollatzPosDens.TrDirectCertificate.cellCheck` of all the `m` concerned is carried out by the
kernel, in its own declaration.

## Main results

* `CollatzPosDens.TrDirectCertificate.cellGood_sixteen`: every accepted cell of the shape of every
  odd `m < 2^{9}` is good.

## References

* [Mazur, *Collatz positive density*], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrDirectCertificate

/-- The default shape for `ω = 16`. -/
def dfltSixteen : Shape := (.node (.node .leaf .leaf) (.node .leaf .leaf))

/-- The odd `m < 2^{9}` whose shape is not the default one, with their shapes. -/
def excSixteen : List (ℕ × Shape) := [
    (31, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (33, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (95, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (97, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (159, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (161, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (223, (.node (.node .leaf .leaf) (.node (.node .leaf .leaf) .leaf))),
    (225, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (287, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (289, (.node (.node .leaf (.node .leaf .leaf)) (.node .leaf .leaf))),
    (351, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (353, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (415, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (417, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (479, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf))),
    (481, (.node (.node .leaf (.node .leaf .leaf)) (.node (.node .leaf .leaf) .leaf)))]

/-- The shape of `m` for `ω = 16`. -/
def shapeSixteen (m : ℕ) : Shape := shapeOf dfltSixteen excSixteen m

/-- The check of the cell `(2, 0)` of the default shape at `ω = 16` holds for every odd
`m < 2^{9}` with `m ≡ 1 (mod 4)` whose shape contains this cell. -/
theorem cellCheck_sixteen_2_0_1 :
    cellCheck 16 1 0 1 37863851383765073935 2 0
      (mList 1 2 1 (2, 0) dfltSixteen excSixteen) = true := by
  decide +kernel

/-- The check of the cell `(2, 0)` of the default shape at `ω = 16` holds for every odd
`m < 2^{9}` with `m ≡ 3 (mod 4)` whose shape contains this cell. -/
theorem cellCheck_sixteen_2_0_3 :
    cellCheck 16 1 0 1 37863851383765073935 2 0
      (mList 1 2 3 (2, 0) dfltSixteen excSixteen) = true := by
  decide +kernel

/-- The check of the cell `(2, 1)` of the default shape at `ω = 16` holds for every odd
`m < 2^{9}` with `m ≡ 1 (mod 4)` whose shape contains this cell. -/
theorem cellCheck_sixteen_2_1_1 :
    cellCheck 16 1 0 1 37863851383765073935 2 1
      (mList 1 2 1 (2, 1) dfltSixteen excSixteen) = true := by
  decide +kernel

/-- The check of the cell `(2, 1)` of the default shape at `ω = 16` holds for every odd
`m < 2^{9}` with `m ≡ 3 (mod 4)` whose shape contains this cell. -/
theorem cellCheck_sixteen_2_1_3 :
    cellCheck 16 1 0 1 37863851383765073935 2 1
      (mList 1 2 3 (2, 1) dfltSixteen excSixteen) = true := by
  decide +kernel

/-- The check of the cell `(2, 2)` of the default shape at `ω = 16` holds for every odd
`m < 2^{9}` with `m ≡ 1 (mod 4)` whose shape contains this cell. -/
theorem cellCheck_sixteen_2_2_1 :
    cellCheck 16 1 0 1 37863851383765073935 2 2
      (mList 1 2 1 (2, 2) dfltSixteen excSixteen) = true := by
  decide +kernel

/-- The check of the cell `(2, 2)` of the default shape at `ω = 16` holds for every odd
`m < 2^{9}` with `m ≡ 3 (mod 4)` whose shape contains this cell. -/
theorem cellCheck_sixteen_2_2_3 :
    cellCheck 16 1 0 1 37863851383765073935 2 2
      (mList 1 2 3 (2, 2) dfltSixteen excSixteen) = true := by
  decide +kernel

/-- The check of the cell `(2, 3)` of the default shape at `ω = 16` holds for every odd
`m < 2^{9}` with `m ≡ 1 (mod 4)` whose shape contains this cell. -/
theorem cellCheck_sixteen_2_3_1 :
    cellCheck 16 1 0 1 37863851383765073935 2 3
      (mList 1 2 1 (2, 3) dfltSixteen excSixteen) = true := by
  decide +kernel

/-- The check of the cell `(2, 3)` of the default shape at `ω = 16` holds for every odd
`m < 2^{9}` with `m ≡ 3 (mod 4)` whose shape contains this cell. -/
theorem cellCheck_sixteen_2_3_3 :
    cellCheck 16 1 0 1 37863851383765073935 2 3
      (mList 1 2 3 (2, 3) dfltSixteen excSixteen) = true := by
  decide +kernel

/-- The check of the cell `(3, 2)` at `ω = 16` holds for every odd `m < 2^{9}` whose shape
contains this cell. -/
theorem cellCheck_sixteen_3_2 :
    cellCheck 16 1 0 1 37863851383765073935 3 2
      (mList 1 1 1 (3, 2) dfltSixteen excSixteen) = true := by
  decide +kernel

/-- The check of the cell `(3, 3)` at `ω = 16` holds for every odd `m < 2^{9}` whose shape
contains this cell. -/
theorem cellCheck_sixteen_3_3 :
    cellCheck 16 1 0 1 37863851383765073935 3 3
      (mList 1 1 1 (3, 3) dfltSixteen excSixteen) = true := by
  decide +kernel

/-- The check of the cell `(3, 4)` at `ω = 16` holds for every odd `m < 2^{9}` whose shape
contains this cell. -/
theorem cellCheck_sixteen_3_4 :
    cellCheck 16 1 0 1 37863851383765073935 3 4
      (mList 1 1 1 (3, 4) dfltSixteen excSixteen) = true := by
  decide +kernel

/-- The check of the cell `(3, 5)` at `ω = 16` holds for every odd `m < 2^{9}` whose shape
contains this cell. -/
theorem cellCheck_sixteen_3_5 :
    cellCheck 16 1 0 1 37863851383765073935 3 5
      (mList 1 1 1 (3, 5) dfltSixteen excSixteen) = true := by
  decide +kernel

/-- The Lipschitz bound for `(ω, p) = (16, 1)`. -/
theorem lipB_sixteen : lipB 17 18 0 0 = 37863851383765073935 := by
  decide +kernel

/-- **The cells at `ω = 16`.** For every odd `m < 2^{9}`, every accepted cell of the shape
of `m` is good. -/
theorem cellGood_sixteen : ∀ m : ℕ, m % 2 = 1 → m < 2 ^ (1 + 8) →
    ∀ q ∈ (shapeSixteen m).leaves 0 0, CellGood 16 1 q.1 q.2 m := by
  intro m hodd hlt q hq
  have hT : trTailGain 16 8 = ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
    rw [trTailGain_sixteen_eight]
    norm_num
  have hL : trTreeLip (fun _ => 8) (allPolicy (16 + 1)) 0 0 ≤
      ((37863851383765073935 : ℕ) : ℝ) / one := by
    have := trTreeLip_allPolicy_le (16 + 1) 18 0 0 (by norm_num)
    rwa [lipB_sixteen] at this
  have key : ∀ (a ρ : ℕ) (q : ℕ × ℕ), a ≤ 1 + 8 →
      cellCheck 16 1 0 1 37863851383765073935 q.1 q.2
        (mList 1 a ρ q dfltSixteen excSixteen) = true →
      1 ≤ ρ → m % 2 ^ a = ρ → q ∈ (shapeSixteen m).leaves 0 0 → CellGood 16 1 q.1 q.2 m :=
    fun a ρ q ha hc hρ hmρ hq => cellGood_of_cellCheck (by norm_num) hT hL hc
      (fun _ h => pos_of_mem_mList hρ h) m (mem_mList ha hlt (by omega) hmρ hq)
  have hQ := mem_of_mem_leaves_shapeOf
      (Q := [(2, 0), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5)])
      (by decide +kernel) (by decide +kernel) hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hρlt : m % 2 ^ 2 < 4 := Nat.mod_lt _ (by norm_num)
    have hρodd : m % 2 ^ 2 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num)]
      exact hodd
    generalize hr : m % 2 ^ 2 = ρ at hρlt hρodd
    obtain rfl | rfl
      : ρ = 1 ∨ ρ = 3 := by omega
    · exact key 2 1 (2, 0) (by norm_num) cellCheck_sixteen_2_0_1 (by norm_num) hr hq
    · exact key 2 3 (2, 0) (by norm_num) cellCheck_sixteen_2_0_3 (by norm_num) hr hq
  · have hρlt : m % 2 ^ 2 < 4 := Nat.mod_lt _ (by norm_num)
    have hρodd : m % 2 ^ 2 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num)]
      exact hodd
    generalize hr : m % 2 ^ 2 = ρ at hρlt hρodd
    obtain rfl | rfl
      : ρ = 1 ∨ ρ = 3 := by omega
    · exact key 2 1 (2, 1) (by norm_num) cellCheck_sixteen_2_1_1 (by norm_num) hr hq
    · exact key 2 3 (2, 1) (by norm_num) cellCheck_sixteen_2_1_3 (by norm_num) hr hq
  · have hρlt : m % 2 ^ 2 < 4 := Nat.mod_lt _ (by norm_num)
    have hρodd : m % 2 ^ 2 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num)]
      exact hodd
    generalize hr : m % 2 ^ 2 = ρ at hρlt hρodd
    obtain rfl | rfl
      : ρ = 1 ∨ ρ = 3 := by omega
    · exact key 2 1 (2, 2) (by norm_num) cellCheck_sixteen_2_2_1 (by norm_num) hr hq
    · exact key 2 3 (2, 2) (by norm_num) cellCheck_sixteen_2_2_3 (by norm_num) hr hq
  · have hρlt : m % 2 ^ 2 < 4 := Nat.mod_lt _ (by norm_num)
    have hρodd : m % 2 ^ 2 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num)]
      exact hodd
    generalize hr : m % 2 ^ 2 = ρ at hρlt hρodd
    obtain rfl | rfl
      : ρ = 1 ∨ ρ = 3 := by omega
    · exact key 2 1 (2, 3) (by norm_num) cellCheck_sixteen_2_3_1 (by norm_num) hr hq
    · exact key 2 3 (2, 3) (by norm_num) cellCheck_sixteen_2_3_3 (by norm_num) hr hq
  · exact key 1 1 (3, 2) (by norm_num) cellCheck_sixteen_3_2 (by norm_num) hodd hq
  · exact key 1 1 (3, 3) (by norm_num) cellCheck_sixteen_3_3 (by norm_num) hodd hq
  · exact key 1 1 (3, 4) (by norm_num) cellCheck_sixteen_3_4 (by norm_num) hodd hq
  · exact key 1 1 (3, 5) (by norm_num) cellCheck_sixteen_3_5 (by norm_num) hodd hq

end TrDirectCertificate

end CollatzPosDens
