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
# The direct-entry certificate at `ω = 1`

This file checks cells of the direct-entry certificate for the pair `(ω, p) = (1, 4)`. Every odd
`m < 2^{12}` is given a bisection shape (`CollatzPosDens.TrDirectCertificate.Shape`) of
`[-1/3, 1/3]`: by default the whole interval `[-1/3, 1/3]`, and for the 136 values of `m` listed in
`CollatzPosDens.TrDirectCertificate.excOne` a finer one. For each accepted cell `(D, k)` of the
default shape and each residue class of `m` modulo `8`, and for each other accepted cell, the check
`CollatzPosDens.TrDirectCertificate.cellCheck` of all the `m` concerned is carried out by the
kernel, in its own declaration.

## Main results

* `CollatzPosDens.TrDirectCertificate.cellGood_one`: every accepted cell of the shape of every
  odd `m < 2^{12}` is good.

## References

* [Mazur, *Collatz positive density*], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrDirectCertificate

/-- The default shape for `ω = 1`. -/
def dfltOne : Shape := .leaf

/-- The odd `m < 2^{12}` whose shape is not the default one, with their shapes. -/
def excOne : List (ℕ × Shape) := [(43, (.node .leaf .leaf)),
    (57, (.node (.node .leaf .leaf) .leaf)), (71, (.node .leaf .leaf)), (85, (.node .leaf .leaf)),
    (171, (.node .leaf .leaf)), (185, (.node .leaf .leaf)), (199, (.node .leaf .leaf)),
    (213, (.node .leaf .leaf)), (235, (.node .leaf .leaf)), (299, (.node .leaf .leaf)),
    (313, (.node .leaf .leaf)), (327, (.node .leaf .leaf)), (341, (.node .leaf .leaf)),
    (427, (.node .leaf .leaf)), (441, (.node .leaf .leaf)),
    (455, (.node .leaf (.node .leaf .leaf))), (469, (.node .leaf .leaf)),
    (555, (.node .leaf .leaf)), (569, (.node (.node .leaf .leaf) .leaf)),
    (583, (.node .leaf .leaf)), (597, (.node .leaf .leaf)),
    (683, (.node (.node .leaf .leaf) .leaf)), (697, (.node .leaf .leaf)),
    (711, (.node .leaf .leaf)), (725, (.node .leaf .leaf)), (789, (.node .leaf .leaf)),
    (811, (.node .leaf .leaf)), (825, (.node .leaf .leaf)), (839, (.node .leaf .leaf)),
    (853, (.node .leaf .leaf)), (939, (.node .leaf .leaf)), (953, (.node .leaf .leaf)),
    (967, (.node .leaf (.node .leaf .leaf))), (981, (.node .leaf .leaf)),
    (1067, (.node .leaf .leaf)), (1081, (.node (.node .leaf .leaf) .leaf)),
    (1095, (.node .leaf .leaf)), (1109, (.node .leaf .leaf)), (1195, (.node .leaf .leaf)),
    (1209, (.node .leaf .leaf)), (1223, (.node .leaf .leaf)), (1237, (.node .leaf .leaf)),
    (1259, (.node .leaf .leaf)), (1323, (.node .leaf .leaf)), (1337, (.node .leaf .leaf)),
    (1351, (.node .leaf .leaf)), (1365, (.node .leaf (.node .leaf .leaf))),
    (1451, (.node .leaf .leaf)), (1465, (.node .leaf .leaf)),
    (1479, (.node .leaf (.node .leaf .leaf))), (1493, (.node .leaf .leaf)),
    (1579, (.node .leaf .leaf)), (1593, (.node (.node .leaf .leaf) .leaf)),
    (1607, (.node .leaf .leaf)), (1621, (.node .leaf .leaf)), (1707, (.node .leaf .leaf)),
    (1721, (.node .leaf .leaf)), (1735, (.node .leaf .leaf)), (1749, (.node .leaf .leaf)),
    (1813, (.node .leaf .leaf)), (1835, (.node .leaf .leaf)), (1849, (.node .leaf .leaf)),
    (1863, (.node .leaf .leaf)), (1877, (.node .leaf .leaf)), (1963, (.node .leaf .leaf)),
    (1977, (.node .leaf .leaf)), (1991, (.node .leaf (.node .leaf .leaf))),
    (2005, (.node .leaf .leaf)), (2091, (.node .leaf .leaf)),
    (2105, (.node (.node .leaf .leaf) .leaf)), (2119, (.node .leaf .leaf)),
    (2133, (.node .leaf .leaf)), (2219, (.node .leaf .leaf)), (2233, (.node .leaf .leaf)),
    (2247, (.node .leaf .leaf)), (2261, (.node .leaf .leaf)), (2283, (.node .leaf .leaf)),
    (2347, (.node .leaf .leaf)), (2361, (.node .leaf .leaf)), (2375, (.node .leaf .leaf)),
    (2389, (.node .leaf .leaf)), (2475, (.node .leaf .leaf)), (2489, (.node .leaf .leaf)),
    (2503, (.node .leaf (.node .leaf .leaf))), (2517, (.node .leaf .leaf)),
    (2603, (.node .leaf .leaf)), (2617, (.node (.node .leaf .leaf) .leaf)),
    (2631, (.node .leaf .leaf)), (2645, (.node .leaf .leaf)),
    (2731, (.node (.node .leaf .leaf) .leaf)), (2745, (.node .leaf .leaf)),
    (2759, (.node .leaf .leaf)), (2773, (.node .leaf .leaf)), (2837, (.node .leaf .leaf)),
    (2859, (.node .leaf .leaf)), (2873, (.node .leaf .leaf)), (2887, (.node .leaf .leaf)),
    (2901, (.node .leaf .leaf)), (2987, (.node .leaf .leaf)), (3001, (.node .leaf .leaf)),
    (3015, (.node .leaf (.node .leaf .leaf))), (3029, (.node .leaf .leaf)),
    (3115, (.node .leaf .leaf)), (3129, (.node (.node .leaf .leaf) .leaf)),
    (3143, (.node .leaf .leaf)), (3157, (.node .leaf .leaf)), (3243, (.node .leaf .leaf)),
    (3257, (.node .leaf .leaf)), (3271, (.node .leaf .leaf)), (3285, (.node .leaf .leaf)),
    (3307, (.node .leaf .leaf)), (3371, (.node .leaf .leaf)), (3385, (.node .leaf .leaf)),
    (3399, (.node .leaf .leaf)), (3413, (.node .leaf (.node .leaf .leaf))),
    (3499, (.node .leaf .leaf)), (3513, (.node .leaf .leaf)),
    (3527, (.node .leaf (.node .leaf .leaf))), (3541, (.node .leaf .leaf)),
    (3627, (.node .leaf .leaf)), (3641, (.node (.node .leaf .leaf) .leaf)),
    (3655, (.node .leaf .leaf)), (3669, (.node .leaf .leaf)), (3755, (.node .leaf .leaf)),
    (3769, (.node .leaf .leaf)), (3783, (.node .leaf .leaf)), (3797, (.node .leaf .leaf)),
    (3861, (.node .leaf .leaf)), (3883, (.node .leaf .leaf)), (3897, (.node .leaf .leaf)),
    (3911, (.node .leaf .leaf)), (3925, (.node .leaf .leaf)), (4011, (.node .leaf .leaf)),
    (4025, (.node .leaf .leaf)), (4039, (.node .leaf (.node .leaf .leaf))),
    (4053, (.node .leaf .leaf))]

/-- The shape of `m` for `ω = 1`. -/
def shapeOne (m : ℕ) : Shape := shapeOf dfltOne excOne m

/-- The check of the cell `(0, 0)` at `ω = 1` holds for every odd `m < 2^{12}` with
`m ≡ 1 (mod 8)` whose shape has the accepted cell `(0, 0)`. -/
theorem cellCheck_one_0_0_1 :
    cellCheck 1 4 4595457 1310720000 13914696624920517488 0 0
      (mList 4 3 1 (0, 0) dfltOne excOne) = true := by
  decide +kernel

/-- The check of the cell `(0, 0)` at `ω = 1` holds for every odd `m < 2^{12}` with
`m ≡ 3 (mod 8)` whose shape has the accepted cell `(0, 0)`. -/
theorem cellCheck_one_0_0_3 :
    cellCheck 1 4 4595457 1310720000 13914696624920517488 0 0
      (mList 4 3 3 (0, 0) dfltOne excOne) = true := by
  decide +kernel

/-- The check of the cell `(0, 0)` at `ω = 1` holds for every odd `m < 2^{12}` with
`m ≡ 5 (mod 8)` whose shape has the accepted cell `(0, 0)`. -/
theorem cellCheck_one_0_0_5 :
    cellCheck 1 4 4595457 1310720000 13914696624920517488 0 0
      (mList 4 3 5 (0, 0) dfltOne excOne) = true := by
  decide +kernel

/-- The check of the cell `(0, 0)` at `ω = 1` holds for every odd `m < 2^{12}` with
`m ≡ 7 (mod 8)` whose shape has the accepted cell `(0, 0)`. -/
theorem cellCheck_one_0_0_7 :
    cellCheck 1 4 4595457 1310720000 13914696624920517488 0 0
      (mList 4 3 7 (0, 0) dfltOne excOne) = true := by
  decide +kernel

/-- The check of the cell `(1, 0)` at `ω = 1` holds for every odd `m < 2^{12}` whose shape has the
accepted cell `(1, 0)`. -/
theorem cellCheck_one_1_0 :
    cellCheck 1 4 4595457 1310720000 13914696624920517488 1 0
      (mList 4 1 1 (1, 0) dfltOne excOne) = true := by
  decide +kernel

/-- The check of the cell `(1, 1)` at `ω = 1` holds for every odd `m < 2^{12}` whose shape has the
accepted cell `(1, 1)`. -/
theorem cellCheck_one_1_1 :
    cellCheck 1 4 4595457 1310720000 13914696624920517488 1 1
      (mList 4 1 1 (1, 1) dfltOne excOne) = true := by
  decide +kernel

/-- The check of the cell `(2, 0)` at `ω = 1` holds for every odd `m < 2^{12}` whose shape has the
accepted cell `(2, 0)`. -/
theorem cellCheck_one_2_0 :
    cellCheck 1 4 4595457 1310720000 13914696624920517488 2 0
      (mList 4 1 1 (2, 0) dfltOne excOne) = true := by
  decide +kernel

/-- The check of the cell `(2, 1)` at `ω = 1` holds for every odd `m < 2^{12}` whose shape has the
accepted cell `(2, 1)`. -/
theorem cellCheck_one_2_1 :
    cellCheck 1 4 4595457 1310720000 13914696624920517488 2 1
      (mList 4 1 1 (2, 1) dfltOne excOne) = true := by
  decide +kernel

/-- The check of the cell `(2, 2)` at `ω = 1` holds for every odd `m < 2^{12}` whose shape has the
accepted cell `(2, 2)`. -/
theorem cellCheck_one_2_2 :
    cellCheck 1 4 4595457 1310720000 13914696624920517488 2 2
      (mList 4 1 1 (2, 2) dfltOne excOne) = true := by
  decide +kernel

/-- The check of the cell `(2, 3)` at `ω = 1` holds for every odd `m < 2^{12}` whose shape has the
accepted cell `(2, 3)`. -/
theorem cellCheck_one_2_3 :
    cellCheck 1 4 4595457 1310720000 13914696624920517488 2 3
      (mList 4 1 1 (2, 3) dfltOne excOne) = true := by
  decide +kernel

/-- The Lipschitz bound for `(ω, p) = (1, 4)`. -/
theorem lipB_one : lipB 5 6 0 0 = 13914696624920517488 := by
  decide +kernel

/-- **The cells at `ω = 1`.** For every odd `m < 2^{12}`, every accepted cell of the shape
of `m` is good. -/
theorem cellGood_one : ∀ m : ℕ, m % 2 = 1 → m < 2 ^ (4 + 8) →
    ∀ q ∈ (shapeOne m).leaves 0 0, CellGood 1 4 q.1 q.2 m := by
  intro m hodd hlt q hq
  have hT : trTailGain 1 8 = ((4595457 : ℕ) : ℝ) / ((1310720000 : ℕ) : ℝ) := by
    rw [trTailGain_one_eight]
    norm_num
  have hL : trTreeLip (fun _ => 8) (allPolicy (1 + 4)) 0 0 ≤
      ((13914696624920517488 : ℕ) : ℝ) / one := by
    have := trTreeLip_allPolicy_le (1 + 4) 6 0 0 (by norm_num)
    rwa [lipB_one] at this
  have key : ∀ (a ρ : ℕ) (q : ℕ × ℕ), a ≤ 4 + 8 →
      cellCheck 1 4 4595457 1310720000 13914696624920517488 q.1 q.2
        (mList 4 a ρ q dfltOne excOne) = true →
      1 ≤ ρ → m % 2 ^ a = ρ → q ∈ (shapeOne m).leaves 0 0 → CellGood 1 4 q.1 q.2 m :=
    fun a ρ q ha hc hρ hmρ hq => cellGood_of_cellCheck (by norm_num) hT hL hc
      (fun _ h => pos_of_mem_mList hρ h) m (mem_mList ha hlt (by omega) hmρ hq)
  have hQ := mem_of_mem_leaves_shapeOf
      (Q := [(0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2), (2, 3)])
      (by decide +kernel) (by decide +kernel) hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hρlt : m % 2 ^ 3 < 8 := Nat.mod_lt _ (by norm_num)
    have hρodd : m % 2 ^ 3 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num)]
      exact hodd
    generalize hr : m % 2 ^ 3 = ρ at hρlt hρodd
    obtain rfl | rfl | rfl | rfl
      : ρ = 1 ∨ ρ = 3 ∨ ρ = 5 ∨ ρ = 7 := by omega
    · exact key 3 1 (0, 0) (by norm_num) cellCheck_one_0_0_1 (by norm_num) hr hq
    · exact key 3 3 (0, 0) (by norm_num) cellCheck_one_0_0_3 (by norm_num) hr hq
    · exact key 3 5 (0, 0) (by norm_num) cellCheck_one_0_0_5 (by norm_num) hr hq
    · exact key 3 7 (0, 0) (by norm_num) cellCheck_one_0_0_7 (by norm_num) hr hq
  · exact key 1 1 (1, 0) (by norm_num) cellCheck_one_1_0 (by norm_num) hodd hq
  · exact key 1 1 (1, 1) (by norm_num) cellCheck_one_1_1 (by norm_num) hodd hq
  · exact key 1 1 (2, 0) (by norm_num) cellCheck_one_2_0 (by norm_num) hodd hq
  · exact key 1 1 (2, 1) (by norm_num) cellCheck_one_2_1 (by norm_num) hodd hq
  · exact key 1 1 (2, 2) (by norm_num) cellCheck_one_2_2 (by norm_num) hodd hq
  · exact key 1 1 (2, 3) (by norm_num) cellCheck_one_2_3 (by norm_num) hodd hq

end TrDirectCertificate

end CollatzPosDens
