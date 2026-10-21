/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDirectCertificateData6a
public import CollatzPosDens.StoppingTrace.TrDirectCertificateData6b
public import CollatzPosDens.StoppingTrace.TrTailGain

/-!
# The direct-entry certificate at `ω = 6` (part 3 of 3)

This file checks cells of the direct-entry certificate for the pair `(ω, p) = (6, 4)` (see
`CollatzPosDens.exists_trTreeCost_trWhitePolicy_sub_trTailGain_lt`). Every odd `m < 2^{12}` is
given a bisection shape (`CollatzPosDens.TrDirectCertificate.Shape`) of `[-1/3, 1/3]`: by default
the two halves of `[-1/3, 1/3]`, and for the values of `m` listed in
`CollatzPosDens.TrDirectCertificate.excSix` (here there are none) a finer one. For the accepted
cell `(1, 1)` of the default shape and each odd residue `ρ` of `m` modulo `64` with `23 ≤ ρ`,
the check `CollatzPosDens.TrDirectCertificate.cellCheck` of all the `m` concerned is carried out
by the kernel, in its own declaration.

## Main results

* `CollatzPosDens.TrDirectCertificate.cellGood_six`: every accepted cell of the shape of every
  odd `m < 2^{12}` is good.

## References

* [Mazur, *Collatz positive density*]
-/
@[expose] public section

namespace CollatzPosDens

namespace TrDirectCertificate

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 23 [MOD 64]`. -/
theorem cellCheck_six_1_1_23 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 23 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 25 [MOD 64]`. -/
theorem cellCheck_six_1_1_25 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 25 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 27 [MOD 64]`. -/
theorem cellCheck_six_1_1_27 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 27 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 29 [MOD 64]`. -/
theorem cellCheck_six_1_1_29 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 29 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 31 [MOD 64]`. -/
theorem cellCheck_six_1_1_31 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 31 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 33 [MOD 64]`. -/
theorem cellCheck_six_1_1_33 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 33 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 35 [MOD 64]`. -/
theorem cellCheck_six_1_1_35 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 35 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 37 [MOD 64]`. -/
theorem cellCheck_six_1_1_37 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 37 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 39 [MOD 64]`. -/
theorem cellCheck_six_1_1_39 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 39 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 41 [MOD 64]`. -/
theorem cellCheck_six_1_1_41 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 41 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 43 [MOD 64]`. -/
theorem cellCheck_six_1_1_43 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 43 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 45 [MOD 64]`. -/
theorem cellCheck_six_1_1_45 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 45 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 47 [MOD 64]`. -/
theorem cellCheck_six_1_1_47 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 47 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 49 [MOD 64]`. -/
theorem cellCheck_six_1_1_49 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 49 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 51 [MOD 64]`. -/
theorem cellCheck_six_1_1_51 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 51 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 53 [MOD 64]`. -/
theorem cellCheck_six_1_1_53 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 53 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 55 [MOD 64]`. -/
theorem cellCheck_six_1_1_55 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 55 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 57 [MOD 64]`. -/
theorem cellCheck_six_1_1_57 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 57 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 59 [MOD 64]`. -/
theorem cellCheck_six_1_1_59 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 59 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 61 [MOD 64]`. -/
theorem cellCheck_six_1_1_61 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 61 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The certificate check `cellCheck` at `(ω, p) = (6, 4)` succeeds on the cell `(1, 1)` for all
odd `m < 2^{12}` with `m ≡ 63 [MOD 64]`. -/
theorem cellCheck_six_1_1_63 :
    cellCheck 6 4 13575489 1638400000 23924397962358011620 1 1
      (mList 4 6 63 (1, 1) dfltSix excSix) = true := by
  decide +kernel

/-- The Lipschitz bound for `(ω, p) = (6, 4)`. -/
theorem lipB_six : lipB 10 11 0 0 = 23924397962358011620 := by
  decide +kernel

/-- **The cells at `ω = 6`.** For every odd `m < 2^{12}`, every accepted cell of the shape
of `m` is good. -/
theorem cellGood_six : ∀ m : ℕ, m % 2 = 1 → m < 2 ^ (4 + 8) →
    ∀ q ∈ (shapeSix m).leaves 0 0, CellGood 6 4 q.1 q.2 m := by
  intro m hodd hlt q hq
  have hT : trTailGain 6 8 = ((13575489 : ℕ) : ℝ) / ((1638400000 : ℕ) : ℝ) := by
    rw [trTailGain_six_eight]
    norm_num
  have hL : trTreeLip (fun _ => 8) (allPolicy (6 + 4)) 0 0 ≤
      ((23924397962358011620 : ℕ) : ℝ) / one := by
    have := trTreeLip_allPolicy_le (6 + 4) 11 0 0 (by norm_num)
    rwa [lipB_six] at this
  have key : ∀ (a ρ : ℕ) (q : ℕ × ℕ), a ≤ 4 + 8 →
      cellCheck 6 4 13575489 1638400000 23924397962358011620 q.1 q.2
        (mList 4 a ρ q dfltSix excSix) = true →
      1 ≤ ρ → m % 2 ^ a = ρ → q ∈ (shapeSix m).leaves 0 0 → CellGood 6 4 q.1 q.2 m :=
    fun a ρ q ha hc hρ hmρ hq => cellGood_of_cellCheck (by norm_num) hT hL hc
      (fun _ h => pos_of_mem_mList hρ h) m (mem_mList ha hlt (by omega) hmρ hq)
  have hQ := mem_of_mem_leaves_shapeOf
      (Q := [(1, 0), (1, 1)])
      (by decide +kernel) (by decide +kernel) hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hQ
  rcases hQ with rfl | rfl
  · have hρlt : m % 2 ^ 6 < 64 := Nat.mod_lt _ (by norm_num)
    have hρodd : m % 2 ^ 6 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num)]
      exact hodd
    generalize hr : m % 2 ^ 6 = ρ at hρlt hρodd
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
      : ρ = 1 ∨ ρ = 3 ∨ ρ = 5 ∨ ρ = 7 ∨ ρ = 9 ∨ ρ = 11 ∨ ρ = 13 ∨ ρ = 15 ∨ ρ = 17 ∨ ρ = 19 ∨
        ρ = 21 ∨ ρ = 23 ∨ ρ = 25 ∨ ρ = 27 ∨ ρ = 29 ∨ ρ = 31 ∨ ρ = 33 ∨ ρ = 35 ∨ ρ = 37 ∨ ρ = 39 ∨
        ρ = 41 ∨ ρ = 43 ∨ ρ = 45 ∨ ρ = 47 ∨ ρ = 49 ∨ ρ = 51 ∨ ρ = 53 ∨ ρ = 55 ∨ ρ = 57 ∨ ρ = 59 ∨
        ρ = 61 ∨ ρ = 63 := by omega
    · exact key 6 1 (1, 0) (by norm_num) cellCheck_six_1_0_1 (by norm_num) hr hq
    · exact key 6 3 (1, 0) (by norm_num) cellCheck_six_1_0_3 (by norm_num) hr hq
    · exact key 6 5 (1, 0) (by norm_num) cellCheck_six_1_0_5 (by norm_num) hr hq
    · exact key 6 7 (1, 0) (by norm_num) cellCheck_six_1_0_7 (by norm_num) hr hq
    · exact key 6 9 (1, 0) (by norm_num) cellCheck_six_1_0_9 (by norm_num) hr hq
    · exact key 6 11 (1, 0) (by norm_num) cellCheck_six_1_0_11 (by norm_num) hr hq
    · exact key 6 13 (1, 0) (by norm_num) cellCheck_six_1_0_13 (by norm_num) hr hq
    · exact key 6 15 (1, 0) (by norm_num) cellCheck_six_1_0_15 (by norm_num) hr hq
    · exact key 6 17 (1, 0) (by norm_num) cellCheck_six_1_0_17 (by norm_num) hr hq
    · exact key 6 19 (1, 0) (by norm_num) cellCheck_six_1_0_19 (by norm_num) hr hq
    · exact key 6 21 (1, 0) (by norm_num) cellCheck_six_1_0_21 (by norm_num) hr hq
    · exact key 6 23 (1, 0) (by norm_num) cellCheck_six_1_0_23 (by norm_num) hr hq
    · exact key 6 25 (1, 0) (by norm_num) cellCheck_six_1_0_25 (by norm_num) hr hq
    · exact key 6 27 (1, 0) (by norm_num) cellCheck_six_1_0_27 (by norm_num) hr hq
    · exact key 6 29 (1, 0) (by norm_num) cellCheck_six_1_0_29 (by norm_num) hr hq
    · exact key 6 31 (1, 0) (by norm_num) cellCheck_six_1_0_31 (by norm_num) hr hq
    · exact key 6 33 (1, 0) (by norm_num) cellCheck_six_1_0_33 (by norm_num) hr hq
    · exact key 6 35 (1, 0) (by norm_num) cellCheck_six_1_0_35 (by norm_num) hr hq
    · exact key 6 37 (1, 0) (by norm_num) cellCheck_six_1_0_37 (by norm_num) hr hq
    · exact key 6 39 (1, 0) (by norm_num) cellCheck_six_1_0_39 (by norm_num) hr hq
    · exact key 6 41 (1, 0) (by norm_num) cellCheck_six_1_0_41 (by norm_num) hr hq
    · exact key 6 43 (1, 0) (by norm_num) cellCheck_six_1_0_43 (by norm_num) hr hq
    · exact key 6 45 (1, 0) (by norm_num) cellCheck_six_1_0_45 (by norm_num) hr hq
    · exact key 6 47 (1, 0) (by norm_num) cellCheck_six_1_0_47 (by norm_num) hr hq
    · exact key 6 49 (1, 0) (by norm_num) cellCheck_six_1_0_49 (by norm_num) hr hq
    · exact key 6 51 (1, 0) (by norm_num) cellCheck_six_1_0_51 (by norm_num) hr hq
    · exact key 6 53 (1, 0) (by norm_num) cellCheck_six_1_0_53 (by norm_num) hr hq
    · exact key 6 55 (1, 0) (by norm_num) cellCheck_six_1_0_55 (by norm_num) hr hq
    · exact key 6 57 (1, 0) (by norm_num) cellCheck_six_1_0_57 (by norm_num) hr hq
    · exact key 6 59 (1, 0) (by norm_num) cellCheck_six_1_0_59 (by norm_num) hr hq
    · exact key 6 61 (1, 0) (by norm_num) cellCheck_six_1_0_61 (by norm_num) hr hq
    · exact key 6 63 (1, 0) (by norm_num) cellCheck_six_1_0_63 (by norm_num) hr hq
  · have hρlt : m % 2 ^ 6 < 64 := Nat.mod_lt _ (by norm_num)
    have hρodd : m % 2 ^ 6 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num)]
      exact hodd
    generalize hr : m % 2 ^ 6 = ρ at hρlt hρodd
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
      : ρ = 1 ∨ ρ = 3 ∨ ρ = 5 ∨ ρ = 7 ∨ ρ = 9 ∨ ρ = 11 ∨ ρ = 13 ∨ ρ = 15 ∨ ρ = 17 ∨ ρ = 19 ∨
        ρ = 21 ∨ ρ = 23 ∨ ρ = 25 ∨ ρ = 27 ∨ ρ = 29 ∨ ρ = 31 ∨ ρ = 33 ∨ ρ = 35 ∨ ρ = 37 ∨ ρ = 39 ∨
        ρ = 41 ∨ ρ = 43 ∨ ρ = 45 ∨ ρ = 47 ∨ ρ = 49 ∨ ρ = 51 ∨ ρ = 53 ∨ ρ = 55 ∨ ρ = 57 ∨ ρ = 59 ∨
        ρ = 61 ∨ ρ = 63 := by omega
    · exact key 6 1 (1, 1) (by norm_num) cellCheck_six_1_1_1 (by norm_num) hr hq
    · exact key 6 3 (1, 1) (by norm_num) cellCheck_six_1_1_3 (by norm_num) hr hq
    · exact key 6 5 (1, 1) (by norm_num) cellCheck_six_1_1_5 (by norm_num) hr hq
    · exact key 6 7 (1, 1) (by norm_num) cellCheck_six_1_1_7 (by norm_num) hr hq
    · exact key 6 9 (1, 1) (by norm_num) cellCheck_six_1_1_9 (by norm_num) hr hq
    · exact key 6 11 (1, 1) (by norm_num) cellCheck_six_1_1_11 (by norm_num) hr hq
    · exact key 6 13 (1, 1) (by norm_num) cellCheck_six_1_1_13 (by norm_num) hr hq
    · exact key 6 15 (1, 1) (by norm_num) cellCheck_six_1_1_15 (by norm_num) hr hq
    · exact key 6 17 (1, 1) (by norm_num) cellCheck_six_1_1_17 (by norm_num) hr hq
    · exact key 6 19 (1, 1) (by norm_num) cellCheck_six_1_1_19 (by norm_num) hr hq
    · exact key 6 21 (1, 1) (by norm_num) cellCheck_six_1_1_21 (by norm_num) hr hq
    · exact key 6 23 (1, 1) (by norm_num) cellCheck_six_1_1_23 (by norm_num) hr hq
    · exact key 6 25 (1, 1) (by norm_num) cellCheck_six_1_1_25 (by norm_num) hr hq
    · exact key 6 27 (1, 1) (by norm_num) cellCheck_six_1_1_27 (by norm_num) hr hq
    · exact key 6 29 (1, 1) (by norm_num) cellCheck_six_1_1_29 (by norm_num) hr hq
    · exact key 6 31 (1, 1) (by norm_num) cellCheck_six_1_1_31 (by norm_num) hr hq
    · exact key 6 33 (1, 1) (by norm_num) cellCheck_six_1_1_33 (by norm_num) hr hq
    · exact key 6 35 (1, 1) (by norm_num) cellCheck_six_1_1_35 (by norm_num) hr hq
    · exact key 6 37 (1, 1) (by norm_num) cellCheck_six_1_1_37 (by norm_num) hr hq
    · exact key 6 39 (1, 1) (by norm_num) cellCheck_six_1_1_39 (by norm_num) hr hq
    · exact key 6 41 (1, 1) (by norm_num) cellCheck_six_1_1_41 (by norm_num) hr hq
    · exact key 6 43 (1, 1) (by norm_num) cellCheck_six_1_1_43 (by norm_num) hr hq
    · exact key 6 45 (1, 1) (by norm_num) cellCheck_six_1_1_45 (by norm_num) hr hq
    · exact key 6 47 (1, 1) (by norm_num) cellCheck_six_1_1_47 (by norm_num) hr hq
    · exact key 6 49 (1, 1) (by norm_num) cellCheck_six_1_1_49 (by norm_num) hr hq
    · exact key 6 51 (1, 1) (by norm_num) cellCheck_six_1_1_51 (by norm_num) hr hq
    · exact key 6 53 (1, 1) (by norm_num) cellCheck_six_1_1_53 (by norm_num) hr hq
    · exact key 6 55 (1, 1) (by norm_num) cellCheck_six_1_1_55 (by norm_num) hr hq
    · exact key 6 57 (1, 1) (by norm_num) cellCheck_six_1_1_57 (by norm_num) hr hq
    · exact key 6 59 (1, 1) (by norm_num) cellCheck_six_1_1_59 (by norm_num) hr hq
    · exact key 6 61 (1, 1) (by norm_num) cellCheck_six_1_1_61 (by norm_num) hr hq
    · exact key 6 63 (1, 1) (by norm_num) cellCheck_six_1_1_63 (by norm_num) hr hq

end TrDirectCertificate

end CollatzPosDens
