/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Bounds.Basic
public import CollatzPosDens.Attr

/-!
# The scale increment `e_b`

For `b ∈ ℕ` the scale increment `e_b ∈ ℕ` is defined by cases. If `b ≤ 12`, then `e_b = 1`.
If `13 ≤ b ≤ 255` and the set
`{k ∈ ℕ : ⌈b/100⌉ ≤ k ≤ b, 9 · 3^b · 16^k < 4^(b+1)}`
is nonempty, then `e_b` is its largest element. Otherwise (in particular for every `b ≥ 256`),
`e_b = ⌈b/100⌉`.

## Main definitions

* `CollatzPosDens.eb`: the scale increment `e_b`.

## Main results

* `CollatzPosDens.eb_of_le_twelve`: `e_b = 1` for `b ≤ 12`.
* `CollatzPosDens.eb_isGreatest`: for `13 ≤ b ≤ 255` with the candidate set nonempty, `e_b`
  is its greatest element.
* `CollatzPosDens.eb_of_not_exists`, `CollatzPosDens.eb_of_le`: the fallback value
  `e_b = ⌈b/100⌉`, in particular for `b ≥ 256`.
* `CollatzPosDens.one_le_eb`: `1 ≤ e_b`.
* `CollatzPosDens.natCeil_div_hundred`: `⌈b/100⌉₊ = (b + 99) / 100` in any linearly ordered
  semifield with a floor, so the natural-number expression used in `eb` is the real ceiling.

## Implementation notes

The ceiling `⌈b/100⌉` of the natural number `b` is written `(b + 99) / 100` with natural
division, which agrees with `⌈(b : K) / 100⌉₊` (`natCeil_div_hundred`); this keeps `eb`
computable with decidable branches. The largest element of the candidate set is
`Nat.findGreatest` of the predicate `⌈b/100⌉ ≤ k ∧ 9 · 3^b · 16^k < 4^(b+1)` below `b`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §15.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The ceiling `⌈b/100⌉` agrees with natural division `(b + 99) / 100`. -/
theorem natCeil_div_hundred {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorSemiring K] (b : ℕ) : ⌈(b : K) / 100⌉₊ = (b + 99) / 100 := by
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ (by norm_num)]
    exact_mod_cast (by omega : b ≤ (b + 99) / 100 * 100)
  · rcases Nat.eq_zero_or_pos ((b + 99) / 100) with h | h
    · rw [h]; exact Nat.zero_le _
    · have : (b + 99) / 100 - 1 < ⌈(b : K) / 100⌉₊ := by
        rw [Nat.lt_ceil, lt_div_iff₀ (by norm_num)]
        exact_mod_cast (by omega : ((b + 99) / 100 - 1) * 100 < b)
      omega

/-- **Scale increment** `e_b`. It is `1` for `b ≤ 12`; for `13 ≤ b ≤ 255` it is the largest
`k` with `⌈b/100⌉ ≤ k ≤ b` and `9 · 3^b · 16^k < 4^(b+1)` when such a `k` exists; and it is
`⌈b/100⌉ = (b + 99) / 100` otherwise. -/
@[collatz_pos_dens "def_eb"]
def eb (b : ℕ) : ℕ :=
  if b ≤ 12 then 1
  else if b ≤ 255 ∧ ∃ k, k ≤ b ∧ (b + 99) / 100 ≤ k ∧ 9 * 3 ^ b * 16 ^ k < 4 ^ (b + 1) then
    Nat.findGreatest (fun k => (b + 99) / 100 ≤ k ∧ 9 * 3 ^ b * 16 ^ k < 4 ^ (b + 1)) b
  else (b + 99) / 100

/-- For `b ≤ 12`, `e_b = 1`. -/
theorem eb_of_le_twelve {b : ℕ} (hb : b ≤ 12) : eb b = 1 := by
  simp [eb, hb]

/-- For `13 ≤ b ≤ 255`, if the candidate set is nonempty then `e_b` is its greatest element. -/
theorem eb_isGreatest {b : ℕ} (hb₁ : 13 ≤ b) (hb₂ : b ≤ 255)
    (hne : ∃ k, (b + 99) / 100 ≤ k ∧ k ≤ b ∧ 9 * 3 ^ b * 16 ^ k < 4 ^ (b + 1)) :
    IsGreatest {k | (b + 99) / 100 ≤ k ∧ k ≤ b ∧ 9 * 3 ^ b * 16 ^ k < 4 ^ (b + 1)} (eb b) := by
  obtain ⟨k₀, hk₀, hk₀b, hk₀p⟩ := hne
  have hif : b ≤ 255 ∧ ∃ k, k ≤ b ∧ (b + 99) / 100 ≤ k ∧ 9 * 3 ^ b * 16 ^ k < 4 ^ (b + 1) :=
    ⟨hb₂, k₀, hk₀b, hk₀, hk₀p⟩
  have heq : eb b =
      Nat.findGreatest (fun k => (b + 99) / 100 ≤ k ∧ 9 * 3 ^ b * 16 ^ k < 4 ^ (b + 1)) b := by
    simp only [eb, show ¬b ≤ 12 by omega, hif, and_self, ite_true, ite_false]
  rw [heq]
  have hs := Nat.findGreatest_spec
    (P := fun k => (b + 99) / 100 ≤ k ∧ 9 * 3 ^ b * 16 ^ k < 4 ^ (b + 1)) hk₀b ⟨hk₀, hk₀p⟩
  refine ⟨⟨hs.1, Nat.findGreatest_le b, hs.2⟩, ?_⟩
  rintro k ⟨hk, hkb, hkp⟩
  exact Nat.le_findGreatest hkb ⟨hk, hkp⟩

/-- For `b ≥ 13`, if the candidate set is empty then `e_b = ⌈b/100⌉`. -/
theorem eb_of_not_exists {b : ℕ} (hb : 13 ≤ b)
    (h : ¬∃ k, (b + 99) / 100 ≤ k ∧ k ≤ b ∧ 9 * 3 ^ b * 16 ^ k < 4 ^ (b + 1)) :
    eb b = (b + 99) / 100 := by
  have hif : ¬(b ≤ 255 ∧ ∃ k, k ≤ b ∧ (b + 99) / 100 ≤ k ∧ 9 * 3 ^ b * 16 ^ k < 4 ^ (b + 1)) :=
    fun ⟨_, k, hkb, hk, hkp⟩ => h ⟨k, hk, hkb, hkp⟩
  simp only [eb, show ¬b ≤ 12 by omega, hif, ite_false]

/-- For `b ≥ 256`, `e_b = ⌈b/100⌉`. -/
theorem eb_of_le {b : ℕ} (hb : 256 ≤ b) : eb b = (b + 99) / 100 := by
  have hif : ¬(b ≤ 255 ∧ ∃ k, k ≤ b ∧ (b + 99) / 100 ≤ k ∧ 9 * 3 ^ b * 16 ^ k < 4 ^ (b + 1)) :=
    fun ⟨h, _⟩ => by omega
  simp only [eb, show ¬b ≤ 12 by omega, hif, ite_false]

/-- `1 ≤ e_b` for every `b`. -/
theorem one_le_eb (b : ℕ) : 1 ≤ eb b := by
  unfold eb
  split_ifs with h₁ h₂
  · exact le_rfl
  · obtain ⟨_, k, hkb, hk, hkp⟩ := h₂
    have hspec := Nat.findGreatest_spec
      (P := fun k => (b + 99) / 100 ≤ k ∧ 9 * 3 ^ b * 16 ^ k < 4 ^ (b + 1)) hkb ⟨hk, hkp⟩
    have : 1 ≤ (b + 99) / 100 := by omega
    exact this.trans hspec.1
  · omega

end CollatzPosDens
