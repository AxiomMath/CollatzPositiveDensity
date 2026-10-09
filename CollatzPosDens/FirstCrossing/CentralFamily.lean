/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.FcMinOvershoot
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.FirstCrossingFinite
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.FirstCrossing.Width

/-!
# The central family `𝒞(b, K)`

For a level `b` and an overshoot bound `K`, the central family `𝒞(b, K)` is the set of words
`w` of the first-crossing family `𝒲(b, r_b, K)` satisfying a further condition depending on `b`:

* for `b ∈ {9, 10, 11}`, the overshoot is at least the minimal early overshoot,
  `A(w) ≥ H_{b,r_b}(|w|) + μ_b(|w|)`;
* for `b ≥ 256`, the length lies in the window `b - wd(b) ≤ |w| ≤ b + wd(b)` around `b`;
* for every other `b`, no further condition.

## Main definitions

* `CollatzPosDens.centralFamily`: the family `𝒞(b, K)`, as a set of words.

## Main results

* `CollatzPosDens.mem_centralFamily`: the defining membership condition.
* `CollatzPosDens.centralFamily_subset_firstCrossing`: `𝒞(b, K) ⊆ 𝒲(b, r_b, K)`.
* `CollatzPosDens.centralFamily_finite`: `𝒞(b, K)` is finite.
* `CollatzPosDens.centralFamily_eq_firstCrossing`: away from `{9, 10, 11}` and below `256`,
  `𝒞(b, K) = 𝒲(b, r_b, K)`.
* `CollatzPosDens.mem_centralFamily_of_large`: for `b ≥ 256`, membership is membership
  in `𝒲(b, r_b, K)` together with the length window.
* `CollatzPosDens.mem_centralFamily_of_small`: for `b ∈ {9, 10, 11}`, membership is
  membership in `𝒲(b, r_b, K)` together with the overshoot lower bound.
* `CollatzPosDens.centralFamily_mono`: `𝒞(b, K)` increases with `K`.

## Implementation notes

The source takes integers `b ≥ 1` and `K ≥ 0`; here both are natural numbers and `b = 0` is
allowed (it falls in the "no further condition" case). The three cases are encoded as two
implications, `b ∈ {9, 10, 11} → …` and `256 ≤ b → …`, which are never both active. The
valuation sum `A(w)` is natural-valued and is compared with the integer barrier after a cast.
The lower end `b - wd(b)` is truncated subtraction in `ℕ`; since `wd(b) < b` for `b ≥ 1`
(`CollatzPosDens.wd_lt_self`) it agrees with the integer difference. The family is a `Set`,
matching `CollatzPosDens.firstCrossing`.

## References

* [Mazur, *Collatz positive density*], §15.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The central family `𝒞(b, K)`: the words `w ∈ 𝒲(b, r_b, K)` with
`A(w) ≥ H_{b,r_b}(|w|) + μ_b(|w|)` if `b ∈ {9, 10, 11}`, and with
`b - wd(b) ≤ |w| ≤ b + wd(b)` if `b ≥ 256`. -/
@[collatz_pos_dens "def_central_family"]
noncomputable def centralFamily (b K : ℕ) : Set Word :=
  {w | w ∈ firstCrossing b (rb b) K ∧
    (b ∈ ({9, 10, 11} : Finset ℕ) →
      barrier b (rb b) w.length + fcMinOvershoot b w.length ≤ (w.valSum : ℤ)) ∧
    (256 ≤ b → b - wd b ≤ w.length ∧ w.length ≤ b + wd b)}

/-- Membership in the central family `𝒞(b, K)`. -/
theorem mem_centralFamily {b K : ℕ} {w : Word} :
    w ∈ centralFamily b K ↔ w ∈ firstCrossing b (rb b) K ∧
      (b ∈ ({9, 10, 11} : Finset ℕ) →
        barrier b (rb b) w.length + fcMinOvershoot b w.length ≤ (w.valSum : ℤ)) ∧
      (256 ≤ b → b - wd b ≤ w.length ∧ w.length ≤ b + wd b) :=
  Iff.rfl

/-- The central family is contained in the first-crossing family `𝒲(b, r_b, K)`. -/
theorem centralFamily_subset_firstCrossing (b K : ℕ) :
    centralFamily b K ⊆ firstCrossing b (rb b) K := fun _ hw => hw.1

/-- For `b ≥ 256`, `w ∈ 𝒞(b, K)` iff `w ∈ 𝒲(b, r_b, K)` and `b - wd(b) ≤ |w| ≤ b + wd(b)`. -/
theorem mem_centralFamily_of_large {b K : ℕ} (hb : 256 ≤ b) {w : Word} :
    w ∈ centralFamily b K ↔
      w ∈ firstCrossing b (rb b) K ∧ b - wd b ≤ w.length ∧ w.length ≤ b + wd b := by
  have hb' : b ∉ ({9, 10, 11} : Finset ℕ) := by simp; omega
  simp only [mem_centralFamily, hb', false_imp_iff, true_and, hb, forall_const]

/-- For `b ∈ {9, 10, 11}`, `w ∈ 𝒞(b, K)` iff `w ∈ 𝒲(b, r_b, K)` and
`A(w) ≥ H_{b,r_b}(|w|) + μ_b(|w|)`. -/
theorem mem_centralFamily_of_small {b K : ℕ} (hb : b ∈ ({9, 10, 11} : Finset ℕ)) {w : Word} :
    w ∈ centralFamily b K ↔ w ∈ firstCrossing b (rb b) K ∧
      barrier b (rb b) w.length + fcMinOvershoot b w.length ≤ (w.valSum : ℤ) := by
  have hb' : ¬ 256 ≤ b := by simp at hb; omega
  simp only [mem_centralFamily, hb, hb', false_imp_iff, and_true, forall_const]

/-- Outside `{9, 10, 11}` and below `256`, `𝒞(b, K) = 𝒲(b, r_b, K)`. -/
theorem centralFamily_eq_firstCrossing {b K : ℕ} (h1 : b ∉ ({9, 10, 11} : Finset ℕ))
    (h2 : b < 256) : centralFamily b K = firstCrossing b (rb b) K := by
  ext w
  simp only [mem_centralFamily, h1, false_imp_iff, not_le.2 h2, and_true]

/-- For `b ≥ 256`, the integer form of the lower length bound of a word of `𝒞(b, K)`. -/
theorem sub_wd_le_length_of_mem_centralFamily {b K : ℕ} (hb : 256 ≤ b) {w : Word}
    (hw : w ∈ centralFamily b K) : (b : ℤ) - wd b ≤ w.length := by
  have := (hw.2.2 hb).1
  have := wd_lt_self (show 0 < b by omega)
  omega

/-- For `b ≥ 256`, the upper length bound of a word of `𝒞(b, K)`. -/
theorem length_le_add_wd_of_mem_centralFamily {b K : ℕ} (hb : 256 ≤ b) {w : Word}
    (hw : w ∈ centralFamily b K) : w.length ≤ b + wd b :=
  (hw.2.2 hb).2

/-- The central families increase with the overshoot bound `K`. -/
theorem centralFamily_mono {b K K' : ℕ} (h : K ≤ K') :
    centralFamily b K ⊆ centralFamily b K' := fun _ hw =>
  ⟨firstCrossing_mono h hw.1, hw.2⟩

/-- The central family `𝒞(b, K)` is finite. -/
theorem centralFamily_finite (b K : ℕ) : (centralFamily b K).Finite :=
  (firstCrossing_finite _ _ _).subset (centralFamily_subset_firstCrossing _ _)

end CollatzPosDens
