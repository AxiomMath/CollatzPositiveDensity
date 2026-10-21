/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Seed.S05OfflawCert
public import CollatzPosDens.Seed.S05JointCertExistsGrid
public import CollatzPosDens.Seed.S05JointCertExistsGData1
public import CollatzPosDens.Seed.S05JointCertExistsGData2

/-!
# The offset-law table of the joint certificate and its checker

This file defines an explicit offset-law table `g = (g_0, …, g_6198)`, and a Boolean checker
whose value `true` on a range of grid indices implies, on that range, the monotonicity condition
and the sub-fixed-point inequality defining `CollatzPosDens.IsOfflawCert`.

Write `n_k = 512 ξ_k` and `p = 2^a n_k - 512`, so that `y_{k,a} = p / 1536`. A natural number
`j` is a *verified index* of `p` if `j ≤ 6198`, `3 n_j ≤ p ≤ 3 n_6198` and either `j = 6198` or
`p < 3 n_{j+1}`; then `j = ι(y_{k,a})` and `c_g(k,a) = ⌊2^{-a} g_j⌋`. For a grid index `k` the
checker evaluates the lower bound
$$\underline c(k,a) \le c_g(k,a), \qquad 1 \le a \le 60,$$
which agrees with `c_g(k,a)` when `y_{k,a} < 0` or `y_{k,a} > ξ_6198`, and in the remaining
case reads `g` at a *claimed* index `j` of `p`: it is `⌊2^{-a} g_j⌋` if `j` is verified, and `0`
otherwise. A wrong claim therefore only lowers the bound, so the claimed index may be produced
by any procedure. The sub-fixed-point inequality at `k` follows from `g_k ≤ ⌊2^62 𝖦₀(ξ_k)⌋` or
`g_k ≤ ∑_{a=1}^{60} \underline c(k,a)`.

## Main definitions

* `CollatzPosDens.jointCertG`: the offset-law table `g : Fin 6199 → ℕ`.
* `CollatzPosDens.jointCertIndexOK p j`: `j` is a verified index of `p`.
* `CollatzPosDens.jointCertGuessIndex p`: a claimed index of `p`, by bisection.
* `CollatzPosDens.jointCertGContribAt k a j`: the lower bound `\underline c(k,a)` with the
  claimed index `j`.
* `CollatzPosDens.jointCertGSumFrom k m a j`: the sum of the lower bounds over `a ≤ a' < a + m`,
  each claimed index computed from the previous one.
* `CollatzPosDens.jointCertGCheckRange lo n`: the checker on the indices `lo ≤ k < lo + n`.

## Main results

* `CollatzPosDens.jointCertIndexOK_spec`: what a verified index satisfies.
* `CollatzPosDens.jointCertGContribAt_le`: `\underline c(k,a) ≤ c_g(k,a)`, for every claimed
  index.
* `CollatzPosDens.le_succ_of_jointCertGCheckAt`, `CollatzPosDens.le_max_of_jointCertGCheckAt`:
  monotonicity and the sub-fixed-point inequality at a checked index.
* `CollatzPosDens.isOfflawCert_jointCertG_of_rangeOK`: if every index passes the checker, then
  `g` is an offset-law certificate.

## Implementation notes

For `a = 1, 2, …` the numbers `p = 2^a n_k - 512` double (`p_{a+1} = 2 p_a + 512`), and on the
geometric part of the grid, of ratio `65/64`, doubling moves the index by `44` or `45`
(`log_{65/64} 2 = 44.7…`). The claimed index at `a + 1` is therefore the claimed index at `a`
plus `45`, or plus `44`, whichever is verified (four reads of the grid), and only if neither is,
`min (p / 3, 4096)` on the linear part of the grid (`p < 3 n_4097 = 12480`) or the result of `12`
bisection steps on `[4096, 6199)`. The grid numerators are read from the table
`CollatzPosDens.jointCertGridTab`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-! ### The table -/

/-- The `6199` entries of the offset-law table in the `25` blocks of `256` entries, each packed
with `64`-bit lanes. -/
def jointCertGBlocks : List ℕ :=
  [jointCertGBlock0, jointCertGBlock1, jointCertGBlock2, jointCertGBlock3, jointCertGBlock4,
    jointCertGBlock5, jointCertGBlock6, jointCertGBlock7, jointCertGBlock8, jointCertGBlock9,
    jointCertGBlock10, jointCertGBlock11, jointCertGBlock12, jointCertGBlock13, jointCertGBlock14,
    jointCertGBlock15, jointCertGBlock16, jointCertGBlock17, jointCertGBlock18, jointCertGBlock19,
    jointCertGBlock20, jointCertGBlock21, jointCertGBlock22, jointCertGBlock23, jointCertGBlock24]

/-- The entry `g_j` of the offset-law table (`j ≤ 6198`). -/
def jointCertGTab (j : ℕ) : ℕ :=
  jointCertBlockLane 64 jointCertGBlocks j

/-- The offset-law table `g = (g_0, …, g_6198)` of the joint certificate. -/
def jointCertG (k : Fin 6199) : ℕ :=
  jointCertGTab k

/-- `g_384 = 997765252056324269`, so that `2^{-62} g_384 = 0.21635…`. -/
theorem jointCertG_384 : jointCertG 384 = 997765252056324269 := by
  decide +kernel

/-- `g_6198 = 4611686018427359570 = ⌊2^62 𝖦₀(ξ_6198)⌋`. -/
theorem jointCertG_6198 : jointCertG 6198 = 4611686018427359570 := by
  decide +kernel

/-! ### Verified and claimed indices -/

/-- `j` is a verified index of `p`: `j ≤ 6198`, `3 n_j ≤ p ≤ 3 n_6198`, and `j = 6198` or
`p < 3 n_{j+1}`, with the grid numerators read from the table. -/
def jointCertIndexOK (p j : ℕ) : Bool :=
  Nat.ble j 6198 && Nat.ble (3 * jointCertGridTab j) p && Nat.ble p (3 * 583351470707564294) &&
    (Nat.beq j 6198 || Nat.blt p (3 * jointCertGridTab (j + 1)))

/-- A verified index satisfies the hypotheses of `offlawContrib_of_index`. -/
theorem jointCertIndexOK_spec {p j : ℕ} (h : jointCertIndexOK p j = true) :
    j < 6199 ∧ 3 * offlawGridNum j ≤ p ∧ p ≤ 3 * 583351470707564294 ∧
      (j = 6198 ∨ p < 3 * offlawGridNum (j + 1)) := by
  simp only [jointCertIndexOK, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.beq_eq,
    Nat.blt_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [jointCertGridTab_eq (by omega)] at h2
  refine ⟨by omega, h2, h3, ?_⟩
  rcases h4 with h4 | h4
  · exact Or.inl h4
  · rcases Nat.lt_or_ge j 6198 with hj | hj
    · exact Or.inr (by rwa [jointCertGridTab_eq (by omega)] at h4)
    · exact Or.inl (by omega)

/-- Bisection for the grid index of `p / 1536` in `[lo, hi)`: `f` steps, each replacing `lo` by
the midpoint `m` if `3 n_m ≤ p` and `hi` by `m` otherwise; the result is the final `lo`. -/
def jointCertIndexSearch (p f : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun lo _ => lo)
    (fun _ ih lo hi =>
      cond (Nat.ble (3 * jointCertGridTab ((lo + hi) / 2)) p) (ih ((lo + hi) / 2) hi)
        (ih lo ((lo + hi) / 2))) f

/-- A claimed grid index of `p / 1536`: `min (p / 3, 4096)` for `p < 12480`, and otherwise the
result of `12` bisection steps on the geometric part `[4096, 6199)` of the grid. -/
def jointCertGuessIndex (p : ℕ) : ℕ :=
  cond (Nat.blt p 12480) (min (p / 3) 4096) (jointCertIndexSearch p 12 4096 6199)

/-! ### The lower bound of the contributions -/

/-- The lower bound `\underline c(k,a)` of `c_g(k,a)` for the table `g = jointCertG`, with a
claimed index `j`: it is `c_g(k,a)` when `y_{k,a} < 0` or `y_{k,a} > ξ_6198`, and `⌊2^{-a} g_j⌋`
if `j` is a verified index of `p = 2^a n_k - 512` (and `0` otherwise) in the remaining case. -/
def jointCertGContribAt (k a j : ℕ) : ℕ :=
  cond (Nat.blt (2 ^ a * jointCertGridTab k) 512) 0 <|
  cond (Nat.blt (3 * 583351470707564294) (2 ^ a * jointCertGridTab k - 512))
    (offlawFloorNum 62 (2 ^ a * jointCertGridTab k - 512) 1536 / 2 ^ a) <|
  cond (jointCertIndexOK (2 ^ a * jointCertGridTab k - 512) j) (jointCertGTab j / 2 ^ a) 0

/-- The lower bound is at most the contribution, whatever the claimed index:
`\underline c(k,a) ≤ c_g(k,a)`. -/
theorem jointCertGContribAt_le {k : ℕ} (hk : k < 6199) (a j : ℕ) :
    jointCertGContribAt k a j ≤ offlawContrib jointCertG k a := by
  rw [jointCertGContribAt, jointCertGridTab_eq (by omega)]
  generalize hP : 2 ^ a * offlawGridNum k = P
  by_cases h0 : P < 512
  · rw [show Nat.blt P 512 = true from Nat.blt_eq ▸ h0, Bool.cond_true]
    exact Nat.zero_le _
  rw [show Nat.blt P 512 = false from by rw [← Bool.not_eq_true, Nat.blt_eq]; exact h0,
    Bool.cond_false]
  by_cases h1 : 3 * 583351470707564294 < P - 512
  · rw [show Nat.blt (3 * 583351470707564294) (P - 512) = true from Nat.blt_eq ▸ h1,
      Bool.cond_true]
    subst hP
    simp [offlawContrib, h0, h1]
  rw [show Nat.blt (3 * 583351470707564294) (P - 512) = false from by
    rw [← Bool.not_eq_true, Nat.blt_eq]; exact h1, Bool.cond_false]
  cases h2 : jointCertIndexOK (P - 512) j
  · exact Nat.zero_le _
  · obtain ⟨hj, hj1, hj2, hj3⟩ := jointCertIndexOK_spec h2
    subst hP
    exact (offlawContrib_of_index jointCertG ⟨j, hj⟩ (by omega) hj1 hj2 hj3).symm.le

/-- A claimed index of `p = 2 p' + 512`, from a claimed index `j'` of `p'`: on the geometric part
of the grid the ratio `65/64` gives `log_{65/64} 2 = 44.7…`, so `j' + 45` and then `j' + 44` are
tried, and `jointCertGuessIndex p` is the claim if neither is verified. -/
def jointCertNextIndex (p j' : ℕ) : ℕ :=
  cond (jointCertIndexOK p (Nat.add j' 45)) (Nat.add j' 45)
    (cond (jointCertIndexOK p (Nat.add j' 44)) (Nat.add j' 44) (jointCertGuessIndex p))

/-- The claimed index at `(k, a)`, from the claimed index `j` at `(k, a - 1)`: `0` (no claim is
read) when `p = 2^a n_k - 512` exceeds `3 n_6198`, and `jointCertNextIndex p j` otherwise. -/
def jointCertClaim (k a j : ℕ) : ℕ :=
  cond (Nat.blt (3 * 583351470707564294) (2 ^ a * jointCertGridTab k - 512)) 0
    (jointCertNextIndex (2 ^ a * jointCertGridTab k - 512) j)

/-- The sum `∑_{a'=a}^{a+m-1} \underline c(k,a')` with the claimed indices `jointCertClaim`,
starting from the claimed index `j` at `a - 1`, by a recursion that the kernel evaluates
directly. -/
def jointCertGSumFrom (k m : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0)
    (fun _ ih a j => Nat.add (jointCertGContribAt k a (jointCertClaim k a j))
      (ih (Nat.add a 1) (jointCertClaim k a j))) m

/-- `jointCertGSumFrom k (m + 1) a j` is the lower bound at `a`, with the claimed index
`jointCertClaim k a j`, plus `jointCertGSumFrom k m (a + 1)` started from that index. -/
theorem jointCertGSumFrom_succ (k m a j : ℕ) :
    jointCertGSumFrom k (m + 1) a j = jointCertGContribAt k a (jointCertClaim k a j) +
      jointCertGSumFrom k m (a + 1) (jointCertClaim k a j) :=
  rfl

/-- The summed lower bound is at most the sum of the contributions. -/
theorem jointCertGSumFrom_le {k : ℕ} (hk : k < 6199) :
    ∀ m a j, jointCertGSumFrom k m a j ≤ ∑ i ∈ range m, offlawContrib jointCertG k (a + i)
  | 0, _, _ => Nat.zero_le _
  | m + 1, a, j => by
    rw [jointCertGSumFrom_succ, Finset.sum_range_succ', add_zero, add_comm]
    have h1 := jointCertGContribAt_le hk a (jointCertClaim k a j)
    have h2 := jointCertGSumFrom_le hk m (a + 1) (jointCertClaim k a j)
    have h3 : ∑ i ∈ range m, offlawContrib jointCertG k (a + 1 + i) =
        ∑ i ∈ range m, offlawContrib jointCertG k (a + (i + 1)) :=
      Finset.sum_congr rfl fun i _ => by rw [Nat.add_right_comm, Nat.add_assoc]
    omega

/-- The summed lower bound over `1 ≤ a ≤ 60` is at most `∑_{a=1}^{60} c_g(k,a)`. -/
theorem jointCertGSumFrom_le_Icc {k : ℕ} (hk : k < 6199) :
    jointCertGSumFrom k 60 1 0 ≤ ∑ a ∈ Icc 1 60, offlawContrib jointCertG k a := by
  refine (jointCertGSumFrom_le hk 60 1 0).trans (le_of_eq ?_)
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]

/-! ### The checker -/

/-- The checker at the index `k`: `g_k ≤ g_{k+1}` unless `k = 6198`, and
`g_k ≤ ⌊2^62 𝖦₀(ξ_k)⌋` or `g_k ≤ ∑_{a=1}^{60} \underline c(k,a)`. -/
def jointCertGCheckAt (k : ℕ) : Bool :=
  (Nat.beq k 6198 || Nat.ble (jointCertGTab k) (jointCertGTab (k + 1))) &&
    (Nat.ble (jointCertGTab k) (offlawFloorNum 62 (jointCertGridTab k) 512) ||
      Nat.ble (jointCertGTab k) (jointCertGSumFrom k 60 1 0))

/-- The checker on the indices `lo ≤ k < lo + n`. -/
def jointCertGCheckRange (lo n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih k => jointCertGCheckAt k && ih (k + 1)) n lo

/-- A checked range gives the checker at each of its indices. -/
theorem jointCertGCheckAt_of_checkRange :
    ∀ {n lo : ℕ}, jointCertGCheckRange lo n = true →
      ∀ k, lo ≤ k → k < lo + n → jointCertGCheckAt k = true
  | 0, _, _, k, h1, h2 => absurd h2 (by omega)
  | n + 1, lo, h, k, h1, h2 => by
    change (jointCertGCheckAt lo && jointCertGCheckRange (lo + 1) n) = true at h
    rw [Bool.and_eq_true] at h
    rcases h1.eq_or_lt with rfl | h1
    · exact h.1
    · exact jointCertGCheckAt_of_checkRange h.2 k h1 (by omega)

/-- Condition (i) on a checked index: `g_k ≤ g_{k+1}` for `k < 6198`. -/
theorem le_succ_of_jointCertGCheckAt {k : ℕ} (h : jointCertGCheckAt k = true) (hk : k < 6198) :
    jointCertGTab k ≤ jointCertGTab (k + 1) := by
  simp only [jointCertGCheckAt, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq,
    Nat.ble_eq] at h
  exact h.1.resolve_left (by omega)

/-- Condition (ii) on a checked index:
`g_k ≤ max(⌊2^62 𝖦₀(ξ_k)⌋, ∑_{a=1}^{60} c_g(k,a))`, with the floor as a natural-number
quotient. -/
theorem le_max_of_jointCertGCheckAt {k : ℕ} (h : jointCertGCheckAt k = true) (hk : k < 6199) :
    jointCertGTab k ≤ max (offlawFloorNum 62 (offlawGridNum k) 512)
      (∑ a ∈ Icc 1 60, offlawContrib jointCertG k a) := by
  simp only [jointCertGCheckAt, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at h
  rw [← jointCertGridTab_eq (by omega)]
  rcases h.2 with h2 | h2
  · exact le_max_of_le_left h2
  · exact le_max_of_le_right (h2.trans (jointCertGSumFrom_le_Icc hk))

/-- Every index `lo ≤ k < hi` passes the checker. -/
def JointCertGRangeOK (lo hi : ℕ) : Prop :=
  ∀ k, lo ≤ k → k < hi → jointCertGCheckAt k = true

/-- A passed range check covers its indices. -/
theorem jointCertGRangeOK_of_checkRange {lo n : ℕ} (h : jointCertGCheckRange lo n = true) :
    JointCertGRangeOK lo (lo + n) :=
  jointCertGCheckAt_of_checkRange h

/-- Checked ranges of indices concatenate. -/
theorem JointCertGRangeOK.trans {a b c : ℕ} (h₁ : JointCertGRangeOK a b)
    (h₂ : JointCertGRangeOK b c) : JointCertGRangeOK a c := fun k ha hc => by
  rcases Nat.lt_or_ge k b with hb | hb
  · exact h₁ k ha hb
  · exact h₂ k hb hc

/-- If every index `k ≤ 6198` passes the checker, then `g` is an offset-law certificate. -/
theorem isOfflawCert_jointCertG_of_rangeOK (h : JointCertGRangeOK 0 6199) :
    IsOfflawCert jointCertG := by
  rw [isOfflawCert_iff]
  refine ⟨fun k => ?_, ?_, fun k => ?_⟩
  · exact le_succ_of_jointCertGCheckAt (h k (Nat.zero_le _) (by omega)) k.isLt
  · decide +kernel
  · exact le_max_of_jointCertGCheckAt (h k (Nat.zero_le _) k.isLt) k.isLt

end CollatzPosDens
