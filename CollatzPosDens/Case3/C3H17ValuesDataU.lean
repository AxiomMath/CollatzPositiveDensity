/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataCosCheck
public import CollatzPosDens.Case3.C3H17CapUp
public import Mathlib.Tactic.LinearCombination

/-!
# The grid majorant `Ū_c` at the points `± 2^v 3^J / 2^17`

For `3 ≤ c ≤ 16`, `t = c - 1`, `0 ≤ v ≤ 16` and a sign `σ = ± 1`, the radicand of
`Ū_c(σ 2^v 3^J / 2^17)` is `(2 Λ - t (t - 2) 10^{18}) / (100 t^2)`, where
`Λ = ∑_{0 ≤ i < j < t} (cosI ((2^j - 2^i) σ 2^v 3^J) + 10^{18})` and every summand is the lane
`cosI (2^{v+i} 3^{J + f_{j-i}}) + 10^{18}` of the cosine table (or `2 · 10^{18}` when
`v + i ≥ 17`). For `256` consecutive values of `J` the `256` sums `Λ` are the lanes of one sum of
packed windows of the cosine table, so the values `10^8 Ū_c` at `256` consecutive points are
computed with one packed sum and `256` exact ceiling square roots.

## Main definitions

* `CollatzPosDens.C3H17Values.cosWin`: the packed window of `256` consecutive lanes of a level.
* `CollatzPosDens.C3H17Values.radSum`: the packed sum of the windows of the radicand.
* `CollatzPosDens.C3H17Values.uVal`: `10^8 Ū_c` from the sum `Λ`.
* `CollatzPosDens.C3H17Values.uBlock`: the values `10^8 Ū_c` at `256` consecutive points.
* `CollatzPosDens.C3H17Values.uSeg`: the values `10^8 Ū_c` at `n` consecutive points.

## Main results

* `CollatzPosDens.C3H17Values.uBlock_spec`: the entries of `uBlock c v a` are
  `10^8 Ū_c(σ 2^v 3^{a + k} / 2^17)`.
* `CollatzPosDens.C3H17Values.uSeg_spec`: the same for `uSeg`.
-/

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

open Finset

/-! ### Windows of the cosine table -/

/-- The lanes of level `0` (for `cosBig1`, level `1`) of the cosine table as one packed number of
width `72`. -/
noncomputable def cosBig0 : ℕ := packR (72 * 256) cosLevel0

@[inherit_doc cosBig0]
noncomputable def cosBig1 : ℕ := packR (72 * 256) cosLevel1

/-- The lanes of level `2` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig2 : ℕ := packR (72 * 256) cosLevel2

/-- The lanes of level `3` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig3 : ℕ := packR (72 * 256) cosLevel3

/-- The lanes of level `4` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig4 : ℕ := packR (72 * 256) cosLevel4

/-- The lanes of level `5` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig5 : ℕ := packR (72 * 256) cosLevel5

/-- The lanes of level `6` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig6 : ℕ := packR (72 * 256) cosLevel6

/-- The lanes of level `7` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig7 : ℕ := packR (72 * 256) cosLevel7

/-- The lanes of level `8` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig8 : ℕ := packR (72 * 256) cosLevel8

/-- The lanes of level `9` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig9 : ℕ := packR (72 * 256) cosLevel9

/-- The lanes of level `10` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig10 : ℕ := packR (72 * 256) cosLevel10

/-- The lanes of level `11` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig11 : ℕ := packR (72 * 256) cosLevel11

/-- The lanes of level `12` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig12 : ℕ := packR (72 * 256) cosLevel12

/-- The lanes of level `13` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig13 : ℕ := packR (72 * 256) cosLevel13

/-- The lanes of level `14` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig14 : ℕ := packR (72 * 256) cosLevel14

/-- The lanes of level `15` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig15 : ℕ := packR (72 * 256) cosLevel15

/-- The lanes of level `16` of the cosine table as one packed number of width `72`. -/
noncomputable def cosBig16 : ℕ := packR (72 * 256) cosLevel16

/-- The packed levels `cosBig0, …, cosBig16`. -/
noncomputable def cosBigs : List ℕ :=
  [cosBig0, cosBig1, cosBig2, cosBig3, cosBig4, cosBig5, cosBig6, cosBig7, cosBig8, cosBig9,
    cosBig10, cosBig11, cosBig12, cosBig13, cosBig14, cosBig15, cosBig16]

/-- The packed number of all lanes of level `v`. -/
noncomputable def cosBig (v : ℕ) : ℕ := getR 0 cosBigs v

/-- For `v ≤ 16`, `cosBig v` is the packing of the chunks of level `v` of the cosine table. -/
theorem cosBig_eq {v : ℕ} (hv : v ≤ 16) : cosBig v = packR (72 * 256) (cosLevels.getD v []) := by
  interval_cases v <;> rfl

/-- For `v ≤ 16` and `J < p_v + 256`, lane `J` of `cosBig v` is `cosLaneAt v J`. -/
theorem lane_cosBig {v J : ℕ} (hv : v ≤ 16) (hJ : J < cosPer v + 256) :
    lane 72 (cosBig v) J = cosLaneAt v J := by
  have h := lane_lane (w := 72) (packR (72 * 256) (cosLevels.getD v [])) (J / 256)
    (Nat.mod_lt J (show 0 < 256 by norm_num))
  rw [Nat.div_add_mod] at h
  rw [cosBig_eq hv, ← h, lane_packR]
  · rfl
  · intro i hi
    exact cosChunk_lt hv (by unfold cosNumChunks; omega)

/-- The packed window of lanes `s, …, s + 255` of level `v`. -/
noncomputable def cosWin (v s : ℕ) : ℕ := win 72 (cosBig v) s 256

/-- `2^17 ∣ 2^v (3^J - 3^{J mod p_v})`. -/
theorem two_pow_dvd_three_pow_sub {v : ℕ} (hv : v ≤ 16) (J : ℕ) :
    (2 : ℤ) ^ 17 ∣ 2 ^ v * 3 ^ J - 2 ^ v * 3 ^ (J % cosPer v) := by
  have h := three_pow_cosPer v (List.mem_range.2 (by omega))
  have hd : (2 : ℤ) ^ (17 - v) ∣ 3 ^ cosPer v - 1 := by
    have h' : ((2 : ℕ) ^ (17 - v) : ℤ) ∣ ((3 ^ cosPer v - 1 : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 (Nat.dvd_of_mod_eq_zero h)
    push_cast [Nat.one_le_pow _ _ (by norm_num : 0 < 3)] at h'
    exact h'
  have h3 : (3 : ℤ) ^ J = 3 ^ (J % cosPer v) * (3 ^ cosPer v) ^ (J / cosPer v) := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  have hd' : (2 : ℤ) ^ (17 - v) ∣ 3 ^ J - 3 ^ (J % cosPer v) := by
    rw [show (3 : ℤ) ^ J - 3 ^ (J % cosPer v) =
        3 ^ (J % cosPer v) * ((3 ^ cosPer v) ^ (J / cosPer v) - 1) by rw [h3]; ring]
    exact dvd_mul_of_dvd_right (dvd_trans hd (sub_one_dvd_pow_sub_one _ _)) _
  rw [← mul_sub, show (2 : ℤ) ^ 17 = 2 ^ v * 2 ^ (17 - v) by rw [← pow_add]; congr 1; omega]
  exact mul_dvd_mul_left _ hd'

/-- For `s < p_v`, `k < 256` and `J ≡ s + k (mod p_v)`, the lane `cosLaneAt v (s + k)` is
`cosI (2^v 3^J) + 10^{18}`. -/
theorem cosLaneAt_eq_of_lt {v s k : ℕ} (hv : v ≤ 16) (hs : s < cosPer v) (hk : k < 256) (J : ℕ)
    (hJ : J % cosPer v = (s + k) % cosPer v) :
    (cosLaneAt v (s + k) : ℤ) = cosI (2 ^ v * 3 ^ J) + 10 ^ 18 := by
  rw [(cosLaneAt_spec hv (by omega)).1, cosI_two_pow_mul_three_pow_mod hv (s + k),
    cosI_two_pow_mul_three_pow_mod hv J, hJ]

/-! ### The radicand as a packed sum -/

/-- The packed window of pair `(i, j)` for the points `2^v 3^{a + k}`, `k < 256`. -/
noncomputable def radTerm (v a j i : ℕ) : ℕ :=
  if v + i ≤ 16 then cosWin (v + i) ((a + mulExp (j - i)) % cosPer (v + i)) else 0

/-- The packed sum `∑_{j < t} ∑_{i < j}` of the windows of the radicand. -/
noncomputable def radSum (t v a : ℕ) : ℕ := ∑ j ∈ range t, ∑ i ∈ range j, radTerm v a j i

/-- The number of pairs `i < j < t` with `v + i ≥ 17`, whose cosine bound is `1`. -/
def radBig (t v : ℕ) : ℕ := ∑ j ∈ range t, ∑ i ∈ range j, if v + i ≤ 16 then 0 else 1

/-- Lane `k < 256` of `radTerm v a j i` is the lane `(a + f_{j-i}) mod p_{v+i} + k` of level
`v + i` of the cosine table when `v + i ≤ 16`, and `0` otherwise. -/
theorem lane_radTerm {v a j i k : ℕ} (hk : k < 256) :
    lane 72 (radTerm v a j i) k = if v + i ≤ 16 then
      cosLaneAt (v + i) ((a + mulExp (j - i)) % cosPer (v + i) + k) else 0 := by
  unfold radTerm
  split_ifs with h
  · rw [cosWin, win_eq_packF, lane_packF (fun _ _ => lane_lt _ _ _) hk]
    exact lane_cosBig (by omega)
      (by have := Nat.mod_lt (a + mulExp (j - i)) (cosPer_pos (v + i)); omega)
  · simp [lane]

/-- Every lane `k < 256` of `radTerm v a j i` is less than `2^62`. -/
theorem lane_radTerm_lt {v a j i k : ℕ} (hk : k < 256) :
    lane 72 (radTerm v a j i) k < 2 ^ 62 := by
  rw [lane_radTerm hk]
  split_ifs with h
  · have := Nat.mod_lt (a + mulExp (j - i)) (cosPer_pos (v + i))
    exact (cosLaneAt_spec (by omega) (by omega)).2
  · norm_num

/-- `radTerm v a j i` has at most `256` lanes of width `72`. -/
theorem radTerm_lt (v a j i : ℕ) : radTerm v a j i < 2 ^ (72 * 256) := by
  unfold radTerm
  split_ifs
  · exact Nat.mod_lt _ (by positivity)
  · positivity

/-- For `t ≤ 15`, lane `k < 256` of `radSum t v a` is the sum of the lanes `k` of the terms
`radTerm v a j i`, `i < j < t`. -/
theorem lane_radSum {t v a k : ℕ} (ht : t ≤ 15) (hk : k < 256) :
    lane 72 (radSum t v a) k = ∑ j ∈ range t, ∑ i ∈ range j, lane 72 (radTerm v a j i) k := by
  have hw : ∀ j i, radTerm v a j i = packF 72 256 (fun m => lane 72 (radTerm v a j i) m) := by
    intro j i
    have := win_eq_packF 72 (radTerm v a j i) 0 256
    rw [win, Nat.shiftRight_zero, Nat.mod_eq_of_lt (radTerm_lt v a j i)] at this
    simpa using this
  have hsum : radSum t v a = packF 72 256 (fun m =>
      ∑ j ∈ range t, ∑ i ∈ range j, lane 72 (radTerm v a j i) m) := by
    rw [radSum, ← sum_packF]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_packF]
    exact sum_congr rfl fun i _ => hw j i
  rw [hsum, lane_packF _ hk]
  intro m hm
  calc ∑ j ∈ range t, ∑ i ∈ range j, lane 72 (radTerm v a j i) m
      ≤ ∑ j ∈ range t, ∑ _i ∈ range j, 2 ^ 62 :=
        sum_le_sum fun j _ => sum_le_sum fun i _ => (lane_radTerm_lt hm).le
    _ = (∑ j ∈ range t, j) * 2 ^ 62 := by simp [sum_mul]
    _ ≤ (∑ j ∈ range 15, j) * 2 ^ 62 :=
        Nat.mul_le_mul_right _ (sum_le_sum_of_subset (range_subset_range.2 ht))
    _ < 2 ^ 72 := by norm_num [sum_range_succ]

/-- `mulExp`, by a recursion that the kernel evaluates directly. -/
noncomputable def mulExpR (m : ℕ) : ℕ :=
  getR 0 [0, 0, 1, 1198, 15628, 11480, 1200, 13664, 6848, 30080, 27392, 22016, 11264, 22528, 12288]
    m

/-- `mulExpR` agrees with `mulExp`. -/
theorem mulExpR_eq (m : ℕ) : mulExpR m = mulExp m := by
  rw [mulExpR, getR_eq]
  rfl

/-- The sum `∑_{i<n} f i`, by a recursion that the kernel evaluates directly. -/
noncomputable def sumR (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i ih => Nat.add ih (f i)) n

/-- `sumR n f` is `∑ i ∈ range n, f i`. -/
theorem sumR_eq (n : ℕ) (f : ℕ → ℕ) : sumR n f = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_range_succ, ← ih]
    rfl

/-- `radTerm`, in a form that the kernel evaluates directly. -/
noncomputable def radTermR (v a j i : ℕ) : ℕ :=
  condR (Nat.ble (Nat.add v i) 16)
    (cosWin (Nat.add v i) (Nat.mod (Nat.add a (mulExpR (Nat.sub j i))) (cosPer (Nat.add v i)))) 0

/-- `radTermR` agrees with `radTerm`. -/
theorem radTermR_eq (v a j i : ℕ) : radTermR v a j i = radTerm v a j i := by
  rw [radTermR, radTerm, mulExpR_eq]
  simp only [Nat.add_eq, Nat.sub_eq]
  by_cases h : v + i ≤ 16
  · simp only [h, ↓reduceIte, ble_true h]
    rfl
  · simp only [h, ↓reduceIte, ble_false h]

/-- `radSum`, by a recursion that the kernel evaluates directly. -/
noncomputable def radSumR (t v a : ℕ) : ℕ := sumR t fun j => sumR j fun i => radTermR v a j i

/-- `radSumR` agrees with `radSum`. -/
theorem radSumR_eq (t v a : ℕ) : radSumR t v a = radSum t v a := by
  simp only [radSumR, sumR_eq, radTermR_eq, radSum]

/-! ### The majorant from the sum `Λ` -/

/-- `10^8 Ū_c` from `Λ`, with `t = c - 1`: the least `k` with
`(2 Λ - t (t - 2) 10^{18}) / (100 t^2) ≤ k^2`, clipped to `[1526, 10^8]`. -/
def uVal (t L : ℕ) : ℕ :=
  natMin 100000000 (natMax (ceilSqrt (Nat.div (Nat.sub (Nat.add (Nat.sub (Nat.mul 2 L)
    (t * (t - 2) * 10 ^ 18)) (100 * t ^ 2)) 1) (100 * t ^ 2))) 1526)

/-- `uVal t L` in terms of `min`, `max` and the ceiling of the radicand. -/
theorem uVal_eq (t L : ℕ) : uVal t L = min (10 ^ 8)
    (max (ceilSqrt ((2 * L - t * (t - 2) * 10 ^ 18 + 100 * t ^ 2 - 1) / (100 * t ^ 2))) 1526) := by
  rw [uVal, natMin_eq, natMax_eq]
  rfl

/-- The radicand `⌈(2 Λ - t (t - 2) 10^{18}) / (100 t^2)⌉` of `uVal t Λ`. -/
def uRad (t L : ℕ) : ℕ :=
  Nat.div (Nat.sub (Nat.add (Nat.sub (Nat.mul 2 L) (t * (t - 2) * 10 ^ 18)) (100 * t ^ 2)) 1)
    (100 * t ^ 2)

/-- The least `k` with `R ≤ k^2`, clipped to `[1526, 10^8]`: the clipped cases are decided by
comparing `R` with `1526^2` and `10^{16}`, before any root is taken. -/
def uClip (R : ℕ) : ℕ :=
  condR (Nat.ble R 2328676) 1526 (condR (Nat.ble R 10000000000000000) (ceilSqrtMid R) 100000000)

/-- `uClip R` is `ceilSqrt R` clipped to `[1526, 10^8]`. -/
theorem uClip_eq (R : ℕ) : uClip R = min (10 ^ 8) (max (ceilSqrt R) 1526) := by
  rw [uClip, ceilSqrtMid_eq, ceilSqrt_eq]
  have hlo : natCeilSqrt (R : ℚ) ≤ 1526 ↔ R ≤ 2328676 := by
    rw [natCeilSqrt_le_iff]; norm_cast
  have hhi : natCeilSqrt (R : ℚ) ≤ 10 ^ 8 ↔ R ≤ 10000000000000000 := by
    rw [natCeilSqrt_le_iff]; norm_cast
  by_cases h1 : R ≤ 2328676
  · simp only [ble_true h1]
    rw [max_eq_right (hlo.2 h1)]
    norm_num
  · simp only [ble_false h1]
    by_cases h2 : R ≤ 10000000000000000
    · simp only [ble_true h2]
      rw [max_eq_left (by have := mt hlo.1 h1; omega), min_eq_right (hhi.2 h2)]
    · simp only [ble_false h2]
      rw [min_eq_left]
      · norm_num
      · have := mt hhi.1 h2; omega

/-- `uVal`, with the clipped cases decided first. -/
def uValR (t L : ℕ) : ℕ := uClip (uRad t L)

/-- `uValR` agrees with `uVal`. -/
theorem uValR_eq (t L : ℕ) : uValR t L = uVal t L := by
  rw [uValR, uClip_eq, uVal_eq]
  rfl

/-- The values `10^8 Ū_c(± 2^v 3^{a + k} / 2^17)`, `k < 256`. -/
noncomputable def uBlock (c v a : ℕ) : List ℕ :=
  mapR (fun L => uValR (c - 1) (Nat.add L (2 * 10 ^ 18 * radBig (c - 1) v)))
    (unpackR 72 256 (radSumR (c - 1) v a))

/-- For an integer `z` and `d > 0`, the ceiling square root of `z / d` is `ceilSqrt` of the
ceiling `⌈z.toNat / d⌉`. -/
theorem natCeilSqrt_div (z : ℤ) {d : ℕ} (hd : 0 < d) :
    natCeilSqrt ((z : ℚ) / d) = ceilSqrt ((z.toNat + d - 1) / d) := by
  rw [ceilSqrt_eq]
  rcases le_or_gt z 0 with hz | hz
  · have h1 : (z : ℚ) / d ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hz) (by positivity)
    have h2 : (z.toNat + d - 1) / d = 0 := by
      rw [Int.toNat_eq_zero.2 hz, zero_add]
      exact Nat.div_eq_of_lt (by omega)
    rw [h2]
    simp [natCeilSqrt, h1]
  · have hc : ⌈(z : ℚ) / d⌉ = ((z.toNat + d - 1) / d : ℕ) := by
      rw [show (z : ℚ) = ((z.toNat : ℤ) : ℚ) by rw [Int.toNat_of_nonneg hz.le],
        Rat.ceil_intCast_div_natCast, ceilDiv_cast _ _ hd]
    have hpos : 0 < (z : ℚ) / d := div_pos (by exact_mod_cast hz) (by positivity)
    have hm : 0 < (z.toNat + d - 1) / d := by
      rw [Nat.div_pos_iff]
      omega
    unfold natCeilSqrt
    rw [ite_eq_right (not_le.2 hpos), ite_eq_right (not_le.2 (by exact_mod_cast hm)), hc]
    simp

/-- The cosine bound of pair `(i, j)` at `σ 2^v 3^J / 2^17`. -/
theorem trCapCosBound_pair {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (v J : ℕ) {i j : ℕ} (hij : i < j)
    (hj : j < 15) :
    trCapCosBound (1 / 10 ^ 18) ((((2 : ℚ) ^ j - 1) - ((2 : ℚ) ^ i - 1)) *
        ((σ * 2 ^ v * 3 ^ J : ℤ) / 2 ^ 17)) =
      (cosI (2 ^ (v + i) * 3 ^ (J + mulExp (j - i))) : ℚ) / 10 ^ 18 := by
  have hj' : (2 : ℚ) ^ j = 2 ^ i * 2 ^ (j - i) := by rw [← pow_add]; congr 1; omega
  have harg : (((2 : ℚ) ^ j - 1) - ((2 : ℚ) ^ i - 1)) * ((σ * 2 ^ v * 3 ^ J : ℤ) / 2 ^ 17) =
      (((2 ^ (j - i) - 1) * (σ * 2 ^ (v + i) * 3 ^ J) : ℤ) : ℚ) / 2 ^ 17 := by
    rw [hj']
    push_cast
    rw [pow_add]
    ring
  rw [harg, trCapCosBound_eq_cosI, cosI_mul_pow_two_sub_one (by simp; omega)]
  congr 2
  have h : (3 : ℤ) ^ mulExp (j - i) * (σ * 2 ^ (v + i) * 3 ^ J) =
      σ * (2 ^ (v + i) * 3 ^ (J + mulExp (j - i))) := by rw [pow_add]; ring
  rw [h]
  rcases hσ with rfl | rfl
  · rw [one_mul]
  · rw [neg_one_mul, cosI_neg]

/-- The shifted cosine bound of pair `(i, j)`, as a lane of the radicand sum. -/
theorem cosI_pair_eq_lane {v a k i j : ℕ} (hk : k < 256) :
    cosI (2 ^ (v + i) * 3 ^ (a + k + mulExp (j - i))) + 10 ^ 18 =
      (lane 72 (radTerm v a j i) k : ℤ) + if v + i ≤ 16 then 0 else 2 * 10 ^ 18 := by
  rw [lane_radTerm hk]
  split_ifs with h
  · rw [cosLaneAt_eq_of_lt h (Nat.mod_lt _ (cosPer_pos _)) hk, add_zero]
    rw [Nat.mod_add_mod, show a + k + mulExp (j - i) = a + mulExp (j - i) + k by omega]
  · rw [cosI_mul_two_pow (by omega)]
    norm_num

/-- For `k < n`, the entry `k` of `(List.range n).map f` is `f k`. -/
theorem getD_map_range (f : ℕ → ℕ) {n k : ℕ} (hk : k < n) :
    ((List.range n).map f).getD k 0 = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- `2 ∑_{j < t} j = t (t - 1)`. -/
theorem two_mul_sum_range_id (t : ℕ) : 2 * (∑ j ∈ range t, j) = t * (t - 1) := by
  rw [mul_comm]; exact Finset.sum_range_id_mul_two t

/-- `∑_{j < t} ∑_{i < j} x = (∑_{j < t} j) • x`. -/
theorem sum_range_sum_range_const {M : Type*} [AddCommMonoid M] (t : ℕ) (x : M) :
    ∑ j ∈ range t, ∑ _i ∈ range j, x = (∑ j ∈ range t, j) • x := by
  simp [sum_smul]

/-- For `3 ≤ c ≤ 16`, `k < 256` and `σ = ± 1`, the entry `k` of `uBlock c v a` is
`10^8 Ū_c(σ 2^v 3^{a + k} / 2^17)`. -/
theorem uBlock_spec {c : ℕ} (hc3 : 3 ≤ c) (hc : c ≤ 16) (v a : ℕ) {k : ℕ}
    (hk : k < 256) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ((uBlock c v a).getD k 0 : ℚ) =
      10 ^ 8 * c3H17CapUp c ((σ * 2 ^ v * 3 ^ (a + k) : ℤ) / 2 ^ 17) := by
  set t := c - 1 with ht
  have ht15 : t ≤ 15 := by omega
  have ht2 : 2 ≤ t := by omega
  rw [c3H17CapUp_eq_trCapUpper, trCapUpper_of_mem (by omega) (by omega),
    show ((c : ℤ) - 1).toNat = t by omega]
  set C : ℤ := ∑ j ∈ range t, ∑ i ∈ range j,
    cosI (2 ^ (v + i) * 3 ^ (a + k + mulExp (j - i))) with hC
  set Λ : ℤ := ∑ j ∈ range t, ∑ i ∈ range j,
    (cosI (2 ^ (v + i) * 3 ^ (a + k + mulExp (j - i))) + 10 ^ 18) with hΛ
  have hΛC : 2 * Λ = 2 * C + (t : ℤ) * ((t : ℤ) - 1) * 10 ^ 18 := by
    rw [hΛ, hC]
    simp only [sum_add_distrib, sum_range_sum_range_const, nsmul_eq_mul]
    have h2 := two_mul_sum_range_id t
    have h2' : (2 : ℤ) * ∑ j ∈ range t, (j : ℤ) = (t : ℤ) * ((t : ℤ) - 1) := by
      have : ((2 * ∑ j ∈ range t, j : ℕ) : ℤ) = ((t * (t - 1) : ℕ) : ℤ) := by rw [h2]
      push_cast [Nat.cast_sub (by omega : 1 ≤ t)] at this
      exact this
    push_cast at h2' ⊢
    linear_combination (10 ^ 18 : ℤ) * h2'
  have hsum : ∑ j ∈ range t, ∑ i ∈ range j, trCapCosBound (1 / 10 ^ 18)
      ((((2 : ℚ) ^ j - 1) - ((2 : ℚ) ^ i - 1)) * ((σ * 2 ^ v * 3 ^ (a + k) : ℤ) / 2 ^ 17)) =
      (C : ℚ) / 10 ^ 18 := by
    rw [hC, Int.cast_sum, sum_div]
    refine sum_congr rfl fun j hj => ?_
    rw [Int.cast_sum, sum_div]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hj hi
    rw [trCapCosBound_pair hσ v (a + k) hi (by omega)]
  have hrad : trCapRadicand t (1 / 10 ^ 18) ((σ * 2 ^ v * 3 ^ (a + k) : ℤ) / 2 ^ 17) =
      ((2 * Λ - t * (t - 2) * 10 ^ 18 : ℤ) : ℚ) / ((100 * t ^ 2 : ℕ) : ℚ) := by
    unfold trCapRadicand
    rw [hsum]
    have htq : (t : ℚ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
    have hΛC' : (2 * (Λ : ℚ)) = 2 * (C : ℚ) + (t : ℚ) * ((t : ℚ) - 1) * 10 ^ 18 := by
      exact_mod_cast hΛC
    push_cast
    rw [hΛC']
    field_simp
    ring
  rw [hrad, natCeilSqrt_div _ (by positivity)]
  have hlane : Λ = ((lane 72 (radSum t v a) k + 2 * 10 ^ 18 * radBig t v : ℕ) : ℤ) := by
    rw [hΛ, show ∑ j ∈ range t, ∑ i ∈ range j,
        (cosI (2 ^ (v + i) * 3 ^ (a + k + mulExp (j - i))) + 10 ^ 18) =
        ∑ j ∈ range t, ∑ i ∈ range j, ((lane 72 (radTerm v a j i) k : ℤ) +
          if v + i ≤ 16 then 0 else 2 * 10 ^ 18) from
      sum_congr rfl fun j _ => sum_congr rfl fun i _ => cosI_pair_eq_lane hk,
      lane_radSum ht15 hk, radBig]
    push_cast
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have htoNat : (2 * Λ - t * (t - 2) * 10 ^ 18 : ℤ).toNat =
      2 * (lane 72 (radSum t v a) k + 2 * 10 ^ 18 * radBig t v) - t * (t - 2) * 10 ^ 18 := by
    rw [hlane]
    have : ((t : ℤ) - 2) = ((t - 2 : ℕ) : ℤ) := by push_cast [Nat.cast_sub ht2]; ring
    rw [this]
    exact_mod_cast Int.toNat_sub _ _
  rw [htoNat, uBlock, mapR_eq, unpackR_eq, List.map_map, getD_map_range _ hk, Function.comp_apply,
    uValR_eq, radSumR_eq, Nat.add_eq, uVal_eq, ← ht]
  have h8 : (0 : ℚ) < 10 ^ 8 := by norm_num
  push_cast
  rw [mul_min_of_nonneg _ _ h8.le, mul_one, mul_div_cancel₀ _ h8.ne']
  norm_num

/-! ### Segments of consecutive points -/

/-- The values `10^8 Ū_c(± 2^v 3^{a + k} / 2^17)` for `k < 256 m`. -/
noncomputable def uSegBlocks (c v a m : ℕ) : List ℕ :=
  flatRangeFrom (fun b => uBlock c v (Nat.add a (Nat.mul 256 b))) m 0

/-- `uBlock c v a` has length `256`. -/
theorem length_uBlock (c v a : ℕ) : (uBlock c v a).length = 256 := by
  rw [uBlock, mapR_eq, unpackR_eq]
  simp

/-- In a flattening of lists of a common positive length `C`, the entry of index `i` is the
entry `i mod C` of the list `⌊i / C⌋`. -/
theorem getD_flatten_of_length {α : Type*} {C : ℕ} (hC : 0 < C) (d : α) :
    ∀ (L : List (List α)), (∀ x ∈ L, x.length = C) → ∀ i,
      L.flatten.getD i d = (L.getD (i / C) []).getD (i % C) d
  | [], _, i => by simp
  | x :: L, hL, i => by
    have hx := hL x (List.mem_cons_self ..)
    rw [List.flatten_cons]
    rcases lt_or_ge i C with h | h
    · rw [List.getD_append _ _ _ _ (by omega), Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      simp
    · rw [List.getD_append_right _ _ _ _ (by omega), hx,
        getD_flatten_of_length hC d L (fun y hy => hL y (List.mem_cons_of_mem _ hy)) (i - C)]
      have h1 : i / C = (i - C) / C + 1 := by
        rw [← Nat.sub_add_cancel h, Nat.add_div_right _ hC, Nat.sub_add_cancel h]
      have h2 : i % C = (i - C) % C := by
        rw [← Nat.sub_add_cancel h, Nat.add_mod_right, Nat.sub_add_cancel h]
      rw [h1, h2]
      simp

/-- A flattening of lists of a common length `C` has length `C` times the number of lists. -/
theorem length_flatten_of_length {α : Type*} {C : ℕ} :
    ∀ (L : List (List α)), (∀ x ∈ L, x.length = C) → L.flatten.length = C * L.length
  | [], _ => by simp
  | x :: L, hL => by
    rw [List.flatten_cons, List.length_append, hL x (List.mem_cons_self ..),
      length_flatten_of_length L (fun y hy => hL y (List.mem_cons_of_mem _ hy))]
    simp [mul_add, add_comm]

/-- `uSegBlocks c v a m` has length `256 m`. -/
theorem length_uSegBlocks (c v a m : ℕ) : (uSegBlocks c v a m).length = 256 * m := by
  rw [uSegBlocks, flatRangeFrom_eq, length_flatten_of_length (C := 256) _ (by simp [length_uBlock])]
  simp

/-- For `3 ≤ c ≤ 16`, `k < 256 m` and `σ = ± 1`, the entry `k` of `uSegBlocks c v a m` is
`10^8 Ū_c(σ 2^v 3^{a + k} / 2^17)`. -/
theorem uSegBlocks_spec {c : ℕ} (hc3 : 3 ≤ c) (hc : c ≤ 16) (v a m : ℕ)
    {k : ℕ} (hk : k < 256 * m) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ((uSegBlocks c v a m).getD k 0 : ℚ) =
      10 ^ 8 * c3H17CapUp c ((σ * 2 ^ v * 3 ^ (a + k) : ℤ) / 2 ^ 17) := by
  rw [uSegBlocks, flatRangeFrom_eq,
    getD_flatten_of_length (C := 256) (by norm_num) 0 _ (by simp [length_uBlock])]
  have hb : k / 256 < m := by omega
  have hmap : ((List.range' 0 m).map fun b => uBlock c v (Nat.add a (Nat.mul 256 b))).getD
      (k / 256) [] = uBlock c v (a + 256 * (k / 256)) := by
    simp [List.getD_eq_getElem?_getD, hb]
  rw [hmap, uBlock_spec hc3 hc v _ (Nat.mod_lt _ (by norm_num)) hσ,
    show a + 256 * (k / 256) + k % 256 = a + k by omega]

/-! ### Periodic segments -/

/-- `Ū_c(± 2^v 3^J / 2^17)` depends only on `J mod p_v`. -/
theorem c3H17CapUp_mod_cosPer (c : ℤ) {v : ℕ} (hv : v ≤ 16) (σ : ℤ) (J : ℕ) :
    c3H17CapUp c ((σ * 2 ^ v * 3 ^ J : ℤ) / 2 ^ 17) =
      c3H17CapUp c ((σ * 2 ^ v * 3 ^ (J % cosPer v) : ℤ) / 2 ^ 17) := by
  obtain ⟨m, hm⟩ := two_pow_dvd_three_pow_sub hv J
  have : ((σ * 2 ^ v * 3 ^ J : ℤ) : ℚ) / 2 ^ 17 =
      ((σ * 2 ^ v * 3 ^ (J % cosPer v) : ℤ) : ℚ) / 2 ^ 17 + ((σ * m : ℤ) : ℚ) := by
    have h' : (σ * 2 ^ v * 3 ^ J : ℤ) = σ * 2 ^ v * 3 ^ (J % cosPer v) + 2 ^ 17 * (σ * m) := by
      linear_combination σ * hm
    rw [h']
    push_cast
    field_simp
    ring
  rw [this, c3H17CapUp_add_intCast]

/-- The values `10^8 Ū_c(± 2^v 3^J / 2^17)` for `J < p_v`. -/
noncomputable def uPer (c v : ℕ) : List ℕ :=
  if 256 ≤ cosPer v then uSegBlocks c v 0 (cosPer v / 256) else takeR (cosPer v) (uBlock c v 0)

/-- The period `p_v` is at most `2^15`. -/
theorem cosPer_le (v : ℕ) : cosPer v ≤ 2 ^ 15 := by
  unfold cosPer; split_ifs
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · norm_num

/-- If `256 ≤ p_v`, then `256 ∣ p_v`. -/
theorem cosPer_dvd {v : ℕ} (h : 256 ≤ cosPer v) : 256 ∣ cosPer v := by
  unfold cosPer at *
  split_ifs at * with hv
  · have h8 : 8 ≤ 15 - v := by
      by_contra h'
      have := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) (not_le.mp h')
      norm_num at this
      omega
    exact (show (256 : ℕ) = 2 ^ 8 by norm_num) ▸ pow_dvd_pow 2 h8
  · omega

/-- `uPer c v` has length `p_v`. -/
theorem length_uPer (c v : ℕ) : (uPer c v).length = cosPer v := by
  unfold uPer
  split_ifs with h
  · rw [length_uSegBlocks, Nat.mul_div_cancel' (cosPer_dvd h)]
  · rw [takeR_eq, List.length_take, length_uBlock]; omega

/-- For `3 ≤ c ≤ 16`, `k < p_v` and `σ = ± 1`, the entry `k` of `uPer c v` is
`10^8 Ū_c(σ 2^v 3^k / 2^17)`. -/
theorem uPer_spec {c : ℕ} (hc3 : 3 ≤ c) (hc : c ≤ 16) (v : ℕ) {k : ℕ}
    (hk : k < cosPer v) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ((uPer c v).getD k 0 : ℚ) = 10 ^ 8 * c3H17CapUp c ((σ * 2 ^ v * 3 ^ k : ℤ) / 2 ^ 17) := by
  unfold uPer
  split_ifs with h
  · rw [uSegBlocks_spec hc3 hc v 0 _ (by rw [Nat.mul_div_cancel' (cosPer_dvd h)]; exact hk) hσ,
      zero_add]
  · rw [takeR_eq, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk,
      ← List.getD_eq_getElem?_getD, uBlock_spec hc3 hc v 0 (by omega) hσ, zero_add]

/-- The values `10^8 Ū_c(± 2^v 3^{a + k} / 2^17)`, `k < n`: computed directly when `n ≤ p_v`,
and as copies of a period otherwise. -/
noncomputable def uSeg (c v a n : ℕ) : List ℕ :=
  if n ≤ cosPer v then uSegBlocks c v a (n / 256)
  else flatRangeFrom (fun _ => uPer c v) (n / cosPer v) 0

/-- If `256 ∣ n` and either `n ≤ p_v` or `p_v ∣ n`, then `uSeg c v a n` has length `n`. -/
theorem length_uSeg {c v a n : ℕ} (hn : 256 ∣ n) (h : n ≤ cosPer v ∨ cosPer v ∣ n) :
    (uSeg c v a n).length = n := by
  unfold uSeg
  split_ifs with h'
  · rw [length_uSegBlocks, Nat.mul_div_cancel' hn]
  · rw [flatRangeFrom_eq, length_flatten_of_length (C := cosPer v) _ (by
      intro x hx; simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; exact length_uPer c v)]
    simp only [List.length_map, List.length_range']
    rcases h with h | h
    · omega
    · rw [Nat.mul_div_cancel' h]

/-- For `3 ≤ c ≤ 16`, `v ≤ 16`, `256 ∣ n`, either `n ≤ p_v` or `p_v ∣ a` and `p_v ∣ n`, `k < n`
and `σ = ± 1`, the entry `k` of `uSeg c v a n` is `10^8 Ū_c(σ 2^v 3^{a + k} / 2^17)`. -/
theorem uSeg_spec {c : ℕ} (hc3 : 3 ≤ c) (hc : c ≤ 16) {v : ℕ} (hv : v ≤ 16) {a n k : ℕ}
    (hn : 256 ∣ n) (h : n ≤ cosPer v ∨ (cosPer v ∣ a ∧ cosPer v ∣ n)) (hk : k < n) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    ((uSeg c v a n).getD k 0 : ℚ) =
      10 ^ 8 * c3H17CapUp c ((σ * 2 ^ v * 3 ^ (a + k) : ℤ) / 2 ^ 17) := by
  unfold uSeg
  split_ifs with h'
  · exact uSegBlocks_spec hc3 hc v a _ (by rw [Nat.mul_div_cancel' hn]; exact hk) hσ
  · rcases h with h | ⟨ha, hn'⟩
    · omega
    have hp := cosPer_pos v
    rw [flatRangeFrom_eq, getD_flatten_of_length hp 0 _ (by
      intro x hx; simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; exact length_uPer c v)]
    have hb : k / cosPer v < n / cosPer v := Nat.div_lt_div_of_lt_of_dvd hn' hk
    have hmap : ((List.range' 0 (n / cosPer v)).map fun _ => uPer c v).getD (k / cosPer v) [] =
        uPer c v := by
      simp [List.getD_eq_getElem?_getD, hb]
    rw [hmap, uPer_spec hc3 hc v (Nat.mod_lt _ hp) hσ, c3H17CapUp_mod_cosPer _ hv σ (a + k)]
    congr 6
    rw [Nat.add_mod, Nat.dvd_iff_mod_eq_zero.1 ha, zero_add, Nat.mod_mod]

/-! ### The segments in one pass -/

/-- `mapR f (unpackR w k Z) ++ rest`, by one recursion that the kernel evaluates directly. -/
noncomputable def unpackMapOnto (f : ℕ → ℕ) (w k Z : ℕ) (rest : List ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => rest)
    (fun _ ih Y => f (Nat.mod Y (2 ^ w)) :: ih (Nat.shiftRight Y w)) k Z

/-- `unpackMapOnto f w k Z rest` is `mapR f (unpackR w k Z) ++ rest`. -/
theorem unpackMapOnto_eq (f : ℕ → ℕ) (w : ℕ) (rest : List ℕ) :
    ∀ k Z, unpackMapOnto f w k Z rest = mapR f (unpackR w k Z) ++ rest
  | 0, _ => rfl
  | k + 1, Z => by
    change f (Nat.mod Z (2 ^ w)) :: unpackMapOnto f w k (Nat.shiftRight Z w) rest =
      f (Nat.mod Z (2 ^ w)) :: (mapR f (unpackR w k (Nat.shiftRight Z w)) ++ rest)
    rw [unpackMapOnto_eq f w rest k]

/-- The concatenation `F k (F (k + 1) (⋯ (F (k + m - 1) [])))`, by a recursion that the kernel
evaluates directly. -/
noncomputable def flatRec (F : ℕ → List ℕ → List ℕ) (m : ℕ) : ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => []) (fun _ ih k => F k (ih (Nat.add k 1))) m

/-- If `F k rest = g k ++ rest` for all `k` and `rest`, then `flatRec F m k` is
`flatRangeFrom g m k`. -/
theorem flatRec_eq (F : ℕ → List ℕ → List ℕ) (g : ℕ → List ℕ)
    (hF : ∀ k rest, F k rest = g k ++ rest) : ∀ m k, flatRec F m k = flatRangeFrom g m k
  | 0, _ => rfl
  | m + 1, k => by
    change F k (flatRec F m (Nat.add k 1)) = appendR (g k) (flatRangeFrom g m (Nat.add k 1))
    rw [hF, flatRec_eq F g hF m, appendR_eq]

/-- The blocks `uBlock c v (a + 256 b)`, `k ≤ b < k + m`, concatenated, by one recursion: each
block is unpacked directly onto the following ones. -/
noncomputable def uBlocksFrom (c v a m : ℕ) : ℕ → List ℕ :=
  flatRec (fun k rest =>
    unpackMapOnto (fun L => uValR (c - 1) (Nat.add L (2 * 10 ^ 18 * radBig (c - 1) v)))
      72 256 (radSumR (c - 1) v (Nat.add a (Nat.mul 256 k))) rest) m

/-- `uBlocksFrom c v a m k` is the concatenation of the blocks `uBlock c v (a + 256 b)`,
`k ≤ b < k + m`. -/
theorem uBlocksFrom_eq (c v a m k : ℕ) :
    uBlocksFrom c v a m k = flatRangeFrom (fun b => uBlock c v (Nat.add a (Nat.mul 256 b))) m k :=
  flatRec_eq _ _ (fun k rest => by rw [unpackMapOnto_eq, uBlock]) m k

/-- `uSegBlocks`, with each block unpacked directly onto the following ones. -/
noncomputable def uSegBlocksF (c v a m : ℕ) : List ℕ := uBlocksFrom c v a m 0

/-- `uSegBlocksF` agrees with `uSegBlocks`. -/
theorem uSegBlocksF_eq (c v a m : ℕ) : uSegBlocksF c v a m = uSegBlocks c v a m :=
  uBlocksFrom_eq c v a m 0

/-- `uPer`, with the blocks unpacked directly onto the following ones. -/
noncomputable def uPerF (c v : ℕ) : List ℕ :=
  if 256 ≤ cosPer v then uSegBlocksF c v 0 (cosPer v / 256) else takeR (cosPer v) (uBlock c v 0)

/-- `uPerF` agrees with `uPer`. -/
theorem uPerF_eq (c v : ℕ) : uPerF c v = uPer c v := by
  unfold uPerF uPer
  split_ifs
  · exact uSegBlocksF_eq _ _ _ _
  · rfl

/-- `uSeg`, with the blocks unpacked directly onto the following ones. -/
noncomputable def uSegF (c v a n : ℕ) : List ℕ :=
  if n ≤ cosPer v then uSegBlocksF c v a (n / 256)
  else flatRangeFrom (fun _ => uPerF c v) (n / cosPer v) 0

/-- `uSegF` agrees with `uSeg`. -/
theorem uSegF_eq (c v a n : ℕ) : uSegF c v a n = uSeg c v a n := by
  unfold uSegF uSeg
  split_ifs
  · exact uSegBlocksF_eq _ _ _ _
  · simp only [uPerF_eq]

end C3H17Values

end CollatzPosDens
