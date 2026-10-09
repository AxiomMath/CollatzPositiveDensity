/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FcBinomialLower
public import CollatzPosDens.FirstCrossing.FcCountInit
public import CollatzPosDens.FirstCrossing.FcCountStep
public import CollatzPosDens.FirstCrossing.FcDpMass
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesB41
public import CollatzPosDens.FirstCrossing.ScalesB42
public import CollatzPosDens.Transfer.GeometricMass
public import Mathlib.Data.List.GetD

/-!
# Computable mirrors for the startup product of central masses

Write `b_j = scale j`, `K_j = cap j`, `𝐩 = geomMass`, `𝒞 = centralFamily` and `e = eb`. For each
`j < 444` this file defines a computable natural number `N_j = fcStartupProduct.startupNum j b_j`
with
$$N_j\,2^{-64} \le \mathbf{p}(\mathcal{C}(b_j,K_j)),$$
and the product `fcStartupProduct.prodGo n j b_j` of `n` consecutive such numbers, computed along
the scale recursion `b_{j+1} = b_j + e(b_j)`.

* For `j ≤ 41` (where `9 ≤ b_j < 256`) the number is the truncation of `2^64` times the exact
  dynamic-programming value of the mass of the first-crossing family, cut by the minimal early
  overshoot `μ_b` when `b ∈ {9, 10, 11}`.
* For `42 ≤ j ≤ 443` (where `b_j ≥ 256`) it comes from the binomial lower bound
  `1 - 2·2^{-n₊}∑_{t<h₊}C(n₊,t) - 2^{-n₋}∑_{t≤h₋-v₋}C(n₋,t) - 2^{-(K+1)}`, each tail being
  rounded up to a multiple of `2^{-64}`.

## Main definitions

* `CollatzPosDens.fcStartupProduct.startupNum`: the `64`-bit lower bound for the `j`-th factor.
* `CollatzPosDens.fcStartupProduct.prodGo`: the product of consecutive such bounds.

## Main results

* `CollatzPosDens.fcStartupProduct.startupNum_le`: `N_j · 2^{-64} ≤ 𝐩(𝒞(b_j, K_j))` for
  `j < 444`.
* `CollatzPosDens.fcStartupProduct.prodGo_eq`: the product computed along the scale recursion
  is the finite product of the factor bounds.
* `CollatzPosDens.fcStartupProduct.prodGo_mul_le`: lower bounds for consecutive blocks multiply.

## Implementation notes

The non-computable ingredients are replaced by computable mirrors proved equal to them:
`B(j) = ⌈j log₂ 3⌉` is `⌊log₂ 3^j⌋ + 1` for `j ≥ 1` and the centred barrier
`H_{b,r_b}(s) = 2b + B((s-b)₊) - B((b-s)₊)` is free of the shift `r_b` (the shared mirrors
`CollatzPosDens.ceilLog3Nat` and `CollatzPosDens.barrierRb`), and the width
`wd(b) = min(⌈√(32 b lg b)⌉, ⌊3b/5⌋ - 1)` uses the integer ceiling square root. For
`b ∈ {9, 10, 11}`, `μ_b(d)` is bounded above by the least `k < 16` passing an integer form of
its defining inequality; a smaller lower-bound family is used if no such `k` exists, so no
case analysis on the values of `μ_b` is needed.

The binomial tails are summed exactly for `j < 140`, while for `140 ≤ j ≤ 443` the lower tail
`∑_{t≤k}C(n,t)` is bounded by the Chernoff estimate `(p+q)^n / (p^k q^{n-k})` at
`p = k`, `q = n - k`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §15.6.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

namespace fcStartupProduct

/-! ### The dynamic programme for the surviving counts

A surviving prefix of length `i` has valuation sum at least `i`, so the counts `c_{b,i}(s)` are
stored from `s = i` on: the list `dpList b k` holds `r ↦ c_{b,ℓ_b+k}(ℓ_b+k+r)` for
`r < H_{b,r_b}(ℓ_b+k) - (ℓ_b+k)`. -/

/-- `stepGo n c acc` is the list of the `n` inclusive prefix sums `acc + c₀ + ⋯ + c_r` of `c`
(continued constantly once `c` is exhausted). -/
def stepGo : ℕ → List ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | n + 1, [], acc => acc :: stepGo n [] acc
  | n + 1, a :: l, acc => (acc + a) :: stepGo n l (acc + a)

private theorem getD_stepGo (n : ℕ) (c : List ℕ) (acc r : ℕ) :
    (stepGo n c acc).getD r 0 = if r < n then acc + (c.take (r + 1)).sum else 0 := by
  induction n generalizing c acc r with
  | zero => simp [stepGo]
  | succ n ih =>
    cases c with
    | nil =>
      cases r with
      | zero => simp [stepGo]
      | succ r =>
        simp only [stepGo, List.getD_cons_succ, ih]
        simp
    | cons a l =>
      cases r with
      | zero => simp [stepGo]
      | succ r =>
        simp only [stepGo, List.getD_cons_succ, ih, List.take_succ_cons, List.sum_cons]
        split_ifs <;> omega

/-- The sum of a list. -/
def lsum : List ℕ → ℕ
  | [] => 0
  | a :: l => a + lsum l

private theorem lsum_eq_sum (l : List ℕ) : lsum l = l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [lsum, ih]

private theorem sum_range_getD (l : List ℕ) (s : ℕ) :
    ∑ t ∈ Finset.range s, l.getD t 0 = (l.take s).sum := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih]
    rcases lt_or_ge s l.length with h | h
    · rw [List.sum_take_succ _ _ h, List.getD_eq_getElem _ _ h]
    · rw [List.getD_eq_default _ _ h, List.take_of_length_le h,
        List.take_of_length_le (by omega)]
      simp

/-- `chooseRow m R r c` lists `C(m+r, r), C(m+r+1, r+1), …` (`R` terms), given
`c = C(m+r, r)`. -/
def chooseRow (m : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | R + 1, r, c => c :: chooseRow m R (r + 1) (c * (m + r + 1) / (r + 1))

private theorem getD_chooseRow (m R r i : ℕ) :
    (chooseRow m R r ((m + r).choose r)).getD i 0 =
      if i < R then (m + r + i).choose (r + i) else 0 := by
  induction R generalizing r i with
  | zero => simp [chooseRow]
  | succ R ih =>
    have hc : (m + r).choose r * (m + r + 1) / (r + 1) = (m + (r + 1)).choose (r + 1) := by
      refine Nat.div_eq_of_eq_mul_left (by omega) ?_
      rw [mul_comm, Nat.add_one_mul_choose_eq, ← add_assoc]
    cases i with
    | zero => simp [chooseRow]
    | succ i =>
      simp only [chooseRow, List.getD_cons_succ, hc, ih]
      simp only [Nat.add_lt_add_iff_right, show m + (r + 1) + i = m + r + (i + 1) by omega,
        show r + 1 + i = r + (i + 1) by omega]

private theorem sum_Ico_int_zero (f : ℤ → ℕ) (s : ℕ) :
    ∑ t ∈ Finset.Ico (0 : ℤ) s, f t = ∑ t ∈ Finset.range s, f t := by
  refine Finset.sum_nbij' (fun t : ℤ => t.toNat) (fun n : ℕ => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp at ht ⊢
    omega
  · intro n hn
    simp at hn ⊢
    omega
  · intro t ht
    simp at ht ⊢
    omega
  · simp
  · intro t ht
    simp only [Finset.mem_Ico] at ht
    congr 1
    omega

/-- The number of stored counts at length `i`: `H_{b,r_b}(i) - i`, truncated at `0`. -/
def width (b i : ℕ) : ℕ := (barrierRb b i - i).toNat

/-- `dpList b k` lists `r ↦ c_{b,ℓ_b+k}(ℓ_b+k+r)` for `r < width b (ℓ_b+k)`. -/
def dpList (b : ℕ) : ℕ → List ℕ
  | 0 => chooseRow (lb b - 1) (width b (lb b)) 0 1
  | k + 1 => stepGo (width b (lb b + k + 1)) (dpList b k) 0

private theorem fcSurvivorCount_eq_dpList {b : ℕ} (hl : 1 ≤ lb b) (k s : ℕ) :
    fcSurvivorCount b (lb b + k) s =
      if lb b + k ≤ s then (dpList b k).getD (s - (lb b + k)) 0 else 0 := by
  induction k generalizing s with
  | zero =>
    rw [add_zero, fcSurvivorCount_lb hl, barrier_rb_eq_barrierRb, dpList]
    rw [show chooseRow (lb b - 1) (width b (lb b)) 0 1 =
      chooseRow (lb b - 1) (width b (lb b)) 0 ((lb b - 1 + 0).choose 0) by simp,
      getD_chooseRow, width]
    by_cases hs : lb b ≤ s
    · by_cases hs' : (s : ℤ) < barrierRb b (lb b)
      · rw [ite_eq_left ⟨by exact_mod_cast hs, hs'⟩, ite_eq_left hs, ite_eq_left (by omega),
          Int.toNat_natCast]
        simp only [add_zero, zero_add]
        rw [show s - 1 = lb b - 1 + (s - lb b) by omega]
        exact Nat.choose_symm_add
      · rw [ite_eq_right (by omega), ite_eq_left hs, ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right hs]
  | succ k ih =>
    rw [fcSurvivorCount_step (by omega), barrier_rb_eq_barrierRb, dpList, getD_stepGo, width,
      show lb b + (k + 1) - 1 = lb b + k by omega, show lb b + (k + 1) = lb b + k + 1 by omega]
    by_cases hs : (s : ℤ) < barrierRb b (lb b + k + 1)
    · rw [ite_eq_left hs, sum_Ico_int_zero]
      simp only [ih]
      by_cases hs' : lb b + k + 1 ≤ s
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hs'
        rw [ite_eq_left hs', Nat.add_sub_cancel_left, ite_eq_left (by omega), zero_add,
          ← sum_range_getD,
          show lb b + k + 1 + r = (lb b + k) + (r + 1) by omega, Finset.sum_range_add,
          Finset.sum_eq_zero fun t ht => by
            rw [Finset.mem_range] at ht; rw [ite_eq_right (by omega)], zero_add]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [ite_eq_left (by omega), Nat.add_sub_cancel_left]
      · rw [ite_eq_right hs']
        exact Finset.sum_eq_zero fun t ht => by
          rw [Finset.mem_range] at ht; rw [ite_eq_right (by omega)]
    · rw [ite_eq_right hs]
      split_ifs <;> first | rfl | omega

private theorem tsum_fcSurvivorCount {b : ℕ} (hl : 1 ≤ lb b) (k : ℕ) :
    ∑' s : ℕ, (fcSurvivorCount b (lb b + k) s : ℝ≥0∞) = (lsum (dpList b k) : ℝ≥0∞) := by
  rw [tsum_eq_sum (s := Finset.range (lb b + k + (dpList b k).length)), ← Nat.cast_sum]
  · congr 1
    rw [Finset.sum_range_add, Finset.sum_eq_zero fun t ht => by
      rw [Finset.mem_range] at ht; rw [fcSurvivorCount_eq_dpList hl, ite_eq_right (by omega)],
      zero_add,
      lsum_eq_sum, ← List.take_length (l := dpList b k), ← sum_range_getD, List.take_length]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [fcSurvivorCount_eq_dpList hl, ite_eq_left (by omega), Nat.add_sub_cancel_left]
  · intro s hs
    rw [Finset.mem_range, not_lt] at hs
    rw [fcSurvivorCount_eq_dpList hl, ite_eq_left (by omega), List.getD_eq_default _ _ (by omega),
      Nat.cast_zero]

/-! ### Exact rational lower bounds in `ℝ≥0∞` -/

/-- A finite sum of dyadic fractions is at least its truncation to `64` binary digits. -/
private theorem dyadic_sum_ge (s : Finset ℕ) (f e : ℕ → ℕ) (E : ℕ) (hE : ∀ d ∈ s, e d ≤ E) :
    (((2 ^ 64 * ∑ d ∈ s, f d * 2 ^ (E - e d)) / 2 ^ E : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 64 ≤
      ∑ d ∈ s, (f d : ℝ≥0∞) / 2 ^ (e d) := by
  set M := ∑ d ∈ s, f d * 2 ^ (E - e d)
  have h2E : (2 : ℝ≥0∞) ^ E ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2E' : (2 : ℝ≥0∞) ^ E ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hsum : ∑ d ∈ s, (f d : ℝ≥0∞) / 2 ^ (e d) = (M : ℝ≥0∞) / 2 ^ E := by
    simp_rw [div_eq_mul_inv]
    rw [Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    have h2 : (2 : ℝ≥0∞) ^ E = 2 ^ (e d) * 2 ^ (E - e d) := by
      rw [← pow_add, Nat.add_sub_of_le (hE d hd)]
    rw [h2, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]
  rw [hsum]
  set q := 2 ^ 64 * M / 2 ^ E
  have hq' : (q : ℝ≥0∞) * 2 ^ E ≤ 2 ^ 64 * (M : ℝ≥0∞) := by
    exact_mod_cast Nat.div_mul_le_self (2 ^ 64 * M) (2 ^ E)
  rw [ENNReal.le_div_iff_mul_le (Or.inl h2E) (Or.inl h2E')]
  calc (q : ℝ≥0∞) * 2⁻¹ ^ 64 * 2 ^ E = ((q : ℝ≥0∞) * 2 ^ E) * 2⁻¹ ^ 64 := by ring
    _ ≤ (2 ^ 64 * (M : ℝ≥0∞)) * 2⁻¹ ^ 64 := mul_le_mul_left hq' _
    _ = M := by
      rw [mul_comm (2 ^ 64 : ℝ≥0∞), mul_assoc, ← mul_pow,
        ENNReal.mul_inv_cancel (by simp) (by simp), one_pow, mul_one]

/-! ### Lower bound for the small scales -/

/-- The defining inequality of `μ_b(d)` at `k`, as a decidable statement on natural numbers. -/
def muTest (b d k : ℕ) : Bool :=
  decide (0 ≤ barrierRb b d + k ∧
    16 * 3 ^ d * 2 ^ (3 * b) < (2 ^ (3 * b) - 1) * 2 ^ (barrierRb b d + k).toNat)

private theorem fcMinOvershoot_le_of_muTest {b d k : ℕ} (h : muTest b d k = true) :
    fcMinOvershoot b d ≤ k := by
  apply fcMinOvershoot_le
  simp only [muTest, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  rw [barrier_rb_eq_barrierRb, ← Int.toNat_of_nonneg h0, zpow_natCast]
  have hb : 1 ≤ 2 ^ (3 * b) := Nat.one_le_two_pow
  have := (Nat.cast_lt (α := ℝ)).2 h1
  push_cast [Nat.cast_sub hb] at this
  exact this

/-- A candidate for `μ_b(d)`: the least `k < 16` passing `muTest`. -/
def muC (b d : ℕ) : ℕ := (List.range 16).findIdx (muTest b d)

/-- The overshoot lower bound used for the small scales: `μ_b` on `{9, 10, 11}` (or `K + 1`,
which empties the family, should the candidate fail), and `0` elsewhere. -/
def muF (b K d : ℕ) : ℕ :=
  if b ∈ ({9, 10, 11} : Finset ℕ) then (if muTest b d (muC b d) then muC b d else K + 1) else 0

private theorem smallSet_subset {b K : ℕ} (hb256 : b < 256) :
    {w : Word | w ∈ firstCrossing b (rb b) K ∧ lb b + 1 ≤ w.length ∧ w.length ≤ hb b ∧
      barrier b (rb b) w.length + muF b K w.length ≤ (w.valSum : ℤ)} ⊆ centralFamily b K := by
  rintro w ⟨hfc, -, -, hμ⟩
  refine ⟨hfc, fun h9 => ?_, fun h => absurd h (by omega)⟩
  simp only [muF, h9, ite_true] at hμ
  split_ifs at hμ with ht
  · have := fcMinOvershoot_le_of_muTest ht
    have : (fcMinOvershoot b w.length : ℤ) ≤ muC b w.length := by exact_mod_cast this
    linarith
  · have := valSum_le_barrier_add_of_mem_firstCrossing hfc
    push_cast at hμ
    linarith

/-- The exponent `H_{b,r_b}(d) + K`, truncated at `0`. -/
def smallE (b K d : ℕ) : ℕ := (barrierRb b d + K).toNat

/-- The numerator `Z_d (2^{K+1-μ(d)} - 1)` of the `d`-th term. -/
def smallA (b K d : ℕ) (c : List ℕ) : ℕ := lsum c * (2 ^ (K + 1 - muF b K d) - 1)

/-- The scaled sum of the terms, accumulated along the dynamic programme. -/
def smallGo (b K E : ℕ) : ℕ → List ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, c, d =>
    smallA b K d c * 2 ^ (E - smallE b K d) + smallGo b K E n (stepGo (width b d) c 0) (d + 1)

private theorem smallGo_eq (b K E n k : ℕ) :
    smallGo b K E n (dpList b k) (lb b + k + 1) =
      ∑ i ∈ Finset.range n, smallA b K (lb b + 1 + (k + i)) (dpList b (k + i)) *
        2 ^ (E - smallE b K (lb b + 1 + (k + i))) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ', smallGo, add_comm]
    have h := ih (k + 1)
    rw [show lb b + (k + 1) + 1 = lb b + k + 1 + 1 by omega] at h
    simp only [dpList] at h
    rw [h, add_zero, show lb b + k + 1 = lb b + 1 + k by omega]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show k + 1 + i = k + (i + 1) by omega]

/-- The maximal exponent. -/
def smallEmax (b K : ℕ) : ℕ := (Finset.Icc (lb b + 1) (hb b)).sup (smallE b K)

/-- A `64`-bit lower bound for `2^64 𝐩(𝒞(b, K))` at a small scale `b`. -/
def smallNum (b K : ℕ) : ℕ :=
  2 ^ 64 * smallGo b K (smallEmax b K) (hb b - lb b) (dpList b 0) (lb b + 1) / 2 ^ smallEmax b K

private theorem smallNum_le {b : ℕ} (K : ℕ) (hl : 1 ≤ lb b) (hb256 : b < 256) :
    (smallNum b K : ℝ≥0∞) * 2⁻¹ ^ 64 ≤ geomMass (centralFamily b K) := by
  refine le_trans ?_ (geomMass_mono (smallSet_subset hb256))
  rw [geomMass_firstCrossing_window_eq b K (lb b + 1) (hb b) (muF b K) (by omega) le_rfl]
  have hsum : smallGo b K (smallEmax b K) (hb b - lb b) (dpList b 0) (lb b + 1) =
      ∑ d ∈ Finset.Icc (lb b + 1) (hb b), smallA b K d (dpList b (d - 1 - lb b)) *
        2 ^ (smallEmax b K - smallE b K d) := by
    have h := smallGo_eq b K (smallEmax b K) (hb b - lb b) 0
    rw [add_zero] at h
    rw [h, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      show hb b + 1 - (lb b + 1) = hb b - lb b by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show lb b + 1 + i - 1 - lb b = 0 + i by omega, zero_add]
  have h1 := dyadic_sum_ge (Finset.Icc (lb b + 1) (hb b))
    (fun d => smallA b K d (dpList b (d - 1 - lb b))) (smallE b K) (smallEmax b K)
    (fun d hd => Finset.le_sup hd)
  rw [← hsum] at h1
  refine h1.trans (Finset.sum_le_sum fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  have hcount : ∑' s : ℕ, (fcSurvivorCount b (d - 1) s : ℝ≥0∞) =
      (lsum (dpList b (d - 1 - lb b)) : ℝ≥0∞) := by
    rw [← tsum_fcSurvivorCount hl, show lb b + (d - 1 - lb b) = d - 1 by omega]
  rw [hcount, smallA, Nat.cast_mul, ENNReal.natCast_sub, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one, mul_div_assoc]
  gcongr
  rw [barrier_rb_eq_barrierRb, smallE, ← zpow_natCast]
  exact ENNReal.zpow_le_of_le one_le_two (by omega)

/-! ### Lower bound for the large scales -/

/-- The ceiling of the square root of a natural number. -/
def ceilSqrt (n : ℕ) : ℕ :=
  if Nat.sqrt n * Nat.sqrt n = n then Nat.sqrt n else Nat.sqrt n + 1

private theorem ceil_sqrt_eq_ceilSqrt (n : ℕ) : ⌈√(n : ℝ)⌉₊ = ceilSqrt n := by
  unfold ceilSqrt
  split_ifs with h
  · have : √(n : ℝ) = Nat.sqrt n := by
      conv_lhs => rw [← h]
      push_cast
      exact Real.sqrt_mul_self (Nat.cast_nonneg _)
    rw [this, Nat.ceil_natCast]
  · rw [Nat.ceil_eq_iff (by omega), Nat.add_sub_cancel]
    refine ⟨?_, by push_cast; exact Real.real_sqrt_le_nat_sqrt_succ⟩
    have hlt : Nat.sqrt n * Nat.sqrt n < n := lt_of_le_of_ne (Nat.sqrt_le n) h
    rw [Real.lt_sqrt (Nat.cast_nonneg _)]
    exact_mod_cast (by nlinarith : Nat.sqrt n ^ 2 < n)

/-- Computable form of the width `wd(b)`. -/
def cWd (b : ℕ) : ℕ := min (ceilSqrt (32 * b * Nat.clog 2 b)) (3 * b / 5 - 1)

private theorem wd_eq_cWd (b : ℕ) : wd b = cWd b := by
  rw [wd_def, cWd, ← ceil_sqrt_eq_ceilSqrt]
  push_cast
  rfl

/-- `bpGo n m t c acc` adds `m` consecutive binomial coefficients `C(n, t), C(n, t+1), …` to
`acc`, given `c = C(n, t)`. -/
def bpGo (n : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | m + 1, t, c, acc => bpGo n m (t + 1) (c * (n - t) / (t + 1)) (acc + c)

private theorem bpGo_eq (n m t acc : ℕ) :
    bpGo n m t (n.choose t) acc = acc + ∑ i ∈ Finset.range m, n.choose (t + i) := by
  induction m generalizing t acc with
  | zero => simp [bpGo]
  | succ m ih =>
    have hc : n.choose t * (n - t) / (t + 1) = n.choose (t + 1) :=
      Nat.div_eq_of_eq_mul_left (by omega) (Nat.choose_succ_right_eq n t).symm
    rw [bpGo, hc, ih, Finset.sum_range_succ', add_zero, add_assoc, add_comm (n.choose t)]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show t + 1 + i = t + (i + 1) by omega]

/-- The Chernoff bound for a lower binomial tail. -/
private theorem choose_sum_mul_le (n k p q : ℕ) (hpq : p ≤ q) (hk : k ≤ n) :
    (∑ t ∈ Finset.range (k + 1), n.choose t) * (p ^ k * q ^ (n - k)) ≤ (p + q) ^ n := by
  rw [add_pow, Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum fun t ht => ?_)
    (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega)))
  rw [Finset.mem_range] at ht
  have e1 : p ^ k = p ^ t * p ^ (k - t) := by rw [← pow_add]; congr 1; omega
  have e2 : q ^ (n - t) = q ^ (k - t) * q ^ (n - k) := by rw [← pow_add]; congr 1; omega
  have h3 : p ^ (k - t) ≤ q ^ (k - t) := Nat.pow_le_pow_left hpq _
  rw [e1, e2]
  calc n.choose t * (p ^ t * p ^ (k - t) * q ^ (n - k))
      ≤ n.choose t * (p ^ t * q ^ (k - t) * q ^ (n - k)) := by gcongr
    _ = p ^ t * (q ^ (k - t) * q ^ (n - k)) * n.choose t := by ring

/-- An upper bound `A` with `c 2^64 ∑_{t<k} C(n,t) ≤ A 2^n`: the exact sum, or (when `exact` is
false and `2(k-1) ≤ n`) the Chernoff bound at the ratio `(k-1)/(n-k+1)`. -/
def tailUB (exact : Bool) (c n k : ℕ) : ℕ :=
  if exact = false ∧ 1 ≤ k ∧ 2 * (k - 1) ≤ n then
    c * 2 ^ 64 * n ^ n / (2 ^ n * ((k - 1) ^ (k - 1) * (n - (k - 1)) ^ (n - (k - 1)))) + 1
  else c * 2 ^ 64 * bpGo n k 0 1 0 / 2 ^ n + 1

private theorem tailUB_spec (exact : Bool) (c n k : ℕ) :
    c * 2 ^ 64 * ∑ t ∈ Finset.range k, n.choose t ≤ tailUB exact c n k * 2 ^ n := by
  unfold tailUB
  split_ifs with h
  · obtain ⟨-, hk, hn⟩ := h
    set p := k - 1
    set D := p ^ p * (n - p) ^ (n - p)
    have hpow : ∀ a : ℕ, 0 < a ^ a := fun a => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · exact pow_pos ha a
    have hD : 0 < D := Nat.mul_pos (hpow p) (hpow (n - p))
    have hS := choose_sum_mul_le n p p (n - p) (by omega) (by omega)
    rw [show p + 1 = k by omega, show p + (n - p) = n by omega] at hS
    have h1 := Nat.lt_div_mul_add (a := c * 2 ^ 64 * n ^ n) (b := 2 ^ n * D) (by positivity)
    refine Nat.le_of_mul_le_mul_right ?_ hD
    calc c * 2 ^ 64 * (∑ t ∈ Finset.range k, n.choose t) * D
        = c * 2 ^ 64 * ((∑ t ∈ Finset.range k, n.choose t) * D) := by ring
      _ ≤ c * 2 ^ 64 * n ^ n := by gcongr
      _ ≤ (c * 2 ^ 64 * n ^ n / (2 ^ n * D) + 1) * 2 ^ n * D := by
          rw [add_mul, add_mul, one_mul, mul_assoc _ (2 ^ n)]; omega
  · have h1 := Nat.lt_div_mul_add (a := c * 2 ^ 64 * bpGo n k 0 1 0) (b := 2 ^ n) (by positivity)
    have h2 := bpGo_eq n k 0 0
    rw [Nat.choose_zero_right, zero_add] at h2
    simp only [zero_add] at h2
    rw [← h2, add_mul, one_mul]
    omega

/-- A `64`-bit lower bound for `2^64 𝐩(𝒞(b, K))` at a large scale `b`, from the binomial
lower bound. -/
def largeNum (exact : Bool) (b K : ℕ) : ℕ :=
  2 ^ 64 - (tailUB exact 2 (2 * (b - cWd b) + 83 * cWd b / 200 - 1) (b - cWd b) +
    tailUB exact 1 (2 * (b + cWd b) - (83 * cWd b / 200 + 1))
      (b + cWd b - (83 * cWd b / 200 + 1) + 1) + 2 ^ (63 - K))

/-- `2^m · 2^{-m} = 1` in `ℝ≥0∞`. -/
theorem two_pow_mul_inv_pow (m : ℕ) : (2 : ℝ≥0∞) ^ m * 2⁻¹ ^ m = 1 := by
  rw [← mul_pow, ENNReal.mul_inv_cancel (by simp) (by simp), one_pow]

private theorem tail_le {c n S A : ℕ} (h : c * 2 ^ 64 * S ≤ A * 2 ^ n) :
    (c : ℝ≥0∞) * 2⁻¹ ^ n * S ≤ A * 2⁻¹ ^ 64 := by
  have h' : (c : ℝ≥0∞) * 2 ^ 64 * S ≤ A * 2 ^ n := by exact_mod_cast h
  calc (c : ℝ≥0∞) * 2⁻¹ ^ n * S
      = ((c : ℝ≥0∞) * 2 ^ 64 * S) * (2⁻¹ ^ n * 2⁻¹ ^ 64) := by
        rw [show ((c : ℝ≥0∞) * 2 ^ 64 * S) * (2⁻¹ ^ n * 2⁻¹ ^ 64) =
          (c : ℝ≥0∞) * 2⁻¹ ^ n * S * (2 ^ 64 * 2⁻¹ ^ 64) by ring, two_pow_mul_inv_pow, mul_one]
    _ ≤ (A * 2 ^ n) * (2⁻¹ ^ n * 2⁻¹ ^ 64) := mul_le_mul_left h' _
    _ = A * 2⁻¹ ^ 64 := by
        rw [show (A : ℝ≥0∞) * 2 ^ n * (2⁻¹ ^ n * 2⁻¹ ^ 64) =
          A * 2⁻¹ ^ 64 * (2 ^ n * 2⁻¹ ^ n) by ring, two_pow_mul_inv_pow, mul_one]

private theorem cap_term_le (K : ℕ) : (2⁻¹ : ℝ≥0∞) ^ (K + 1) ≤ (2 ^ (63 - K) : ℕ) * 2⁻¹ ^ 64 := by
  rcases le_or_gt K 63 with hK | hK
  · rw [show (2⁻¹ : ℝ≥0∞) ^ 64 = 2⁻¹ ^ (63 - K) * 2⁻¹ ^ (K + 1) by
        rw [← pow_add]; congr 1; omega, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc,
      two_pow_mul_inv_pow, one_mul]
  · rw [show 63 - K = 0 by omega, pow_zero, Nat.cast_one, one_mul]
    exact pow_le_pow_right_of_le_one' (by norm_num) (by omega)

private theorem largeNum_le (exact : Bool) {b : ℕ} (hb256 : 256 ≤ b) (K : ℕ) :
    (largeNum exact b K : ℝ≥0∞) * 2⁻¹ ^ 64 ≤ geomMass (centralFamily b K) := by
  have h := geomMass_centralFamily_ge_binomial hb256 K
  rw [wd_eq_cWd] at h
  refine le_trans ?_ h
  set w := cWd b
  set A := tailUB exact 2 (2 * (b - w) + 83 * w / 200 - 1) (b - w)
  set B := tailUB exact 1 (2 * (b + w) - (83 * w / 200 + 1)) (b + w - (83 * w / 200 + 1) + 1)
  set C := 2 ^ (63 - K)
  have hA := tail_le (tailUB_spec exact 2 (2 * (b - w) + 83 * w / 200 - 1) (b - w))
  have hB := tail_le (tailUB_spec exact 1 (2 * (b + w) - (83 * w / 200 + 1))
    (b + w - (83 * w / 200 + 1) + 1))
  have hC := cap_term_le K
  push_cast at hA hB
  rw [one_mul] at hB
  unfold largeNum
  have hfin : ∀ x : ℕ, (x : ℝ≥0∞) * 2⁻¹ ^ 64 ≠ ⊤ := fun x =>
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top x) (ENNReal.pow_ne_top (by simp))
  rcases le_or_gt (A + B + C) (2 ^ 64) with hle | hgt
  · set N := 2 ^ 64 - (A + B + C)
    have hsum : (N : ℝ≥0∞) * 2⁻¹ ^ 64 + C * 2⁻¹ ^ 64 + B * 2⁻¹ ^ 64 + A * 2⁻¹ ^ 64 = 1 := by
      rw [← add_mul, ← add_mul, ← add_mul, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add,
        show N + C + B + A = 2 ^ 64 by omega, Nat.cast_pow, Nat.cast_ofNat, two_pow_mul_inv_pow]
    refine ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top (hfin _) hC)
      (ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top (hfin _) hB)
      (ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top (hfin _) hA) ?_))
    rw [← hsum]
    calc _ = (N : ℝ≥0∞) * 2⁻¹ ^ 64 + 2⁻¹ ^ (K + 1) +
          2⁻¹ ^ (2 * (b + w) - (83 * w / 200 + 1)) *
            ∑ t ∈ Finset.range (b + w - (83 * w / 200 + 1) + 1),
              ((2 * (b + w) - (83 * w / 200 + 1)).choose t : ℝ≥0∞) +
          2 * 2⁻¹ ^ (2 * (b - w) + 83 * w / 200 - 1) *
            ∑ t ∈ Finset.range (b - w), ((2 * (b - w) + 83 * w / 200 - 1).choose t : ℝ≥0∞) := by
          ring
      _ ≤ _ := by gcongr
  · rw [show 2 ^ 64 - (A + B + C) = 0 by omega, Nat.cast_zero, zero_mul]
    positivity

/-! ### The product -/

/-- The `64`-bit lower bound used for the `j`-th factor, at `b = b_j`: the exact
dynamic-programming value for `j ≤ 41`, the binomial bound for `42 ≤ j`, with exact binomial
sums for `j < 140` and Chernoff bounds beyond. -/
def startupNum (j b : ℕ) : ℕ :=
  if j < 42 then smallNum b (cap j) else largeNum (decide (j < 140)) b (cap j)

/-- For `j < 444`, `startupNum j b_j * 2⁻⁶⁴` is a lower bound for the geometric mass of the
central family at scale `b_j` and cap `cap j`. -/
theorem startupNum_le {j : ℕ} (hj : j < 444) :
    (startupNum j (scale j) : ℝ≥0∞) * 2⁻¹ ^ 64 ≤ geomMass (centralFamily (scale j) (cap j)) := by
  unfold startupNum
  split_ifs with h
  · apply smallNum_le
    · have := nine_le_scale j; rw [lb_eq]; omega
    · have := scale_monotone (show j ≤ 41 by omega); rw [scale_41] at this; omega
  · apply largeNum_le
    exact two_hundred_fifty_six_le_scale (by omega)

/-- The product of the bounds `startupNum j b_j` for `j₀ ≤ j < j₀ + n`, carrying `b = b_j`. -/
def prodGo : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | n + 1, j, b => startupNum j b * prodGo n (j + 1) (b + eb b)

/-- Started at `b = b_j`, `prodGo n j` is the product of `startupNum (j + i) b_{j + i}` over
`i < n`. -/
theorem prodGo_eq (n j : ℕ) :
    prodGo n j (scale j) = ∏ i ∈ Finset.range n, startupNum (j + i) (scale (j + i)) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [prodGo, ← scale_succ, ih, Finset.prod_range_succ', add_zero, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show j + 1 + i = j + (i + 1) by omega]

/-- Lower bounds for the products over `[j, j + m)` and `[j + m, j + m + n)` multiply to a lower
bound for the product over `[j, j + m + n)`. -/
theorem prodGo_mul_le {m n j L₁ L₂ : ℕ} (h₁ : L₁ ≤ prodGo m j (scale j))
    (h₂ : L₂ ≤ prodGo n (j + m) (scale (j + m))) : L₁ * L₂ ≤ prodGo (m + n) j (scale j) := by
  rw [prodGo_eq] at h₁ h₂ ⊢
  rw [Finset.prod_range_add]
  simp only [← add_assoc] at h₂ ⊢
  exact Nat.mul_le_mul h₁ h₂

end fcStartupProduct

end CollatzPosDens
