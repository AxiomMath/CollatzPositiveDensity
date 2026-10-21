/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Rat.Floor

/-!
# The rational majorant `U^η_c(θ)` of a capped packet factor

For an integer `c`, a rational `θ` and a rounding step `η` (used with `η = 0` and
`η = 10^{-18}`), the rational number `U^η_c(θ)` is defined as follows. If `c < 3` or `c > 16`,
`U^η_c(θ) = 1`. Otherwise let `t = c - 1` and `a_j = 2^j - 1`, and write
`π₀ = 3141592653589793 / 10^15`, `E_cos = (22/7)^26 / 26! + 10^{-15}` and
`P(y) = ∑_{k ≤ 12} (-1)^k y^{2k} / (2k)!`, the Taylor polynomial of `cos` of degree `25`.
For `0 ≤ i < j < t` let `τ_{ij} ∈ [-1/2, 1/2)` be the rational number with
`(a_j - a_i) θ - τ_{ij} ∈ ℤ`, and let `cb_{ij} = 1` if `(a_j - a_i) θ ∈ ℤ`, and otherwise
`cb_{ij}` be `P(2 π₀ τ_{ij}) + E_cos`, rounded up to the grid `η ℤ` when `η > 0`. With `k` the
least natural number such that `k^2 ≥ 10^16 t^{-2} (t + 2 ∑_{i<j<t} cb_{ij})`,
`U^η_c(θ) = min {1, max {k, 1526} / 10^8}`.

The number `cb_{ij}` is an upper bound for `cos (2π (a_j - a_i) θ)`, so `U^η_c(θ)` is an
upper bound for the capped packet factor at `θ`, computable by exact rational arithmetic.

## Main definitions

* `CollatzPosDens.natCeilSqrt`: the least natural number whose square is at least a rational.
* `CollatzPosDens.trCapPi0`, `CollatzPosDens.trCapCosErr`, `CollatzPosDens.trCapCosPoly`:
  the constants `π₀`, `E_cos` and the polynomial `P`.
* `CollatzPosDens.trCapRoundUp`: rounding up to the grid `η ℤ` (no rounding for `η ≤ 0`).
* `CollatzPosDens.trCapCosBound`: the cosine bound `cb`, as a function of `(a_j - a_i) θ`.
* `CollatzPosDens.trCapRadicand`: the quantity `10^16 t^{-2} (t + 2 ∑_{i<j<t} cb_{ij})`.
* `CollatzPosDens.trCapUpper`: the rational majorant `U^η_c(θ)`.

## Main results

* `CollatzPosDens.isLeast_natCeilSqrt`: `natCeilSqrt r` is the least `k` with `r ≤ k^2`.
* `CollatzPosDens.sub_round_mem_Ico`: `x - round x ∈ [-1/2, 1/2)`, so `τ_{ij}` is
  `(a_j - a_i) θ - round ((a_j - a_i) θ)`.
* `CollatzPosDens.trCapUpper_of_mem`, `CollatzPosDens.trCapUpper_of_not_mem`: the two cases.
* `CollatzPosDens.trCapUpper_of_witness`: the value of `U^η_c(θ)` from a square-root witness.
* `CollatzPosDens.trCapUpper_le_one`, `CollatzPosDens.trCapUpper_pos`: `0 < U^η_c(θ) ≤ 1`.

## Implementation notes

The rounding step `η` is an arbitrary rational: for `η > 0` the cosine bound is rounded up to
`η ⌈x / η⌉`, and for `η ≤ 0` it is not rounded. At `η = 10^{-18}` this is
`10^{-18} ⌈10^18 x⌉`, and at `η = 0` it is the exact value. The integer `t` is taken as the
natural number `(c - 1).toNat`, which equals `c - 1` on the range `3 ≤ c ≤ 16` where it is
used. The number `τ_{ij}` is `x - round x` for `x = (a_j - a_i) θ`, and the condition `x ∈ ℤ`
is `Int.fract x = 0`.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-! ### The least natural number whose square bounds a rational -/

/-- The least natural number `k` with `r ≤ k ^ 2`, for a rational `r`. -/
def natCeilSqrt (r : ℚ) : ℕ :=
  if r ≤ 0 then 0 else Nat.sqrt (⌈r⌉.toNat - 1) + 1

/-- `natCeilSqrt r ≤ k` if and only if `r ≤ k ^ 2`. -/
theorem natCeilSqrt_le_iff {r : ℚ} {k : ℕ} : natCeilSqrt r ≤ k ↔ r ≤ (k : ℚ) ^ 2 := by
  unfold natCeilSqrt
  split_ifs with hr
  · exact ⟨fun _ => hr.trans (by positivity), fun _ => Nat.zero_le _⟩
  · rw [not_le] at hr
    have hc : (1 : ℤ) ≤ ⌈r⌉ := Int.one_le_ceil_iff.mpr hr
    have hkq : r ≤ (k : ℚ) ^ 2 ↔ ⌈r⌉ ≤ ((k ^ 2 : ℕ) : ℤ) := by
      rw [Int.ceil_le]; push_cast; rfl
    rw [hkq, Nat.add_one_le_iff, Nat.sqrt_lt, sq, Nat.cast_mul]
    omega

/-- The square of `natCeilSqrt r` is at least `r`. -/
theorem le_natCeilSqrt_sq (r : ℚ) : r ≤ (natCeilSqrt r : ℚ) ^ 2 :=
  natCeilSqrt_le_iff.mp le_rfl

/-- `natCeilSqrt r` is the least natural number `k` with `r ≤ k ^ 2`. -/
theorem isLeast_natCeilSqrt (r : ℚ) :
    IsLeast {k : ℕ | r ≤ (k : ℚ) ^ 2} (natCeilSqrt r) :=
  ⟨le_natCeilSqrt_sq r, fun _ hk => natCeilSqrt_le_iff.mpr hk⟩

/-- `natCeilSqrt r = k` as soon as `(k - 1)^2 < r ≤ k^2` with `k ≥ 1`. -/
theorem natCeilSqrt_eq_of_lt_of_le {r : ℚ} {k : ℕ} (h₁ : ((k : ℚ) - 1) ^ 2 < r)
    (h₂ : r ≤ (k : ℚ) ^ 2) (hk : 1 ≤ k) : natCeilSqrt r = k := by
  refine le_antisymm (natCeilSqrt_le_iff.mpr h₂) ?_
  by_contra h
  rw [not_le] at h
  have := natCeilSqrt_le_iff.mp (Nat.le_sub_one_of_lt h)
  rw [Nat.cast_sub hk, Nat.cast_one] at this
  exact (lt_irrefl _ (h₁.trans_le this))

/-! ### The constants -/

/-- The rational approximation `π₀ = 3141592653589793 / 10^15` of `π` from below. -/
def trCapPi0 : ℚ := 3141592653589793 / 10 ^ 15

/-- The cosine error `E_cos = (22/7)^26 / 26! + 10^{-15}`. -/
def trCapCosErr : ℚ := (22 / 7) ^ 26 / (Nat.factorial 26 : ℚ) + 1 / 10 ^ 15

/-- The Taylor polynomial `P(y) = ∑_{k ≤ 12} (-1)^k y^{2k} / (2k)!` of `cos` of degree `25`. -/
def trCapCosPoly (y : ℚ) : ℚ :=
  ∑ k ∈ range 13, (-1) ^ k * y ^ (2 * k) / ((2 * k).factorial : ℚ)

/-- Rounding up to the grid `η ℤ`: `η ⌈x / η⌉` for `η > 0`, and `x` itself for `η ≤ 0`. -/
def trCapRoundUp (η x : ℚ) : ℚ :=
  if 0 < η then η * ⌈x / η⌉ else x

/-- Rounding up to the grid `η ℤ` does not decrease `x`. -/
theorem le_trCapRoundUp (η x : ℚ) : x ≤ trCapRoundUp η x := by
  unfold trCapRoundUp
  split_ifs with h
  · rw [← div_le_iff₀' h]
    exact Int.le_ceil _
  · exact le_rfl

/-- For `η > 0`, `trCapRoundUp η x = η ⌈x / η⌉`. -/
theorem trCapRoundUp_of_pos {η : ℚ} (h : 0 < η) (x : ℚ) : trCapRoundUp η x = η * ⌈x / η⌉ :=
  ite_eq_left_of_eq_true _ _ (eq_true h)

/-- For `η ≤ 0`, `trCapRoundUp η x = x`. -/
theorem trCapRoundUp_of_nonpos {η : ℚ} (h : η ≤ 0) (x : ℚ) : trCapRoundUp η x = x :=
  ite_eq_right_of_eq_false _ _ (eq_false h.not_gt)

/-! ### The signed fractional part -/

/-- `x - round x` lies in `[-1/2, 1/2)`: it is the number `τ` of the definition. -/
theorem sub_round_mem_Ico (x : ℚ) : x - round x ∈ Set.Ico (-(1 / 2) : ℚ) (1 / 2) := by
  have h := round_eq_iff.mp (rfl : round x = round x)
  rw [Set.mem_Ico] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- `x - round x` differs from `x` by an integer. -/
theorem sub_sub_round (x : ℚ) : x - (x - round x) = (round x : ℚ) := by ring

/-- The number `τ ∈ [-1/2, 1/2)` with `x - τ ∈ ℤ` is unique, and equals `x - round x`. -/
theorem eq_sub_round_of_mem_Ico {x τ : ℚ} {n : ℤ} (hn : x - τ = n)
    (hτ : τ ∈ Set.Ico (-(1 / 2) : ℚ) (1 / 2)) : τ = x - round x := by
  have : round x = n := by
    rw [round_eq_iff, Set.mem_Ico]
    rw [Set.mem_Ico] at hτ
    constructor <;> linarith [hτ.1, hτ.2]
  rw [this, ← hn]
  ring

/-! ### The cosine bound and the majorant -/

/-- The cosine bound `cb` at `x = (a_j - a_i) θ`: `1` if `x ∈ ℤ`, and otherwise
`P(2 π₀ τ) + E_cos` rounded up to the grid `η ℤ`, where `τ = x - round x`. -/
def trCapCosBound (η x : ℚ) : ℚ :=
  if Int.fract x = 0 then 1
  else trCapRoundUp η (trCapCosPoly (2 * trCapPi0 * (x - round x)) + trCapCosErr)

/-- The cosine bound at an integer `x` is `1`. -/
theorem trCapCosBound_of_fract_eq_zero {x : ℚ} (h : Int.fract x = 0) (η : ℚ) :
    trCapCosBound η x = 1 :=
  ite_eq_left_of_eq_true _ _ (eq_true h)

/-- The cosine bound at a non-integer `x` is `P(2 π₀ (x - round x)) + E_cos`, rounded up to the
grid `η ℤ`. -/
theorem trCapCosBound_of_fract_ne_zero {x : ℚ} (h : Int.fract x ≠ 0) (η : ℚ) :
    trCapCosBound η x =
      trCapRoundUp η (trCapCosPoly (2 * trCapPi0 * (x - round x)) + trCapCosErr) :=
  ite_eq_right_of_eq_false _ _ (eq_false h)

/-- The cosine bound at an integer cast `n` is `1`. -/
theorem trCapCosBound_intCast (η : ℚ) (n : ℤ) : trCapCosBound η n = 1 :=
  trCapCosBound_of_fract_eq_zero (Int.fract_intCast n) η

/-- The cosine bound before rounding is at most the cosine bound. -/
theorem le_trCapCosBound {x : ℚ} (h : Int.fract x ≠ 0) (η : ℚ) :
    trCapCosPoly (2 * trCapPi0 * (x - round x)) + trCapCosErr ≤ trCapCosBound η x := by
  rw [trCapCosBound_of_fract_ne_zero h]
  exact le_trCapRoundUp _ _

/-- The radicand `10^16 t^{-2} (t + 2 ∑_{0 ≤ i < j < t} cb_{ij})`, with `a_j = 2^j - 1`. -/
def trCapRadicand (t : ℕ) (η θ : ℚ) : ℚ :=
  10 ^ 16 / (t : ℚ) ^ 2 * (t + 2 * ∑ j ∈ range t, ∑ i ∈ range j,
    trCapCosBound η ((((2 : ℚ) ^ j - 1) - ((2 : ℚ) ^ i - 1)) * θ))

/-- The rational majorant `U^η_c(θ)` of the capped packet factor: `1` unless `3 ≤ c ≤ 16`, and
otherwise `min {1, max {k, 1526} / 10^8}`, where `k` is the least natural number whose square
is at least `trCapRadicand (c - 1) η θ`. -/
@[collatz_pos_dens "def_tr_cap_upper"]
def trCapUpper (c : ℤ) (η θ : ℚ) : ℚ :=
  if 3 ≤ c ∧ c ≤ 16 then
    min 1 (((max (natCeilSqrt (trCapRadicand (c - 1).toNat η θ)) 1526 : ℕ) : ℚ) / 10 ^ 8)
  else 1

/-- For `3 ≤ c ≤ 16`, `U^η_c(θ) = min {1, max {k, 1526} / 10^8}`, where `k` is the least natural
number whose square is at least `trCapRadicand (c - 1) η θ`. -/
theorem trCapUpper_of_mem {c : ℤ} (h₁ : 3 ≤ c) (h₂ : c ≤ 16) (η θ : ℚ) :
    trCapUpper c η θ =
      min 1 (((max (natCeilSqrt (trCapRadicand (c - 1).toNat η θ)) 1526 : ℕ) : ℚ) / 10 ^ 8) :=
  ite_eq_left_of_eq_true _ _ (eq_true ⟨h₁, h₂⟩)

/-- Outside the range `3 ≤ c ≤ 16`, `U^η_c(θ) = 1`. -/
theorem trCapUpper_of_not_mem {c : ℤ} (h : ¬(3 ≤ c ∧ c ≤ 16)) (η θ : ℚ) :
    trCapUpper c η θ = 1 :=
  ite_eq_right_of_eq_false _ _ (eq_false h)

/-- Computing `U^η_c(θ)` from a witness `k` with `(k - 1)^2 < R ≤ k^2`, `R` the radicand. -/
theorem trCapUpper_of_witness {c : ℤ} (h₁ : 3 ≤ c) (h₂ : c ≤ 16) {η θ : ℚ} {k : ℕ}
    (hk : 1 ≤ k) (hlo : ((k : ℚ) - 1) ^ 2 < trCapRadicand (c - 1).toNat η θ)
    (hhi : trCapRadicand (c - 1).toNat η θ ≤ (k : ℚ) ^ 2) :
    trCapUpper c η θ = min 1 (((max k 1526 : ℕ) : ℚ) / 10 ^ 8) := by
  rw [trCapUpper_of_mem h₁ h₂, natCeilSqrt_eq_of_lt_of_le hlo hhi hk]

/-- `U^η_c(θ) ≤ 1`. -/
theorem trCapUpper_le_one (c : ℤ) (η θ : ℚ) : trCapUpper c η θ ≤ 1 := by
  unfold trCapUpper
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- `0 < U^η_c(θ)`. -/
theorem trCapUpper_pos (c : ℤ) (η θ : ℚ) : 0 < trCapUpper c η θ := by
  unfold trCapUpper
  split_ifs
  · refine lt_min one_pos (div_pos ?_ (by positivity))
    exact_mod_cast (show 0 < 1526 by norm_num).trans_le (le_max_right _ _)
  · exact one_pos

end CollatzPosDens
