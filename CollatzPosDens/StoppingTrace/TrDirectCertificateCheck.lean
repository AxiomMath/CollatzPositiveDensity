/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCapFactor
public import CollatzPosDens.StoppingTrace.TrCapPairBound
public import CollatzPosDens.StoppingTrace.TrCosTaylor
public import CollatzPosDens.Transfer.EpsStar

/-!
# Fixed-point upper bounds for capped packet factors

This file provides natural-number computations, on the scale `2^64`, of upper bounds for the
cosines `cos (2π x)` at rational points, for the capped packet factors `Φ^cap_c(θ)` and for the
white test, together with their soundness.

For natural numbers `P` and `Q > 0`, the bound `CollatzPosDens.TrDirectCertificate.cosB P Q` is
an upper bound for `2^64 (1 + cos (2π P/Q))`.
With the reduction `α = |P/Q - ⌊P/Q + 1/2⌋| = A/(2Q)`, it is
`⌈2^64 max {0, 1 + K(α)}⌉ + 18446744074` if `2A ≤ Q` and
`⌈2^64 max {0, 1 - K(1/2 - α)}⌉ + 18446744074` otherwise, where
`K(y) = ∑_{k=0}^{7} (-1)^k (6283185308 y / 10^9)^{2k} / (2k)!` is evaluated as one fraction of
natural numbers; the bound `CollatzPosDens.abs_cos_two_pi_sub_cosTaylorSum_le` on a quarter
turn makes it sound.

For a point `θ_n = 9^r X / (X_D 2^n)` (with `X`, `X_D` natural numbers), an *entry*
(`CollatzPosDens.TrDirectCertificate.Entry`) records upper bounds for the pair sums
`∑_{i<j<t} cos (2π (2^j - 2^i) θ_n)`, `t ≤ 7`, and the resulting bounds for the capped factors
`Φ^cap_c(θ_n)`, `3 ≤ c ≤ 8`, given by `CollatzPosDens.trCapFactor_le_of_pairSum_le`. Since
`2 θ_n = θ_{n-1}`, the pair sum of length `t + 1` at `θ_n` is the sum of `t` new cosines
`cos (2π (2^j - 1) θ_n)`, `1 ≤ j ≤ t`, and the pair sum of length `t` at `θ_{n-1}`; the entries
are therefore computed by a recursion on `n`, with six new cosines per step.

## Main definitions

* `CollatzPosDens.TrDirectCertificate.sqrtUp`: an upper bound for the square root.
* `CollatzPosDens.TrDirectCertificate.capB`: the bound for a capped factor from a pair-sum bound.
* `CollatzPosDens.TrDirectCertificate.mkEntry`, `CollatzPosDens.TrDirectCertificate.specEntry`:
  one step of the entry recursion, and the entries at `θ_0, θ_1, …`.

## Main results

* `CollatzPosDens.TrDirectCertificate.trCapFactor_le_capB`: the factor bound from a pair-sum
  bound.
* `CollatzPosDens.TrDirectCertificate.pairCos_le_specEntry`,
  `CollatzPosDens.TrDirectCertificate.trCapFactor_le_specEntry`: the entries are sound.
* `CollatzPosDens.TrDirectCertificate.specEntry_congr`: the entries at `θ_n` depend on `X` only
  modulo `X_D 2^n`.

## Implementation notes

All computations use the primitive operations `Nat.add`, `Nat.mul`, `Nat.div`, … rather than
the arithmetic notation, so that the kernel evaluates them directly; each definition is
restated with the notation by `rfl`.

## References

* [Mazur, *Collatz positive density*], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrDirectCertificate

open Real Finset

/-! ### Square roots and the factor bound -/

/-- A power of two near `√N`, for `N < 2^72` (any value is admissible). -/
def sqrtGuess (N : ℕ) : ℕ :=
  cond (Nat.blt N 68719476736)
    (cond (Nat.blt N 262144)
      (cond (Nat.blt N 256)
        (cond (Nat.blt N 16)
          (cond (Nat.blt N 4)
            (2)
            (4))
          (cond (Nat.blt N 64)
            (8)
            (16)))
        (cond (Nat.blt N 4096)
          (cond (Nat.blt N 1024)
            (32)
            (64))
          (cond (Nat.blt N 16384)
            (128)
            (cond (Nat.blt N 65536)
              (256)
              (512)))))
      (cond (Nat.blt N 67108864)
        (cond (Nat.blt N 4194304)
          (cond (Nat.blt N 1048576)
            (1024)
            (2048))
          (cond (Nat.blt N 16777216)
            (4096)
            (8192)))
        (cond (Nat.blt N 1073741824)
          (cond (Nat.blt N 268435456)
            (16384)
            (32768))
          (cond (Nat.blt N 4294967296)
            (65536)
            (cond (Nat.blt N 17179869184)
              (131072)
              (262144))))))
    (cond (Nat.blt N 18014398509481984)
      (cond (Nat.blt N 17592186044416)
        (cond (Nat.blt N 1099511627776)
          (cond (Nat.blt N 274877906944)
            (524288)
            (1048576))
          (cond (Nat.blt N 4398046511104)
            (2097152)
            (4194304)))
        (cond (Nat.blt N 281474976710656)
          (cond (Nat.blt N 70368744177664)
            (8388608)
            (16777216))
          (cond (Nat.blt N 1125899906842624)
            (33554432)
            (cond (Nat.blt N 4503599627370496)
              (67108864)
              (134217728)))))
      (cond (Nat.blt N 4611686018427387904)
        (cond (Nat.blt N 288230376151711744)
          (cond (Nat.blt N 72057594037927936)
            (268435456)
            (536870912))
          (cond (Nat.blt N 1152921504606846976)
            (1073741824)
            (2147483648)))
        (cond (Nat.blt N 73786976294838206464)
          (cond (Nat.blt N 18446744073709551616)
            (4294967296)
            (8589934592))
          (cond (Nat.blt N 295147905179352825856)
            (17179869184)
            (cond (Nat.blt N 1180591620717411303424)
              (34359738368)
              (68719476736))))))

/-- One Newton step `⌊(g + ⌊N/g⌋)/2⌋` for `√N`. -/
def newtonStep (N g : ℕ) : ℕ := Nat.div (Nat.add g (Nat.div N g)) 2

/-- For `g > 0`, `⌈(N + g^2) / (2g)⌉` is at least `√N` (arithmetic-geometric mean). -/
theorem le_sq_ceilDiv (N g : ℕ) (hg : 0 < g) : N ≤ ((N + g * g + 2 * g - 1) / (2 * g)) ^ 2 := by
  set s := (N + g * g + 2 * g - 1) / (2 * g) with hs
  have h1 : N + g * g ≤ s * (2 * g) := by
    have := Nat.lt_div_mul_add (a := N + g * g + 2 * g - 1) (b := 2 * g) (by omega)
    rw [← hs] at this
    omega
  have h1' : ((N : ℤ) + g * g) ≤ s * (2 * g) := by exact_mod_cast h1
  have hg' : (0 : ℤ) < g := by exact_mod_cast hg
  by_contra hc
  have hc' : (s : ℤ) ^ 2 < N := by exact_mod_cast not_le.1 hc
  have hN : (0 : ℤ) ≤ N := by positivity
  have hs0 : (0 : ℤ) ≤ s := by positivity
  nlinarith [sq_nonneg ((N : ℤ) - g * g), mul_le_mul h1' h1' (by positivity) (by positivity)]

/-- An upper bound for `√N`: three Newton steps from `sqrtGuess N`, then one rounded-up step. -/
def sqrtUp (N : ℕ) : ℕ :=
  let g := Nat.succ (newtonStep N (newtonStep N (newtonStep N (sqrtGuess N))))
  Nat.div (Nat.sub (Nat.add (Nat.add N (Nat.mul g g)) (Nat.mul 2 g)) 1) (Nat.mul 2 g)

/-- `sqrtUp N` is an upper bound for `√N`: `N ≤ (sqrtUp N)^2`. -/
theorem le_sqrtUp_sq (N : ℕ) : N ≤ sqrtUp N ^ 2 :=
  le_sq_ceilDiv N _ (Nat.succ_pos _)

/-- The bound `min {2^64, max {⌈2^32 √M / t⌉, 2^48}}` for a capped factor, where
`M = t 2^64 + 2 S - t (t - 1) 2^64`. -/
def capB (t S : ℕ) : ℕ :=
  let M := Nat.sub (Nat.add (Nat.mul t one) (Nat.mul 2 S)) (Nat.mul (Nat.mul t (Nat.sub t 1)) one)
  let V := Nat.div (Nat.sub (Nat.add (Nat.mul (sqrtUp M) 4294967296) t) 1) t
  cond (Nat.ble one V) one (cond (Nat.ble V 281474976710656) 281474976710656 V)

/-- `capB` written with the arithmetic notation. -/
theorem capB_eq (t S : ℕ) : capB t S =
    let V := (sqrtUp (t * one + 2 * S - t * (t - 1) * one) * 4294967296 + t - 1) / t
    if one ≤ V then one else if V ≤ 281474976710656 then 281474976710656 else V := by
  simp only [capB, cond_eq_ite, Nat.ble_eq]
  rfl

/-- The pair sum `∑_{i<j<t} cos (2π (2^j - 2^i) θ)`. -/
noncomputable def pairCos (t : ℕ) (θ : ℝ) : ℝ :=
  ∑ j ∈ range t, ∑ i ∈ range j, Real.cos (2 * π * (((2 : ℝ) ^ j - 2 ^ i) * θ))

/-- The pair sum of length `1` vanishes. -/
theorem pairCos_one (θ : ℝ) : pairCos 1 θ = 0 := by simp [pairCos]

/-- The pair sum of length `t + 1` at `θ` is the sum of the `t` cosines
`cos (2π (2^{j+1} - 1) θ)` and the pair sum of length `t` at `2θ`. -/
theorem pairCos_succ (t : ℕ) (θ : ℝ) :
    pairCos (t + 1) θ =
      ∑ j ∈ range t, Real.cos (2 * π * (((2 : ℝ) ^ (j + 1) - 1) * θ)) + pairCos t (2 * θ) := by
  simp only [pairCos]
  rw [sum_range_succ', sum_range_zero, add_zero]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_range_succ', pow_zero, add_comm]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  congr 2
  ring

/-- **The factor bound.** If the pair sum of length `t` at `θ` is at most
`S / 2^64 - t (t - 1) / 2`, then `Φ^cap_{t+1}(θ) ≤ capB t S / 2^64`: with `M = t 2^64 + 2S -
t (t - 1) 2^64 ≤ sqrtUp(M)^2`, this is `CollatzPosDens.trCapFactor_le_of_pairSum_le` with
`u = sqrtUp(M) / 2^32`, rounded up. -/
theorem trCapFactor_le_capB {t : ℕ} (ht2 : 2 ≤ t) (ht : t ≤ 15) (θ : ℝ) (S : ℕ)
    (h : pairCos t θ ≤ (S : ℝ) / one - t * (t - 1) / 2) :
    trCapFactor (t + 1 : ℕ) θ ≤ (capB t S : ℝ) / one := by
  have hone : (0 : ℝ) < one := by exact_mod_cast one_pos
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  set M := t * one + 2 * S - t * (t - 1) * one with hM
  have hMr : (t : ℝ) * one + 2 * S - t * (t - 1) * one ≤ M := by
    have := sub_le_natSub (K := ℝ) (t * one + 2 * S) (t * (t - 1) * one)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ t)] at this
    push_cast at this
    simpa [hM] using this
  set u := sqrtUp M with hu
  have hu2 : (M : ℝ) ≤ (u : ℝ) ^ 2 := by exact_mod_cast le_sqrtUp_sq M
  have hone' : (one : ℝ) = 4294967296 ^ 2 := by norm_num [one]
  have hc : (((t + 1 : ℕ) : ℤ) : ℝ) - 1 = t := by push_cast; ring
  have hb := trCapFactor_le_of_pairSum_le (c := ((t + 1 : ℕ) : ℤ)) (by omega) (by omega)
    (θ := θ) (S := (S : ℝ) / one - t * (t - 1) / 2) (u := (u : ℝ) / 4294967296) (by positivity)
    (by rw [show (((t + 1 : ℕ) : ℤ) - 1).toNat = t by omega]; exact h)
    (by
      rw [hc, div_pow, ← hone']
      have e : (t : ℝ) + 2 * ((S : ℝ) / one - t * (t - 1) / 2) =
          ((t : ℝ) * one + 2 * S - t * (t - 1) * one) / one := by
        field_simp
        ring
      rw [e]
      exact div_le_div_of_nonneg_right (hMr.trans hu2) hone.le)
  rw [hc] at hb
  refine hb.trans ?_
  set V := (u * 4294967296 + t - 1) / t with hV
  have hVge : (u : ℝ) / 4294967296 / t ≤ (V : ℝ) / one := by
    have h1 := div_le_ceilDiv (K := ℝ) (u * 4294967296) t (by omega)
    rw [← hV] at h1
    have : (u : ℝ) / 4294967296 / t = ((u * 4294967296 : ℕ) : ℝ) / t / one := by
      push_cast; rw [hone']; field_simp
    rw [this]
    gcongr
  have h16 : (2 : ℝ) ^ (-16 : ℤ) = 281474976710656 / one := by norm_num [one]
  rw [capB_eq]
  simp only
  rw [← hM, ← hu, ← hV]
  split_ifs with h1 h2
  · rw [div_self hone.ne']
    exact min_le_left _ _
  · rw [h16]
    refine (min_le_right _ _).trans (max_le (hVge.trans ?_) le_rfl)
    gcongr
  · rw [h16]
    refine (min_le_right _ _).trans (max_le hVge ?_)
    gcongr
    exact_mod_cast (not_le.1 h2).le

/-! ### Entries -/

/-- An entry: pair-sum bounds `p_t` (`2 ≤ t ≤ 7`), factor bounds `c_c` (`3 ≤ c ≤ 8`) and the
white bit, at one point `θ_n`. -/
structure Entry where
  /-- pair-sum bound for `t = 2` -/
  p2 : ℕ
  /-- pair-sum bound for `t = 3` -/
  p3 : ℕ
  /-- pair-sum bound for `t = 4` -/
  p4 : ℕ
  /-- pair-sum bound for `t = 5` -/
  p5 : ℕ
  /-- pair-sum bound for `t = 6` -/
  p6 : ℕ
  /-- pair-sum bound for `t = 7` -/
  p7 : ℕ
  /-- factor bound for `c = 3` -/
  c3 : ℕ
  /-- factor bound for `c = 4` -/
  c4 : ℕ
  /-- factor bound for `c = 5` -/
  c5 : ℕ
  /-- factor bound for `c = 6` -/
  c6 : ℕ
  /-- factor bound for `c = 7` -/
  c7 : ℕ
  /-- factor bound for `c = 8` -/
  c8 : ℕ
  /-- the white bit -/
  wh : Bool

/-- The entry below level `0`. -/
def Entry.zero : Entry := ⟨0, 0, 0, 0, 0, 0, one, one, one, one, one, one, false⟩

/-- The white test `ε_* Q + 9^r < dist(Y, Q ℤ)` in natural numbers (`z = 9^r`). -/
def whiteB (Y Q z : ℕ) : Bool :=
  let f := Nat.mod Y Q
  let g := Nat.sub Q f
  Nat.blt (Nat.add (Nat.mul 37037 Q) (Nat.mul 1000000 z))
    (Nat.mul 1000000 (cond (Nat.ble f g) f g))

/-- `whiteB` written with the arithmetic notation. -/
theorem whiteB_eq (Y Q z : ℕ) :
    whiteB Y Q z = decide (37037 * Q + 1000000 * z < 1000000 * min (Y % Q) (Q - Y % Q)) := by
  simp only [whiteB, cond_eq_ite, Nat.ble_eq, min_def]
  rfl

/-- One step of the entry recursion at `θ_n = 9^r X / (X_D 2^n)`, from the entry `e` at
`θ_{n-1}`. -/
def mkEntry (X XD r n : ℕ) (e : Entry) : Entry :=
  let Q := Nat.mul XD (Nat.pow 2 n)
  let Y := Nat.mul (Nat.pow 9 r) X
  let s1 := cosB Y Q
  let s2 := Nat.add s1 (cosB (Nat.mul 3 Y) Q)
  let s3 := Nat.add s2 (cosB (Nat.mul 7 Y) Q)
  let s4 := Nat.add s3 (cosB (Nat.mul 15 Y) Q)
  let s5 := Nat.add s4 (cosB (Nat.mul 31 Y) Q)
  let s6 := Nat.add s5 (cosB (Nat.mul 63 Y) Q)
  let p3 := Nat.add s2 e.p2
  let p4 := Nat.add s3 e.p3
  let p5 := Nat.add s4 e.p4
  let p6 := Nat.add s5 e.p5
  let p7 := Nat.add s6 e.p6
  ⟨s1, p3, p4, p5, p6, p7, capB 2 s1, capB 3 p3, capB 4 p4, capB 5 p5, capB 6 p6, capB 7 p7,
    whiteB Y Q (Nat.pow 9 r)⟩

/-- The entries at `θ_0, θ_1, …`. -/
def specEntry (X XD r : ℕ) : ℕ → Entry
  | 0 => mkEntry X XD r 0 Entry.zero
  | n + 1 => mkEntry X XD r (n + 1) (specEntry X XD r n)

/-- The pair-sum bound of an entry, `p_t` (and `0` for `t ≤ 1`). -/
def Entry.p (e : Entry) : ℕ → ℕ
  | 2 => e.p2
  | 3 => e.p3
  | 4 => e.p4
  | 5 => e.p5
  | 6 => e.p6
  | 7 => e.p7
  | _ => 0

/-- The factor bound of an entry, `c_c` (and `2^64` outside `3 ≤ c ≤ 8`). -/
def Entry.cap (e : Entry) : ℕ → ℕ
  | 3 => e.c3
  | 4 => e.c4
  | 5 => e.c5
  | 6 => e.c6
  | 7 => e.c7
  | 8 => e.c8
  | _ => one

/-- The cosine sums `s_t = ∑_{j<t} cosB ((2^{j+1} - 1) Y) Q`. -/
def cosSum (Y Q t : ℕ) : ℕ := ∑ j ∈ range t, cosB ((2 ^ (j + 1) - 1) * Y) Q

/-- For `1 ≤ t ≤ 6`, the pair-sum bound `p_{t+1}` of `mkEntry X XD r n e` is the cosine sum
`s_t` at level `n` plus the bound `p_t` of `e`. -/
theorem mkEntry_p {X XD r n : ℕ} (e : Entry) {t : ℕ} (ht1 : 1 ≤ t) (ht : t ≤ 6) :
    (mkEntry X XD r n e).p (t + 1) =
      cosSum (9 ^ r * X) (XD * 2 ^ n) t + e.p t := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by
    omega
  all_goals
    simp only [mkEntry, Entry.p, cosSum, sum_range_succ, sum_range_zero, Nat.add_eq, Nat.mul_eq,
      Nat.pow_eq]
    norm_num
    try ring

/-- For `2 ≤ t ≤ 7`, the factor bound `c_{t+1}` of `mkEntry X XD r n e` is `capB t p_t`. -/
theorem mkEntry_cap {X XD r n : ℕ} (e : Entry) {t : ℕ} (ht2 : 2 ≤ t) (ht : t ≤ 7) :
    (mkEntry X XD r n e).cap (t + 1) = capB t ((mkEntry X XD r n e).p t) := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
    omega
  all_goals rfl

/-- The white bit of `mkEntry X XD r n e` is the white test at `θ_n`. -/
theorem mkEntry_wh (X XD r n : ℕ) (e : Entry) :
    (mkEntry X XD r n e).wh = whiteB (9 ^ r * X) (XD * 2 ^ n) (9 ^ r) := rfl

/-- The entry at `θ_{n+1}` is one step of the recursion from the entry at `θ_n`. -/
theorem specEntry_succ (X XD r n : ℕ) :
    specEntry X XD r (n + 1) = mkEntry X XD r (n + 1) (specEntry X XD r n) := rfl

/-- The point `θ_n = 9^r X / (X_D 2^n)`. -/
noncomputable def theta (X XD r n : ℕ) : ℝ := (9 ^ r * X : ℕ) / (XD * 2 ^ n : ℕ)

/-- `2 θ_{n+1} = θ_n`. -/
theorem two_mul_theta (X XD r n : ℕ) : 2 * theta X XD r (n + 1) = theta X XD r n := by
  simp only [theta]
  push_cast
  rw [pow_succ]
  rcases eq_or_ne (XD : ℝ) 0 with h | h
  · simp [h]
  · field_simp

/-- For `X_D > 0`, `∑_{j<t} cos (2π (2^{j+1} - 1) θ_n) ≤ s_t / 2^64 - t`. -/
theorem cos_le_cosSum (X XD r n t : ℕ) (hXD : 0 < XD) :
    ∑ j ∈ range t, Real.cos (2 * π * (((2 : ℝ) ^ (j + 1) - 1) * theta X XD r n)) ≤
      (cosSum (9 ^ r * X) (XD * 2 ^ n) t : ℝ) / one - t := by
  simp only [cosSum]
  push_cast
  have ht : (t : ℝ) = ∑ _j ∈ range t, (1 : ℝ) := by simp
  rw [div_eq_mul_inv, Finset.sum_mul, ht, ← sum_sub_distrib]
  refine sum_le_sum fun j _ => ?_
  rw [← div_eq_mul_inv]
  have hQ : 0 < XD * 2 ^ n := by positivity
  have h := cos_le_cosB ((2 ^ (j + 1) - 1) * (9 ^ r * X)) (XD * 2 ^ n) hQ
  have h1 : (1 : ℕ) ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  rw [Nat.cast_mul, Nat.cast_sub h1] at h
  push_cast at h
  simp only [theta]
  push_cast
  convert h using 3
  ring

/-- **Soundness of the entries.** For `2 ≤ t ≤ 7` with `t ≤ n + 2`, the pair sum of length `t`
at `θ_n` is at most `p_t / 2^64 - t (t - 1) / 2`. -/
theorem pairCos_le_specEntry (X XD r : ℕ) (hXD : 0 < XD) :
    ∀ n t, 2 ≤ t → t ≤ 7 → t ≤ n + 2 →
      pairCos t (theta X XD r n) ≤ ((specEntry X XD r n).p t : ℝ) / one - t * (t - 1) / 2 := by
  intro n
  induction n with
  | zero =>
    intro t ht2 ht7 htn
    obtain rfl : t = 2 := by omega
    have h := pairCos_succ 1 (theta X XD r 0)
    rw [pairCos_one, add_zero] at h
    rw [h]
    have := cos_le_cosSum X XD r 0 1 hXD
    have hp : (specEntry X XD r 0).p 2 = cosSum (9 ^ r * X) (XD * 2 ^ 0) 1 + Entry.zero.p 1 :=
      mkEntry_p (t := 1) Entry.zero le_rfl (by norm_num)
    rw [hp]
    simp only [Entry.p, add_zero]
    norm_num at this ⊢
    linarith
  | succ n ih =>
    intro t ht2 ht7 htn
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have h := pairCos_succ t (theta X XD r (n + 1))
    rw [two_mul_theta] at h
    rw [h]
    have hc := cos_le_cosSum X XD r (n + 1) t hXD
    have hp : (specEntry X XD r (n + 1)).p (t + 1) =
        cosSum (9 ^ r * X) (XD * 2 ^ (n + 1)) t + (specEntry X XD r n).p t := by
      rw [specEntry_succ]
      exact mkEntry_p _ (by omega) (by omega)
    rw [hp]
    push_cast
    rcases Nat.lt_or_ge t 2 with ht | ht
    · obtain rfl : t = 1 := by omega
      rw [pairCos_one]
      simp only [Entry.p]
      norm_num at hc ⊢
      linarith
    · have := ih t ht (by omega) (by omega)
      rw [add_div]
      linarith

/-- For `2 ≤ t ≤ 7`, the factor bound `c_{t+1}` of the entry at `θ_n` is `capB t p_t`. -/
theorem specEntry_cap (X XD r n : ℕ) {t : ℕ} (ht2 : 2 ≤ t) (ht : t ≤ 7) :
    (specEntry X XD r n).cap (t + 1) = capB t ((specEntry X XD r n).p t) := by
  cases n <;> exact mkEntry_cap _ ht2 ht

/-- The white bit of the entry at `θ_n` is the white test at `θ_n`. -/
theorem specEntry_wh (X XD r n : ℕ) :
    (specEntry X XD r n).wh = whiteB (9 ^ r * X) (XD * 2 ^ n) (9 ^ r) := by
  cases n <;> rfl

/-- **The factor bounds of the entries.** For `3 ≤ c ≤ 8` with `c ≤ n + 3`,
`Φ^cap_c(θ_n) ≤ c_c / 2^64`. -/
theorem trCapFactor_le_specEntry (X XD r n c : ℕ) (hXD : 0 < XD) (hc3 : 3 ≤ c) (hc8 : c ≤ 8)
    (hcn : c ≤ n + 3) :
    trCapFactor c (theta X XD r n) ≤ ((specEntry X XD r n).cap c : ℝ) / one := by
  obtain ⟨t, rfl⟩ : ∃ t, c = t + 1 := ⟨c - 1, by omega⟩
  rw [specEntry_cap _ _ _ _ (by omega) (by omega)]
  exact trCapFactor_le_capB (by omega) (by omega) _ _
    (pairCos_le_specEntry X XD r hXD n t (by omega) (by omega) (by omega))

/-- An entry step depends on `X` only modulo `X_D 2^n`. -/
theorem mkEntry_congr {X X' XD r n : ℕ} (h : X ≡ X' [MOD XD * 2 ^ n]) (e : Entry) :
    mkEntry X XD r n e = mkEntry X' XD r n e := by
  have hY : 9 ^ r * X ≡ 9 ^ r * X' [MOD XD * 2 ^ n] := h.mul_left _
  have hw : whiteB (9 ^ r * X) (XD * 2 ^ n) (9 ^ r) = whiteB (9 ^ r * X') (XD * 2 ^ n) (9 ^ r) := by
    rw [whiteB_eq, whiteB_eq, show 9 ^ r * X % (XD * 2 ^ n) = 9 ^ r * X' % (XD * 2 ^ n) from hY]
  simp only [mkEntry, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [cosB_congr hY, cosB_congr (hY.mul_left 3), cosB_congr (hY.mul_left 7),
    cosB_congr (hY.mul_left 15), cosB_congr (hY.mul_left 31), cosB_congr (hY.mul_left 63), hw]

/-- The entries depend on `X` only modulo `X_D 2^n`. -/
theorem specEntry_congr {X X' XD r : ℕ} :
    ∀ n, X ≡ X' [MOD XD * 2 ^ n] → specEntry X XD r n = specEntry X' XD r n := by
  intro n
  induction n with
  | zero => intro h; exact mkEntry_congr h _
  | succ n ih =>
    intro h
    have h' : X ≡ X' [MOD XD * 2 ^ n] :=
      Nat.ModEq.of_dvd (Nat.mul_dvd_mul_left _ (pow_dvd_pow 2 (Nat.le_succ n))) h
    rw [specEntry_succ, specEntry_succ, ih h', mkEntry_congr h]

end TrDirectCertificate

end CollatzPosDens
