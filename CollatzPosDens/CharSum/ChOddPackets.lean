/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPacketFn
public import CollatzPosDens.CharSum.ChPacketTable
public import CollatzPosDens.CharSum.ChPiUpper
public import CollatzPosDens.StoppingTrace.TrCosTaylor
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The packet function at odd dyadic cells

For every pair `(s,t)` of the packet envelope table `T_U`, every odd integer `b` and every real
`β` with `|β| ≤ 1/3`, the packet function satisfies `Φ_t((b + β) / 2^s) ≤ U_{s,t}`.

Writing `a_j = 2^j - 1`, the square of the packet function is the cosine polynomial
`Φ_t(θ)^2 = (t + 2 ∑_{i<j<t} cos(2π(2^j - 2^i)θ)) / t^2`. Its numerator is `1`-periodic, even,
and Lipschitz with constant `2 ∑_{i<j<t} 2π(2^j - 2^i)`. Since `b` may be reduced modulo `2^s`
and replaced by `2^s - b`, it suffices to bound the numerator on the finitely many cells
`[(b - 1/3)/2^s, (b + 1/3)/2^s]` with `b` odd and `1 ≤ b ≤ 2^(s-1)`. On each cell this is
done by adaptive bisection: on a segment `[lo, hi]` the numerator is at most the larger of its
values at the endpoints plus half the Lipschitz constant times `hi - lo`, and the endpoint
values are bounded above in fixed point, on the scale `2^64`, by the natural-number cosine bound
`CollatzPosDens.TrDirectCertificate.cosB` (the Taylor polynomial of degree `14` of the cosine at
the approximation `3.141592654` of `π`).

## Main definitions

* `CollatzPosDens.chPacketPairSum t θ`: the cosine polynomial `t + 2 ∑_{i<j<t} cos(2π(2^j-2^i)θ)`.
* `CollatzPosDens.chPairCosB t N Q`: the fixed-point upper bound for the pair sum at `N / Q`.
* `CollatzPosDens.chOddCellsN s t Bn Bd`: the bisection certificate of the cells of `(s,t)`.

## Main results

* `CollatzPosDens.sq_norm_chPacketSum`: the square of the modulus of the packet sum is
  `chPacketPairSum t θ`.
* `CollatzPosDens.chPacketFn_sq`: `Φ_t(θ)^2 = chPacketPairSum t θ / t^2`.
* `CollatzPosDens.chPacketPairSum_le_chPairCosB`: the cosine polynomial at `N / Q` is at most
  `t - t(t - 1) + 2 chPairCosB t N Q / 2^64`.
* `CollatzPosDens.chOddCellsN_sound`: a passing certificate bounds the cosine polynomial on the
  cells.
* `CollatzPosDens.chPacketFn_le_chPacketTable`: `Φ_t((b + β) / 2^s) ≤ U_{s,t}` for
  `(s,t) ∈ T_U`, `b` odd and `|β| ≤ 1/3`.

## Implementation notes

The source bounds the second derivative of `Φ_t^2` and evaluates it on a uniform grid of `256`
or `64` points per cell. We instead use the first-order (Lipschitz) bound together with an
adaptive bisection of each cell, which needs far fewer evaluations; the bisection is carried
out by the kernel, entirely in natural-number arithmetic: the points of the cells of `(s,t)` are
`N / Q` with `Q = 3 · 2^(s+20)`, and the test of a segment is one comparison of natural numbers
with the denominators cleared. The pair `(1,2)`, where `U_{1,2} = 1/2` is attained, is treated
exactly: there `Φ_2(θ)^2 = (1 + cos (2πθ)) / 2` and `cos (2πθ) ≤ -1/2` on `[1/3, 2/3]`.

## References

* [Mazur, *Collatz positive density*].
-/

@[expose] public section

namespace CollatzPosDens

open Real Finset

/-! ### The cosine polynomial `Φ_t^2` -/

/-- The cosine polynomial `t + 2 ∑_{i<j<t} cos(2π(2^j - 2^i)θ)`, the square of the modulus of
the packet sum `∑_{a<t} exp(2πi (2^a - 1) θ)`. -/
noncomputable def chPacketPairSum (t : ℕ) (θ : ℝ) : ℝ :=
  t + 2 * ∑ j ∈ range t, ∑ i ∈ range j, Real.cos (2 * π * (((2 : ℝ) ^ j - 2 ^ i) * θ))

private theorem chPacket_summand_eq (a : ℕ) (θ : ℝ) :
    Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ a - 1) * θ : ℝ)) =
      Complex.exp (((2 * π * (((2 : ℝ) ^ a - 1) * θ) : ℝ) : ℂ) * Complex.I) := by
  congr 1; push_cast; ring

private theorem re_exp_mul_conj_exp (x y : ℝ) :
    (Complex.exp ((x : ℂ) * Complex.I) * (starRingEnd ℂ) (Complex.exp ((y : ℂ) * Complex.I))).re
      = Real.cos (x - y) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
  have : (x : ℂ) * Complex.I + (y : ℂ) * -Complex.I = ((x - y : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-- The square of the modulus of the packet sum is the cosine polynomial `chPacketPairSum`. -/
theorem sq_norm_chPacketSum (t : ℕ) (θ : ℝ) :
    ‖∑ a ∈ range t, Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ a - 1) * θ : ℝ))‖ ^ 2 =
      chPacketPairSum t θ := by
  induction t with
  | zero => simp [chPacketPairSum]
  | succ t ih =>
    rw [sum_range_succ, Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm, ih,
      ← Complex.sq_norm, norm_exp_chPacket_summand, sum_mul, Complex.re_sum]
    have hterm : ∀ i ∈ range t,
        (Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ i - 1) * θ : ℝ)) *
          (starRingEnd ℂ) (Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ t - 1) * θ : ℝ)))).re =
        Real.cos (2 * π * (((2 : ℝ) ^ t - 2 ^ i) * θ)) := by
      intro i _
      rw [chPacket_summand_eq, chPacket_summand_eq, re_exp_mul_conj_exp, ← Real.cos_neg]
      congr 1; ring
    rw [sum_congr rfl hterm]
    simp only [chPacketPairSum, sum_range_succ]
    push_cast
    ring

/-- `Φ_t(θ)^2 = chPacketPairSum t θ / t^2`. -/
theorem chPacketFn_sq (t : ℕ) (θ : ℝ) :
    chPacketFn t θ ^ 2 = chPacketPairSum t θ / (t : ℝ) ^ 2 := by
  rw [chPacketFn, mul_pow, sq_norm_chPacketSum]
  ring

/-- `chPacketPairSum t` is `1`-periodic. -/
theorem chPacketPairSum_add_int (t : ℕ) (θ : ℝ) (n : ℤ) :
    chPacketPairSum t (θ + n) = chPacketPairSum t θ := by
  unfold chPacketPairSum
  congr 2
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  have : 2 * π * (((2 : ℝ) ^ j - 2 ^ i) * (θ + n)) =
      2 * π * (((2 : ℝ) ^ j - 2 ^ i) * θ) + (((2 : ℤ) ^ j - 2 ^ i) * n : ℤ) * (2 * π) := by
    push_cast; ring
  rw [this, Real.cos_add_int_mul_two_pi]

/-- `chPacketPairSum t` is even. -/
theorem chPacketPairSum_neg (t : ℕ) (θ : ℝ) :
    chPacketPairSum t (-θ) = chPacketPairSum t θ := by
  unfold chPacketPairSum
  congr 2
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  rw [mul_neg, mul_neg, Real.cos_neg]

/-- The Lipschitz constant `2 ∑_{i<j<t} (44/7)(2^j - 2^i)` of `chPacketPairSum t`. -/
def chPacketPairSumLip (t : ℕ) : ℚ :=
  2 * ∑ j ∈ range t, ∑ i ∈ range j, 44 / 7 * ((2 : ℚ) ^ j - 2 ^ i)

private theorem two_pow_sub_two_pow_nonneg {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {i j : ℕ} (h : i ∈ range j) : (0 : K) ≤ 2 ^ j - 2 ^ i :=
  sub_nonneg.2 (pow_le_pow_right₀ one_le_two (mem_range.1 h).le)

/-- The Lipschitz constant `chPacketPairSumLip t` is nonnegative. -/
theorem chPacketPairSumLip_nonneg (t : ℕ) : 0 ≤ chPacketPairSumLip t := by
  unfold chPacketPairSumLip
  refine mul_nonneg zero_le_two (sum_nonneg fun j _ => sum_nonneg fun i hi => ?_)
  exact mul_nonneg (by norm_num) (two_pow_sub_two_pow_nonneg hi)

/-- `chPacketPairSum t` is Lipschitz with constant `chPacketPairSumLip t`:
`chPacketPairSum t θ ≤ chPacketPairSum t θ' + chPacketPairSumLip t * |θ - θ'|`. -/
theorem chPacketPairSum_le_add_lip (t : ℕ) (θ θ' : ℝ) :
    chPacketPairSum t θ ≤ chPacketPairSum t θ' + chPacketPairSumLip t * |θ - θ'| := by
  unfold chPacketPairSum chPacketPairSumLip
  push_cast
  rw [mul_assoc, add_assoc, ← mul_add, sum_mul, ← sum_add_distrib]
  gcongr with j hj
  rw [sum_mul, ← sum_add_distrib]
  gcongr with i hi
  have hd : (0 : ℝ) ≤ 2 ^ j - 2 ^ i := two_pow_sub_two_pow_nonneg hi
  have hL := Real.abs_cos_sub_cos_le (2 * π * (((2 : ℝ) ^ j - 2 ^ i) * θ))
    (2 * π * (((2 : ℝ) ^ j - 2 ^ i) * θ'))
  have hπ := pi_lt_twentyTwo_div_seven
  rw [show 2 * π * (((2 : ℝ) ^ j - 2 ^ i) * θ) - 2 * π * (((2 : ℝ) ^ j - 2 ^ i) * θ') =
    (2 * π * (2 ^ j - 2 ^ i)) * (θ - θ') by ring, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π * (2 ^ j - 2 ^ i))] at hL
  have h2 : 2 * π * (2 ^ j - 2 ^ i) * |θ - θ'| ≤ 44 / 7 * ((2 : ℝ) ^ j - 2 ^ i) * |θ - θ'| := by
    gcongr; linarith
  linarith [(abs_le.1 hL).2]

/-! ### Fixed-point bounds for the cosine polynomial -/

/-- `∑_{i<n} f i`, by a recursion that the kernel evaluates directly. -/
def chSumR (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i ih => Nat.add ih (f i)) n

/-- `chSumR n f` is the sum `∑_{i<n} f i`. -/
theorem chSumR_eq (n : ℕ) (f : ℕ → ℕ) : chSumR n f = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_range_succ, ← ih]; rfl

/-- The fixed-point pair sum `∑_{i<j<t} cosB ((2^j - 2^i) N) Q`, an upper bound for
`2^64 ∑_{i<j<t} (1 + cos (2π (2^j - 2^i) N / Q))`. -/
def chPairCosB (t N Q : ℕ) : ℕ :=
  chSumR t fun j => chSumR j fun i =>
    TrDirectCertificate.cosB (Nat.mul (Nat.sub (Nat.pow 2 j) (Nat.pow 2 i)) N) Q

/-- `chPairCosB t N Q` is the double sum `∑_{i<j<t} cosB ((2^j - 2^i) N) Q`. -/
theorem chPairCosB_eq (t N Q : ℕ) : chPairCosB t N Q =
    ∑ j ∈ range t, ∑ i ∈ range j, TrDirectCertificate.cosB ((2 ^ j - 2 ^ i) * N) Q := by
  simp only [chPairCosB, chSumR_eq]
  rfl

private theorem sum_range_sum_range_one (t : ℕ) :
    ∑ j ∈ range t, ∑ _i ∈ range j, (1 : ℝ) = (t : ℝ) * ((t : ℝ) - 1) / 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, ih]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    push_cast
    ring

/-- The cosine polynomial at `N / Q` is at most `t - t (t - 1) + 2 chPairCosB t N Q / 2^64`. -/
theorem chPacketPairSum_le_chPairCosB (t N Q : ℕ) (hQ : 0 < Q) :
    chPacketPairSum t ((N : ℝ) / Q) ≤
      (t : ℝ) - t * (t - 1) + 2 * (chPairCosB t N Q : ℝ) / TrDirectCertificate.one := by
  have hterm : ∀ j ∈ range t, ∀ i ∈ range j,
      Real.cos (2 * π * (((2 : ℝ) ^ j - 2 ^ i) * ((N : ℝ) / Q))) ≤
        (TrDirectCertificate.cosB ((2 ^ j - 2 ^ i) * N) Q : ℝ) / TrDirectCertificate.one - 1 := by
    intro j _ i hi
    have hij : 2 ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (mem_range.1 hi).le
    have h := TrDirectCertificate.cos_le_cosB ((2 ^ j - 2 ^ i) * N) Q hQ
    have harg : (((2 ^ j - 2 ^ i) * N : ℕ) : ℝ) / Q = ((2 : ℝ) ^ j - 2 ^ i) * ((N : ℝ) / Q) := by
      push_cast [Nat.cast_sub hij]
      ring
    rwa [harg] at h
  have hsum : ∑ j ∈ range t, ∑ i ∈ range j,
      Real.cos (2 * π * (((2 : ℝ) ^ j - 2 ^ i) * ((N : ℝ) / Q))) ≤
        ∑ j ∈ range t, ∑ i ∈ range j,
          ((TrDirectCertificate.cosB ((2 ^ j - 2 ^ i) * N) Q : ℝ) / TrDirectCertificate.one - 1) :=
    sum_le_sum fun j hj => sum_le_sum fun i hi => hterm j hj i hi
  have hcount : ∑ j ∈ range t, ∑ i ∈ range j,
      ((TrDirectCertificate.cosB ((2 ^ j - 2 ^ i) * N) Q : ℝ) / TrDirectCertificate.one - 1) =
        (chPairCosB t N Q : ℝ) / TrDirectCertificate.one - (t : ℝ) * ((t : ℝ) - 1) / 2 := by
    rw [chPairCosB_eq, ← sum_range_sum_range_one t]
    push_cast
    simp only [sum_sub_distrib, sum_div]
  unfold chPacketPairSum
  rw [mul_div_assoc]
  linarith

/-- The Lipschitz numerator `88 ∑_{i<j<t} (2^j - 2^i)`: the Lipschitz constant
`chPacketPairSumLip t` is `chLipN t / 7`. -/
def chLipN (t : ℕ) : ℕ :=
  chSumR t fun j => chSumR j fun i => Nat.mul 88 (Nat.sub (Nat.pow 2 j) (Nat.pow 2 i))

/-! ### Adaptive bisection in natural numbers -/

/-- The maximum `a + (b - a)`, by arithmetic that the kernel evaluates directly. -/
def chMax (a b : ℕ) : ℕ := Nat.add a (Nat.sub b a)

/-- The test of a segment `[lo/Q, hi/Q]` with fixed-point pair sums `glo`, `ghi` at its ends,
against the bound `Bn / Bd`: with `G = max glo ghi`, the inequality
`28 Q Bd G + chLipN t 2^64 Bd (hi - lo) < 14 · 2^64 Q (Bn + Bd t (t - 2))`, which is the
inequality `t - t(t - 1) + 2 G / 2^64 + chPacketPairSumLip t (hi - lo) / (2Q) < Bn / Bd` with
the denominators cleared. -/
def chNodeOK (t Q Bn Bd lo hi glo ghi : ℕ) : Bool :=
  Nat.blt (Nat.add (Nat.mul (Nat.mul 28 (Nat.mul Q Bd)) (chMax glo ghi))
      (Nat.mul (Nat.mul (chLipN t) (Nat.mul TrDirectCertificate.one Bd)) (Nat.sub hi lo)))
    (Nat.mul (Nat.mul 14 (Nat.mul TrDirectCertificate.one Q))
      (Nat.add Bn (Nat.mul Bd (Nat.mul t (Nat.sub t 2)))))

/-- Adaptive bisection certificate: `chOddCheckN t Q Bn Bd n lo hi glo ghi` asserts, given the
fixed-point pair sums `glo`, `ghi` at `lo / Q` and `hi / Q`, that `chPacketPairSum t < Bn / Bd`
on `[lo / Q, hi / Q]`, with at most `n` levels of bisection at the points `⌊(lo + hi) / 2⌋ / Q`. -/
def chOddCheckN (t Q Bn Bd : ℕ) (n : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool)
    (fun lo hi glo ghi => chNodeOK t Q Bn Bd lo hi glo ghi)
    (fun _ ih lo hi glo ghi => chNodeOK t Q Bn Bd lo hi glo ghi ||
      (ih lo (Nat.div (Nat.add lo hi) 2) glo (chPairCosB t (Nat.div (Nat.add lo hi) 2) Q) &&
        ih (Nat.div (Nat.add lo hi) 2) hi (chPairCosB t (Nat.div (Nat.add lo hi) 2) Q) ghi)) n

private theorem chPacketPairSumLip_eq (t : ℕ) :
    ((chPacketPairSumLip t : ℚ) : ℝ) = (chLipN t : ℝ) / 7 := by
  have hij : ∀ j ∈ range t, ∀ i ∈ range j, 2 ^ i ≤ 2 ^ j := fun j _ i hi =>
    Nat.pow_le_pow_right (by norm_num) (mem_range.1 hi).le
  have hN : chLipN t = ∑ j ∈ range t, ∑ i ∈ range j, 88 * (2 ^ j - 2 ^ i) := by
    simp only [chLipN, chSumR_eq]
    rfl
  rw [hN, chPacketPairSumLip]
  push_cast
  rw [mul_sum, sum_div]
  refine sum_congr rfl fun j hj => ?_
  rw [mul_sum, sum_div]
  refine sum_congr rfl fun i hi => ?_
  rw [Nat.cast_sub (hij j hj i hi)]
  push_cast
  ring

/-- A segment passing the test `chNodeOK` satisfies the bound. -/
private theorem lt_of_chNodeOK {t Q Bn Bd lo hi glo ghi : ℕ} (ht : 2 ≤ t) (hQ : 0 < Q)
    (hBd : 0 < Bd) (h : chNodeOK t Q Bn Bd lo hi glo ghi = true)
    (hlo : chPacketPairSum t ((lo : ℝ) / Q) ≤
      (t : ℝ) - t * (t - 1) + 2 * (glo : ℝ) / TrDirectCertificate.one)
    (hhi : chPacketPairSum t ((hi : ℝ) / Q) ≤
      (t : ℝ) - t * (t - 1) + 2 * (ghi : ℝ) / TrDirectCertificate.one)
    {θ : ℝ} (h1 : (lo : ℝ) / Q ≤ θ) (h2 : θ ≤ (hi : ℝ) / Q) :
    chPacketPairSum t θ < (Bn : ℝ) / Bd := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlohi : lo ≤ hi := by
    have : (lo : ℝ) ≤ hi := by
      have := h1.trans h2
      rwa [div_le_div_iff_of_pos_right hQ'] at this
    exact_mod_cast this
  have hone : (0 : ℝ) < TrDirectCertificate.one := by
    exact_mod_cast TrDirectCertificate.one_pos
  set G := chMax glo ghi with hG
  have hGmax : G = max glo ghi := by
    rw [hG, chMax]; simp only [Nat.add_eq, Nat.sub_eq]; omega
  have hN : (28 * (Q * Bd) * G + chLipN t * (TrDirectCertificate.one * Bd) * (hi - lo) : ℕ) <
      14 * (TrDirectCertificate.one * Q) * (Bn + Bd * (t * (t - 2))) := by
    simpa [chNodeOK, hG] using h
  have hR : (28 : ℝ) * (Q * Bd) * G + chLipN t * (TrDirectCertificate.one * Bd) * (hi - lo) <
      14 * (TrDirectCertificate.one * Q) * (Bn + Bd * (t * (t - 2))) := by
    have := (Nat.cast_lt (α := ℝ)).2 hN
    push_cast [Nat.cast_sub hlohi, Nat.cast_sub ht] at this
    exact this
  set L := chPacketPairSumLip t with hL
  have hLR : ((L : ℚ) : ℝ) = (chLipN t : ℝ) / 7 := chPacketPairSumLip_eq t
  set gl : ℝ := (t : ℝ) - t * (t - 1) + 2 * (glo : ℝ) / TrDirectCertificate.one
  set gh : ℝ := (t : ℝ) - t * (t - 1) + 2 * (ghi : ℝ) / TrDirectCertificate.one
  have hmax : max gl gh = (t : ℝ) - t * (t - 1) + 2 * (G : ℝ) / TrDirectCertificate.one := by
    rw [hGmax]
    rcases le_total glo ghi with hg | hg
    · have h' : (glo : ℝ) ≤ ghi := by exact_mod_cast hg
      have h'' : gl ≤ gh := by simp only [gl, gh]; gcongr
      rw [max_eq_right h'', max_eq_right hg]
    · have h' : (ghi : ℝ) ≤ glo := by exact_mod_cast hg
      have h'' : gh ≤ gl := by simp only [gl, gh]; gcongr
      rw [max_eq_left h'', max_eq_left hg]
  have hkey : max gl gh + (L : ℝ) * ((hi : ℝ) / Q - (lo : ℝ) / Q) / 2 < (Bn : ℝ) / Bd := by
    have hBd' : (0 : ℝ) < Bd := by exact_mod_cast hBd
    rw [hmax, hLR, lt_div_iff₀ hBd']
    have hD : (0 : ℝ) < 14 * TrDirectCertificate.one * Q := by positivity
    rw [← mul_lt_mul_iff_of_pos_right hD]
    have e : ((t : ℝ) - t * (t - 1) + 2 * (G : ℝ) / TrDirectCertificate.one +
        (chLipN t : ℝ) / 7 * ((hi : ℝ) / Q - (lo : ℝ) / Q) / 2) * Bd *
          (14 * TrDirectCertificate.one * Q) =
        28 * (Q * Bd) * G + chLipN t * (TrDirectCertificate.one * Bd) * (hi - lo) -
          14 * (TrDirectCertificate.one * Q) * (Bd * (t * (t - 2))) := by
      field_simp
      ring
    rw [e]
    nlinarith
  have hLnn : (0 : ℝ) ≤ L := by exact_mod_cast chPacketPairSumLip_nonneg t
  have hmax1 : gl ≤ max gl gh := le_max_left _ _
  have hmax2 : gh ≤ max gl gh := le_max_right _ _
  rcases le_total θ (((lo : ℝ) / Q + (hi : ℝ) / Q) / 2) with hm | hm
  · have := chPacketPairSum_le_add_lip t θ ((lo : ℝ) / Q)
    rw [abs_of_nonneg (by linarith)] at this
    have : (L : ℝ) * (θ - (lo : ℝ) / Q) ≤ L * ((hi : ℝ) / Q - (lo : ℝ) / Q) / 2 := by
      rw [mul_div_assoc]; gcongr; linarith
    linarith
  · have := chPacketPairSum_le_add_lip t θ ((hi : ℝ) / Q)
    rw [abs_of_nonpos (by linarith)] at this
    have : (L : ℝ) * -(θ - (hi : ℝ) / Q) ≤ L * ((hi : ℝ) / Q - (lo : ℝ) / Q) / 2 := by
      rw [mul_div_assoc]; gcongr; linarith
    linarith

/-- If `chOddCheckN t Q Bn Bd n lo hi glo ghi` holds and `glo`, `ghi` are fixed-point upper
bounds for `chPacketPairSum t` at `lo / Q` and `hi / Q`, then `chPacketPairSum t θ < Bn / Bd`
for every `θ ∈ [lo / Q, hi / Q]`. -/
theorem chOddCheckN_sound {t Q Bn Bd : ℕ} (ht : 2 ≤ t) (hQ : 0 < Q) (hBd : 0 < Bd) :
    ∀ {n lo hi glo ghi : ℕ}, chOddCheckN t Q Bn Bd n lo hi glo ghi = true →
      chPacketPairSum t ((lo : ℝ) / Q) ≤
        (t : ℝ) - t * (t - 1) + 2 * (glo : ℝ) / TrDirectCertificate.one →
      chPacketPairSum t ((hi : ℝ) / Q) ≤
        (t : ℝ) - t * (t - 1) + 2 * (ghi : ℝ) / TrDirectCertificate.one →
      ∀ {θ : ℝ}, (lo : ℝ) / Q ≤ θ → θ ≤ (hi : ℝ) / Q → chPacketPairSum t θ < (Bn : ℝ) / Bd
  | 0, lo, hi, glo, ghi, h, hlo, hhi, θ, h1, h2 => lt_of_chNodeOK ht hQ hBd h hlo hhi h1 h2
  | n + 1, lo, hi, glo, ghi, h, hlo, hhi, θ, h1, h2 => by
    change (chNodeOK t Q Bn Bd lo hi glo ghi ||
      (chOddCheckN t Q Bn Bd n lo ((lo + hi) / 2) glo (chPairCosB t ((lo + hi) / 2) Q) &&
        chOddCheckN t Q Bn Bd n ((lo + hi) / 2) hi (chPairCosB t ((lo + hi) / 2) Q) ghi)) =
      true at h
    rw [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hl, hr⟩
    · exact lt_of_chNodeOK ht hQ hBd h hlo hhi h1 h2
    · have hm := chPacketPairSum_le_chPairCosB t ((lo + hi) / 2) Q hQ
      rcases le_total θ ((((lo + hi) / 2 : ℕ) : ℝ) / Q) with h3 | h3
      · exact chOddCheckN_sound ht hQ hBd hl hlo hm h1 h3
      · exact chOddCheckN_sound ht hQ hBd hr hm hhi h3 h2

/-- `all` over `k < n`, by a recursion that the kernel evaluates directly. -/
def chAllR (n : ℕ) (p : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && p k) n

/-- If `chAllR n p` holds, then `p k` holds for every `k < n`. -/
theorem chAllR_spec {n : ℕ} {p : ℕ → Bool} (h : chAllR n p = true) {k : ℕ} (hk : k < n) :
    p k = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    change (chAllR n p && p n) = true at h
    rw [Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ih h.1 hk
    · exact h.2

/-- The certificate for a pair `(s,t)` with bound `Bn / Bd`: for every odd `b = 2k + 1 ≤ 2^(s-1)`,
bisection with `20` levels proves `chPacketPairSum t < Bn / Bd` on the cell
`[(b - 1/3)/2^s, (b + 1/3)/2^s] = [(6k + 2) 2^20 / Q, (6k + 4) 2^20 / Q]`, `Q = 3 · 2^(s+20)`. -/
def chOddCellsN (s t Bn Bd : ℕ) : Bool :=
  chAllR ((2 ^ (s - 1) + 1) / 2) fun k =>
    chOddCheckN t (Nat.mul 3 (Nat.pow 2 (Nat.add s 20))) Bn Bd 20
      (Nat.mul (Nat.add (Nat.mul 6 k) 2) 1048576) (Nat.mul (Nat.add (Nat.mul 6 k) 4) 1048576)
      (chPairCosB t (Nat.mul (Nat.add (Nat.mul 6 k) 2) 1048576)
        (Nat.mul 3 (Nat.pow 2 (Nat.add s 20))))
      (chPairCosB t (Nat.mul (Nat.add (Nat.mul 6 k) 4) 1048576)
        (Nat.mul 3 (Nat.pow 2 (Nat.add s 20))))

/-- If the certificate `chOddCellsN s t Bn Bd` holds, then `chPacketPairSum t θ < Bn / Bd` for
every odd `b = 2k + 1 ≤ 2^(s-1)` and every `θ ∈ [(b - 1/3)/2^s, (b + 1/3)/2^s]`. -/
theorem chOddCellsN_sound {s t Bn Bd : ℕ} (ht : 2 ≤ t) (hBd : 0 < Bd)
    (h : chOddCellsN s t Bn Bd = true) {k : ℕ} (hk : 2 * k + 1 ≤ 2 ^ (s - 1)) {θ : ℝ}
    (h1 : (2 * k + 1 - 1 / 3) / 2 ^ s ≤ θ) (h2 : θ ≤ (2 * k + 1 + 1 / 3) / 2 ^ s) :
    chPacketPairSum t θ < (Bn : ℝ) / Bd := by
  have hc := chAllR_spec h (k := k) (by omega)
  simp only [Nat.mul_eq, Nat.add_eq, Nat.pow_eq] at hc
  have hQ : 0 < 3 * 2 ^ (s + 20) := by positivity
  have hcell : ∀ c : ℕ, (((6 * k + c) * 1048576 : ℕ) : ℝ) / ((3 * 2 ^ (s + 20) : ℕ) : ℝ) =
      (6 * k + c) / (3 * 2 ^ s) := by
    intro c
    push_cast
    rw [pow_add]
    field_simp
    ring
  refine chOddCheckN_sound ht hQ hBd hc (chPacketPairSum_le_chPairCosB _ _ _ hQ)
    (chPacketPairSum_le_chPairCosB _ _ _ hQ) ?_ ?_
  · rw [hcell]
    refine le_trans (le_of_eq ?_) h1
    field_simp
    ring
  · rw [hcell]
    refine h2.trans (le_of_eq ?_)
    field_simp
    ring

/-- Reduction of an odd numerator: the value of `chPacketPairSum t` at `(b + β) / 2^s` is its
value at a point of a cell `[(2k + 1 - 1/3)/2^s, (2k + 1 + 1/3)/2^s]` with `2k + 1 ≤ 2^(s-1)`. -/
theorem chPacketPairSum_odd_reduce {s : ℕ} (hs : 1 ≤ s) (t : ℕ) {b : ℤ} (hb : Odd b) {β : ℝ}
    (hβ : |β| ≤ 1 / 3) :
    ∃ k : ℕ, 2 * k + 1 ≤ 2 ^ (s - 1) ∧ ∃ θ : ℝ, (2 * k + 1 - 1 / 3) / 2 ^ s ≤ θ ∧
      θ ≤ (2 * k + 1 + 1 / 3) / 2 ^ s ∧
        chPacketPairSum t ((b + β) / 2 ^ s) = chPacketPairSum t θ := by
  obtain ⟨m, rfl⟩ := hb
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set N : ℤ := 2 ^ s with hN
  have hNpos : 0 < N := by positivity
  set q := (2 * m + 1) / (2 * N)
  set r := (2 * m + 1) % (2 * N)
  have hdiv : 2 * N * q + r = 2 * m + 1 := by
    exact Int.mul_ediv_add_emod (2 * m + 1) (2 * N)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hr1 : r < 2 * N := Int.emod_lt_of_pos _ (by omega)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, r = 2 * k + 1 := ⟨(r - 1) / 2, by
    have : r = 2 * m + 1 - 2 * (N * q) := by rw [← hdiv]; ring
    omega⟩
  have hNR : ((N : ℤ) : ℝ) = (2 : ℝ) ^ s := by rw [hN]; push_cast; ring
  have hpow : (2 : ℝ) ^ (s + 1) = 2 * N := by rw [hNR]; ring
  have hβ' := abs_le.1 hβ
  have hdivR : ((2 * m + 1 : ℤ) : ℝ) = 2 * N * q + r := by exact_mod_cast hdiv.symm
  have hk0 : 0 ≤ k := by omega
  rcases le_or_gt r N with hrN | hrN
  · refine ⟨k.toNat, ?_, (r + β) / 2 ^ (s + 1), ?_, ?_, ?_⟩
    · have : ((2 * k.toNat + 1 : ℕ) : ℤ) ≤ N := by push_cast; omega
      exact_mod_cast (show ((2 * k.toNat + 1 : ℕ) : ℤ) ≤ ((2 ^ s : ℕ) : ℤ) by
        rw [hN] at this; exact_mod_cast this)
    · have hkR : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0
      rw [hkR, hk]; push_cast; gcongr; linarith
    · have hkR : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0
      rw [hkR, hk]; push_cast; gcongr; linarith
    · rw [← chPacketPairSum_add_int t ((r + β) / 2 ^ (s + 1)) q, hdivR, hpow]
      congr 1
      field_simp
      ring
  · obtain ⟨k', hk'⟩ : ∃ k' : ℤ, 2 * N - r = 2 * k' + 1 := ⟨N - k - 1, by omega⟩
    have hk'0 : 0 ≤ k' := by omega
    refine ⟨k'.toNat, ?_, (2 * N - r - β) / 2 ^ (s + 1), ?_, ?_, ?_⟩
    · have : ((2 * k'.toNat + 1 : ℕ) : ℤ) ≤ N := by push_cast; omega
      exact_mod_cast (show ((2 * k'.toNat + 1 : ℕ) : ℤ) ≤ ((2 ^ s : ℕ) : ℤ) by
        rw [hN] at this; exact_mod_cast this)
    · have hkR : ((k'.toNat : ℕ) : ℝ) = (k' : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk'0
      have hk'R : (2 * N - r : ℝ) = 2 * k' + 1 := by exact_mod_cast hk'
      rw [hkR, sub_sub, ← sub_sub, hk'R]; gcongr; linarith
    · have hkR : ((k'.toNat : ℕ) : ℝ) = (k' : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk'0
      have hk'R : (2 * N - r : ℝ) = 2 * k' + 1 := by exact_mod_cast hk'
      rw [hkR, sub_sub, ← sub_sub, hk'R]; gcongr; linarith
    · rw [← chPacketPairSum_neg t ((2 * N - r - β) / 2 ^ (s + 1)), ← chPacketPairSum_add_int t
        (-((2 * N - r - β) / 2 ^ (s + 1))) (q + 1), hdivR, hpow]
      congr 1
      push_cast
      field_simp
      ring

/-! ### The bound -/

private theorem chPacketFn_le_of_pairSum_le {t : ℕ} (ht : 1 ≤ t) {θ : ℝ} {u : ℝ} (hu : 0 ≤ u)
    (h : chPacketPairSum t θ ≤ (t : ℝ) ^ 2 * u ^ 2) : chPacketFn t θ ≤ u := by
  have htR : (0 : ℝ) < (t : ℝ) ^ 2 := by positivity
  have hsq : chPacketFn t θ ^ 2 ≤ u ^ 2 := by
    rw [chPacketFn_sq, div_le_iff₀ htR]; linarith
  exact (pow_le_pow_iff_left₀ (chPacketFn_nonneg t θ) hu two_ne_zero).1 hsq

/-- The exact case `(s,t) = (1,2)`: `chPacketPairSum 2 θ = 2 + 2 cos (2πθ) ≤ 1` on
`[1/3, 2/3]`. -/
private theorem chPacketPairSum_two_le {θ : ℝ} (h1 : 1 / 3 ≤ θ) (h2 : θ ≤ 2 / 3) :
    chPacketPairSum 2 θ ≤ 1 := by
  have hc : Real.cos (2 * π * θ) ≤ -(1 / 2) := by
    have hx : |2 * π * θ - π| ≤ π / 3 := by
      rw [abs_le]; constructor <;> nlinarith [Real.pi_pos]
    have hcos : Real.cos (π / 3) ≤ Real.cos (2 * π * θ - π) := by
      rw [← Real.cos_abs (2 * π * θ - π)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hx
    rw [Real.cos_pi_div_three, Real.cos_sub_pi] at hcos
    linarith
  simp only [chPacketPairSum, sum_range_succ, sum_range_zero]
  norm_num
  linarith

private theorem chOddCells_1_3 : chOddCellsN 1 3 31329 10000 = true := by
  decide +kernel

private theorem chOddCells_1_4 : chOddCellsN 1 4 63504 15625 = true := by
  decide +kernel

private theorem chOddCells_2_2 : chOddCellsN 2 2 751689 250000 = true := by
  decide +kernel

private theorem chOddCells_2_3 : chOddCellsN 2 3 3017169 1000000 = true := by
  decide +kernel

private theorem chOddCells_2_4 : chOddCellsN 2 4 97969 15625 = true := by
  decide +kernel

private theorem chOddCells_3_2 : chOddCellsN 3 2 9330207649 2500000000 = true := by
  decide +kernel

private theorem chOddCells_3_3 : chOddCellsN 3 3 144 25 = true := by
  decide +kernel

private theorem chOddCells_3_4 : chOddCellsN 3 4 11449 2500 = true := by
  decide +kernel

private theorem chOddCells_4_2 : chOddCellsN 4 2 61504 15625 = true := by
  decide +kernel

private theorem chOddCells_4_3 : chOddCellsN 4 3 80782713729 10000000000 = true := by
  decide +kernel

private theorem chOddCells_4_4 : chOddCellsN 4 4 961 100 = true := by
  decide +kernel

private theorem chOddCells_5_2 : chOddCellsN 5 2 2489311449 625000000 = true := by
  decide +kernel

private theorem chOddCells_5_3 : chOddCellsN 5 3 342287001 39062500 = true := by
  decide +kernel

private theorem chOddCells_5_4 : chOddCellsN 5 4 8829045369 625000000 = true := by
  decide +kernel

private theorem chOddCells_6_2 : chOddCellsN 6 2 39957211449 10000000000 = true := by
  decide +kernel

private theorem chOddCells_6_3 : chOddCellsN 6 3 2182664961 244140625 = true := by
  decide +kernel

private theorem chOddCells_6_4 : chOddCellsN 6 4 242399660281 15625000000 = true := by
  decide +kernel

private theorem chOddCells_6_5 : chOddCellsN 6 5 881721 40000 = true := by
  decide +kernel

private theorem chOddCells_7_6 : chOddCellsN 7 6 19881 625 = true := by
  decide +kernel

private theorem chOddCells_8_7 : chOddCellsN 8 7 43573201 1000000 = true := by
  decide +kernel

/-- For every `(s,t) ∈ T_U`, every odd integer `b` and every real `β` with `|β| ≤ 1/3`,
`Φ_t((b + β) / 2^s) ≤ U_{s,t}`. -/
@[collatz_pos_dens "lem_ch_odd_packets"]
theorem chPacketFn_le_chPacketTable {s t : ℕ} (hst : (s, t) ∈ chPacketTableDomain) {b : ℤ}
    (hb : Odd b) {β : ℝ} (hβ : |β| ≤ 1 / 3) :
    chPacketFn t ((b + β) / 2 ^ s) ≤ chPacketTable s t := by
  obtain ⟨hs, ht⟩ := mem_chPacketTableDomain_bounds hst
  obtain ⟨k, hk, θ, h1, h2, hθ⟩ := chPacketPairSum_odd_reduce hs t hb hβ
  refine chPacketFn_le_of_pairSum_le (by omega)
    (by exact_mod_cast (chPacketTable_pos hst).le) ?_
  rw [hθ]
  have key : ∀ Bn Bd : ℕ, chOddCellsN s t Bn Bd = true →
      (Bn : ℝ) / Bd = (t : ℝ) ^ 2 * ((chPacketTable s t : ℚ) : ℝ) ^ 2 → 0 < Bd →
      chPacketPairSum t θ ≤ (t : ℝ) ^ 2 * ((chPacketTable s t : ℚ) : ℝ) ^ 2 := by
    intro Bn Bd hc hB hBd
    rw [← hB]
    exact (chOddCellsN_sound ht hBd hc hk h1 h2).le
  simp only [chPacketTableDomain, mem_insert, mem_singleton, Prod.mk.injEq] at hst
  rcases hst with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h <;> obtain ⟨rfl, rfl⟩ := h
  · obtain rfl : k = 0 := by simp at hk; omega
    norm_num at h1 h2
    norm_num [chPacketTable]
    exact chPacketPairSum_two_le h1 h2
  exacts [key _ _ chOddCells_1_3 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_1_4 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_2_2 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_2_3 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_2_4 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_3_2 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_3_3 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_3_4 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_4_2 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_4_3 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_4_4 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_5_2 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_5_3 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_5_4 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_6_2 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_6_3 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_6_4 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_6_5 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_7_6 (by norm_num [chPacketTable]) (by norm_num),
    key _ _ chOddCells_8_7 (by norm_num [chPacketTable]) (by norm_num)]

end CollatzPosDens
