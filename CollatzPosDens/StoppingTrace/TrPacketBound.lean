/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChOddPackets
public import CollatzPosDens.StoppingTrace.TrPacketDeficit

/-!
# The packet bound

Let `b` be an odd integer, `β` a real number with `|β| ≤ 1/3`, and `θ` a real number with
`θ - (b + β) / 2^o ∈ ℤ`. Then the packet function of length `c - 1` satisfies
`Φ_{c-1}(θ) ≤ 1 - δ^{pk}_{c,o}`, where `δ^{pk}_{c,o}` is the packet deficit.

Write `ζ_k = exp(2πi (2^k - 1) θ)`. By downward induction on `i ≤ c - 1` one shows
`|∑_{k=i}^{c-2} ζ_k| ≤ (c - 1 - i) - F_{c,o}(i)`, where `F_{c,o}` is the packet value. A step
`F_{c,o}(i) = F_{c,o}(i+1)` uses `|ζ_i| = 1`. A jump
`F_{c,o}(i) = t (1 - U_{o-i,t}) + F_{c,o}(i+t)` uses that the block `∑_{k=i}^{i+t-1} ζ_k` has
modulus `t Φ_t(2^i θ)`, that `2^i θ - (b + β) / 2^{o-i} ∈ ℤ`, that `Φ_t` is `1`-periodic, and the
odd packet bound `Φ_t((b + β)/2^{o-i}) ≤ U_{o-i,t}`.

## Main results

* `CollatzPosDens.norm_sum_range_chPacket_shift`: the block of length `t` starting at `i` has
  modulus `t Φ_t(2^i θ)`.
* `CollatzPosDens.norm_sum_Ico_chPacket_le_trPacketValue`: the downward induction bound.
* `CollatzPosDens.chPacketFn_le_one_sub_trPacketDeficit`: `Φ_{c-1}(θ) ≤ 1 - δ^{pk}_{c,o}`.

## Implementation notes

The statement holds for all natural numbers `c, o`, without assuming `3 ≤ c ≤ 16` or
`1 ≤ o ≤ c`. Only jumps with `(o - i, t) ∈ T_U` enter the recursion, and these force
`i < o`, so the truncated subtraction `o - i` is the integer one.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

public section

namespace CollatzPosDens

open Complex Real Finset

/-- The block `∑_{a<t} exp(2πi (2^{i+a} - 1) θ)` has modulus `t Φ_t(2^i θ)`. -/
theorem norm_sum_range_chPacket_shift (t i : ℕ) (θ : ℝ) :
    ‖∑ a ∈ range t, Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ (i + a) - 1) * θ : ℝ))‖ =
      t * chPacketFn t (2 ^ i * θ) := by
  have h : ∀ a : ℕ, Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ (i + a) - 1) * θ : ℝ)) =
      Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ i - 1) * θ : ℝ)) *
        Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ a - 1) * (2 ^ i * θ) : ℝ)) := by
    intro a
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [h, ← mul_sum, norm_mul, norm_exp_chPacket_summand, one_mul]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · rw [chPacketFn, ← mul_assoc, mul_one_div_cancel (by positivity), one_mul]

/-- The downward induction of the packet bound: for `i ≤ c - 1`,
`|∑_{k=i}^{c-2} exp(2πi (2^k - 1) θ)| ≤ (c - 1 - i) - F_{c,o}(i)`. -/
theorem norm_sum_Ico_chPacket_le_trPacketValue (c o : ℕ) {b : ℤ} (hb : Odd b) {β : ℝ}
    (hβ : |β| ≤ 1 / 3) {θ : ℝ} {m : ℤ} (hθ : θ - (b + β) / 2 ^ o = m) {i : ℕ}
    (hi : i ≤ c - 1) :
    ‖∑ k ∈ Ico i (c - 1), Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ k - 1) * θ : ℝ))‖ ≤
      ((c - 1 - i : ℕ) : ℝ) - (trPacketValue c o i : ℝ) := by
  obtain ⟨j, hj⟩ : ∃ j, j = c - 1 - i := ⟨_, rfl⟩
  induction j using Nat.strong_induction_on generalizing i with
  | _ j ih =>
  rcases eq_or_lt_of_le hi with rfl | hlt
  · simp
  rcases trPacketValue_eq_or_exists c o hlt with hF | ⟨t, ht1, ht2, hT, hF⟩
  · rw [Finset.sum_eq_sum_Ico_succ_bot hlt, hF]
    have hrec := ih (c - 1 - (i + 1)) (by omega) (i := i + 1) (by omega) rfl
    have hn : c - 1 - i = (c - 1 - (i + 1)) + 1 := by omega
    rw [hn, Nat.cast_add, Nat.cast_one]
    refine (norm_add_le _ _).trans ?_
    rw [norm_exp_chPacket_summand]
    linarith
  · rw [← Finset.sum_Ico_consecutive _ (by omega : i ≤ i + t) ht2]
    have hrec := ih (c - 1 - (i + t)) (by omega) (i := i + t) (by omega) rfl
    have hn : c - 1 - i = (c - 1 - (i + t)) + t := by omega
    have hio : i < o := by have := (mem_chPacketTableDomain_bounds hT).1; omega
    have hshift : (2 : ℝ) ^ i * θ = (b + β) / 2 ^ (o - i) + ((2 ^ i * m : ℤ) : ℝ) := by
      obtain ⟨s, rfl⟩ : ∃ s, o = i + s := ⟨o - i, by omega⟩
      rw [show θ = (b + β) / 2 ^ (i + s) + m by linarith, Nat.add_sub_cancel_left, pow_add]
      push_cast
      field_simp
    have hU := chPacketFn_le_chPacketTable hT hb hβ
    have hblock :
        ‖∑ k ∈ Ico i (i + t),
            Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ k - 1) * θ : ℝ))‖ ≤
          t * (chPacketTable (o - i) t : ℝ) := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
        norm_sum_range_chPacket_shift, hshift, chPacketFn_add_intCast]
      exact mul_le_mul_of_nonneg_left hU (by positivity)
    have hF' : (trPacketValue c o i : ℝ) =
        t * (1 - (chPacketTable (o - i) t : ℝ)) + (trPacketValue c o (i + t) : ℝ) := by
      rw [hF]; push_cast; ring
    rw [hn, Nat.cast_add, hF']
    refine (norm_add_le _ _).trans ?_
    linarith

/-- **Packet bound.** If `b` is odd, `|β| ≤ 1/3` and `θ - (b + β)/2^o ∈ ℤ`, then
`Φ_{c-1}(θ) ≤ 1 - δ^{pk}_{c,o}`. -/
@[collatz_pos_dens "lem_tr_packet_bound"]
theorem chPacketFn_le_one_sub_trPacketDeficit (c o : ℕ) {b : ℤ} (hb : Odd b) {β : ℝ}
    (hβ : |β| ≤ 1 / 3) {θ : ℝ} (hθ : ∃ m : ℤ, θ - (b + β) / 2 ^ o = m) :
    chPacketFn (c - 1) θ ≤ 1 - (trPacketDeficit c o : ℝ) := by
  obtain ⟨m, hm⟩ := hθ
  rcases c with _ | _ | n
  · simp [chPacketFn, trPacketDeficit, trPacketValue, trPacketValueList]
  · simp [chPacketFn, trPacketDeficit]
  have key := norm_sum_Ico_chPacket_le_trPacketValue (n + 1 + 1) o hb hβ hm (i := 0) (by omega)
  rw [← Finset.range_eq_Ico] at key
  simp only [Nat.sub_zero] at key
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [chPacketFn, trPacketDeficit]
  push_cast at key ⊢
  rw [show (n : ℝ) + 1 + 1 - 1 = n + 1 by ring, one_div, inv_mul_le_iff₀ hn,
    mul_sub, mul_one, mul_div_cancel₀ _ hn.ne']
  linarith

end CollatzPosDens
