/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChRawFactor
public import CollatzPosDens.CharSum.ChAngleShift

/-!
# Bounding a raw factor by disjoint sub-packets

Fix `n : ℕ`, `ξ ∈ G_n`, an integer `c ≥ 2` and `p ∈ 𝒫`, and put `θ = ϑ_{n,ξ}(p)`. Then
`(c - 1) φ_c(p) = |∑_{m=0}^{c-2} e(2^m - 1) θ|`. Let `S` be a finite set of pairs `(k, t)` with
`k + t ≤ c - 1` whose index blocks `{k, …, k + t - 1}` are pairwise disjoint. Splitting the sum
along these blocks and the remaining indices, the triangle inequality bounds each remaining
summand by `1`, while the block indexed by `(k, t)` is, up to a unimodular factor, the packet sum
of length `t` at the angle `ϑ_{n,ξ}(p - (0, k))`, because `ϑ(p - (0, k)) - 2^k θ ∈ ℤ`. Hence
`(c - 1) φ_c(p) ≤ (c - 1) - ∑ t + ∑ t φ_{t+1}(p - (0, k))`.

## Main results

* `CollatzPosDens.chRawFactor_le_packets`: the packet bound for the raw factor.

## Implementation notes

Pairs with `t = 0` are allowed: such a pair contributes `0` to both sides.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- The summand `exp(2πi (2^a - 1) θ)` of the packet sum. -/
private noncomputable def packetTerm (θ : ℝ) (a : ℕ) : ℂ :=
  Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ a - 1) * θ : ℝ))

private theorem packetTerm_add (θ θ' : ℝ) (k j : ℕ) (m : ℤ) (h : θ' - 2 ^ k * θ = m) :
    packetTerm θ (k + j) = packetTerm θ k * packetTerm θ' j := by
  have hθ' : θ' = 2 ^ k * θ + m := by linarith
  have hint : (((2 : ℝ) ^ j - 1) * m : ℝ) = (((2 ^ j - 1) * m : ℤ) : ℝ) := by push_cast; ring
  unfold packetTerm
  rw [← Complex.exp_add]
  have : 2 * π * Complex.I * ((((2 : ℝ) ^ k - 1) * θ : ℝ) : ℂ) +
      2 * π * Complex.I * ((((2 : ℝ) ^ j - 1) * θ' : ℝ) : ℂ) =
      2 * π * Complex.I * ((((2 : ℝ) ^ (k + j) - 1) * θ : ℝ) : ℂ) +
        (((2 ^ j - 1) * m : ℤ) : ℂ) * (2 * π * Complex.I) := by
    rw [hθ']
    push_cast
    ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private theorem norm_packetTerm (θ : ℝ) (a : ℕ) : ‖packetTerm θ a‖ = 1 :=
  norm_exp_chPacket_summand a θ

/-- `t Φ_t(θ)` is the modulus of the packet sum of length `t`. -/
private theorem mul_chPacketFn (t : ℕ) (θ : ℝ) :
    (t : ℝ) * chPacketFn t θ = ‖∑ a ∈ Finset.range t, packetTerm θ a‖ := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have : (t : ℝ) ≠ 0 := by positivity
  rw [chPacketFn_def, ← mul_assoc, mul_one_div_cancel this, one_mul]
  rfl

/-- **Packet bound.** For `c ≥ 2`, `p ∈ 𝒫` and a finite set `S` of pairs `(k, t)` with
`k + t ≤ c - 1` whose index blocks `{k, …, k + t - 1}` are pairwise disjoint,
`(c - 1) φ_c(p) ≤ (c - 1) - ∑_{(k,t) ∈ S} t + ∑_{(k,t) ∈ S} t φ_{t+1}(p - (0, k))`. -/
@[collatz_pos_dens "lem_ch_packet_bound"]
theorem chRawFactor_le_packets (n : ℕ) (ξ : ResidueGroup n) {c : ℤ} (hc : 2 ≤ c)
    {p : ℤ × ℤ} (hp : p ∈ bkPoints) (S : Finset (ℕ × ℕ))
    (hS : ∀ kt ∈ S, ((kt.1 + kt.2 : ℕ) : ℤ) ≤ c - 1)
    (hdisj : (S : Set (ℕ × ℕ)).PairwiseDisjoint fun kt => Finset.Ico kt.1 (kt.1 + kt.2)) :
    ((c : ℝ) - 1) * chRawFactor n ξ c p ≤
      ((c : ℝ) - 1) - ∑ kt ∈ S, (kt.2 : ℝ) +
        ∑ kt ∈ S, (kt.2 : ℝ) * chRawFactor n ξ ((kt.2 : ℤ) + 1) (p - (0, (kt.1 : ℤ))) := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, c = (N : ℤ) + 1 := ⟨(c - 1).toNat, by omega⟩
  have hN : 1 ≤ N := by omega
  have hcR : (((N : ℤ) + 1 : ℤ) : ℝ) - 1 = N := by push_cast; ring
  rw [hcR, chRawFactor_natCast_add_one n ξ hN, mul_chPacketFn]
  set θ := bkTheta n ξ p
  set f := packetTerm θ
  set T := S.biUnion fun kt => Finset.Ico kt.1 (kt.1 + kt.2)
  have hT : T ⊆ Finset.range N := by
    intro m hm
    obtain ⟨kt, hkt, hm⟩ := Finset.mem_biUnion.1 hm
    have := hS kt hkt
    simp only [Finset.mem_Ico] at hm
    simp only [Finset.mem_range]
    omega
  have hcardT : (T.card : ℝ) = ∑ kt ∈ S, (kt.2 : ℝ) := by
    rw [Finset.card_biUnion hdisj]
    push_cast
    simp
  have hcardU : (((Finset.range N) \ T).card : ℝ) = N - ∑ kt ∈ S, (kt.2 : ℝ) := by
    rw [Finset.card_sdiff_of_subset hT, Nat.cast_sub (Finset.card_le_card hT), hcardT,
      Finset.card_range]
  -- each block is a packet sum at the shifted angle
  have hblock : ∀ kt ∈ S, ‖∑ m ∈ Finset.Ico kt.1 (kt.1 + kt.2), f m‖ =
      (kt.2 : ℝ) * chRawFactor n ξ ((kt.2 : ℤ) + 1) (p - (0, (kt.1 : ℤ))) := by
    intro kt _
    obtain ⟨k, t⟩ := kt
    obtain ⟨m, hm⟩ := bkTheta_sub_shift_mem_int n ξ hp k
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    rw [chRawFactor_natCast_add_one n ξ ht, mul_chPacketFn, Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel_left]
    simp only
    rw [Finset.sum_congr rfl fun j _ => packetTerm_add θ _ k j m hm, ← Finset.mul_sum,
      norm_mul, norm_packetTerm, one_mul]
  calc ‖∑ a ∈ Finset.range N, f a‖
      = ‖∑ a ∈ (Finset.range N) \ T, f a + ∑ kt ∈ S, ∑ m ∈ Finset.Ico kt.1 (kt.1 + kt.2), f m‖ := by
        rw [← Finset.sum_biUnion hdisj, Finset.sum_sdiff hT]
    _ ≤ ∑ a ∈ (Finset.range N) \ T, ‖f a‖ +
          ∑ kt ∈ S, ‖∑ m ∈ Finset.Ico kt.1 (kt.1 + kt.2), f m‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))
    _ = _ := by
        rw [Finset.sum_congr rfl fun a _ => norm_packetTerm θ a, Finset.sum_const, nsmul_eq_mul,
          mul_one, hcardU, Finset.sum_congr rfl hblock]

end CollatzPosDens
