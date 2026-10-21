/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3NarrowCells
public import CollatzPosDens.Case3.C3NarrowDeficit
public import CollatzPosDens.StoppingTrace.TrCapFactor

/-!
# The narrow factor

Let `3 ≤ c ≤ 16` and `o ≥ 1` be integers, `b` an odd integer and `β` a real number with
`|β| ≤ 10⁻⁶`. At the odd dyadic angle `θ = (b + β)/2^o` the capped factor satisfies
`Φ^cap_c(θ) ≤ 1 - δ'_{c,o}`, where `δ'_{c,o}` is the narrow deficit.

With `𝔞 = e^{2πiθ}`, the normalised packet sum is `(c - 1) Φ_{c-1}(θ) = |∑_{k<c-1} 𝔞^{2^k-1}|`.
Split it along a packet family `𝒦` attaining the maximal packet deficit `a_{c,o}`: on the packet
`{i, …, i + t - 1}` the sum has modulus at most `t U'_{o-i,t}` by the narrow cell estimates, and
every other term has modulus `1`. Hence `Φ_{c-1}(θ) ≤ 1 - a_{c,o}/(c - 1)`, and since
`Φ^cap_c(θ) = max (Φ_{c-1}(θ), 2^{-16})` and `δ'_{c,o} = min (a_{c,o}/(c - 1), 1 - 2^{-16})`, the
claim follows.

## Main results

* `CollatzPosDens.norm_sum_le_card_sub_sum_of_pairwiseDisjoint`: splitting a sum of terms of
  norm at most `1` along pairwise disjoint blocks.
* `CollatzPosDens.chPacketFn_le_one_sub_c3PacketWeight`: the packet function at an odd dyadic
  angle is at most `1 - (weight of 𝒦)/N` for every packet family `𝒦`.
* `CollatzPosDens.trCapFactor_le_one_sub_c3NarrowDeficit`: the narrow factor bound
  `Φ^cap_c((b + β)/2^o) ≤ 1 - δ'_{c,o}`.

## Implementation notes

No upper bound `o ≤ c` is needed: the result is stated for every `o ≥ 1`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- Splitting a sum along pairwise disjoint blocks `S k ⊆ s`, `k ∈ K`, of terms of norm at most
`1`: `‖∑_{i ∈ s} f i‖ ≤ #s - ∑_{k ∈ K} (#S k - ‖∑_{i ∈ S k} f i‖)`. -/
theorem norm_sum_le_card_sub_sum_of_pairwiseDisjoint {ι κ E : Type*}
    [SeminormedAddCommGroup E] {s : Finset ι} {K : Finset κ} {S : κ → Finset ι}
    (hS : ∀ k ∈ K, S k ⊆ s) (hd : (K : Set κ).PairwiseDisjoint S) {f : ι → E}
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ s.card - ∑ k ∈ K, (((S k).card : ℝ) - ‖∑ i ∈ S k, f i‖) := by
  classical
  have hU : K.biUnion S ⊆ s := Finset.biUnion_subset.2 hS
  have hcard : ((s \ K.biUnion S).card : ℝ) + ∑ k ∈ K, ((S k).card : ℝ) = s.card := by
    rw [← Nat.cast_sum, ← Finset.card_biUnion hd]
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hU
  have h1 : ‖∑ i ∈ s \ K.biUnion S, f i‖ ≤ (s \ K.biUnion S).card := by
    refine (norm_sum_le _ _).trans ?_
    simpa using Finset.sum_le_sum fun i hi => hf i (Finset.sdiff_subset hi)
  have h2 : ‖∑ i ∈ K.biUnion S, f i‖ ≤ ∑ k ∈ K, ‖∑ i ∈ S k, f i‖ := by
    rw [Finset.sum_biUnion hd]
    exact norm_sum_le _ _
  rw [← Finset.sum_sdiff hU, Finset.sum_sub_distrib]
  linarith [norm_add_le (∑ i ∈ s \ K.biUnion S, f i) (∑ i ∈ K.biUnion S, f i)]

/-- One packet of the packet sum at an odd dyadic angle: for `i, t ∈ ℕ`, `(s, t) ∈ T'` with
`o = i + s`, `b` odd and `|β| ≤ 10⁻⁶`, the terms `k ∈ {i, …, i + t - 1}` of the packet sum at
`ϑ = (b + β)/2^o` have sum of modulus at most `t U'_{s,t}`. -/
theorem norm_sum_Ico_exp_le_c3NarrowTable {i t s o : ℕ} (hso : o = i + s)
    (hst : ((s : ℤ), (t : ℤ)) ∈ c3NarrowTableDomain) {b : ℤ} (hb : Odd b) {β : ℝ}
    (hβ : |β| ≤ 1 / 10 ^ 6) :
    ‖∑ a ∈ Finset.Ico i (i + t),
        Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ a - 1) * ((b + β) / 2 ^ o) : ℝ))‖ ≤
      (t : ℝ) * c3NarrowTable s t := by
  have hcell := norm_sum_exp_le_c3NarrowTable hst hb hβ
  simp only [Int.toNat_natCast, zpow_natCast, Int.cast_natCast] at hcell
  refine le_of_eq_of_le ?_ hcell
  rw [Finset.sum_Ico_eq_sum_range, add_tsub_cancel_left]
  have hterm : ∀ m ∈ Finset.range t,
      Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ (i + m) - 1) * ((b + β) / 2 ^ o) : ℝ)) =
        Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ i - 1) * ((b + β) / 2 ^ o) : ℝ)) *
          Complex.exp (2 * π * Complex.I * ((2 ^ m - 1) * ((b + β) / (2 : ℂ) ^ s))) := by
    intro m _
    rw [← Complex.exp_add]
    congr 1
    push_cast
    rw [hso, pow_add, pow_add]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, norm_mul, norm_exp_chPacket_summand,
    one_mul]

/-- **The packet bound.** Let `N ≥ 1`, `o ∈ ℕ`, `𝒦` a packet family for `(N + 1, o)`, `b` odd and
`|β| ≤ 10⁻⁶`. Then `Φ_N((b + β)/2^o) ≤ 1 - W/N`, where `W = ∑_{(i,t) ∈ 𝒦} t (1 - U'_{o-i,t})` is
the weight of `𝒦`. -/
theorem chPacketFn_le_one_sub_c3PacketWeight {N o : ℕ} (hN : 1 ≤ N) {K : Finset (ℤ × ℤ)}
    (hK : IsC3PacketFamily ((N : ℤ) + 1) o K) {b : ℤ} (hb : Odd b) {β : ℝ}
    (hβ : |β| ≤ 1 / 10 ^ 6) :
    chPacketFn N ((b + β) / 2 ^ o) ≤ 1 - (c3PacketWeight o K : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set θ : ℝ := (b + β) / 2 ^ o with hθ
  set f : ℕ → ℂ := fun a => Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ a - 1) * θ : ℝ))
  set S : ℤ × ℤ → Finset ℕ := fun p => Finset.Ico p.1.toNat (p.1.toNat + p.2.toNat)
  have hS : ∀ p ∈ K, S p ⊆ Finset.range N := by
    intro p hp x hx
    obtain ⟨h0, h1, h2⟩ := hK.1 p hp
    have := (mem_c3NarrowTableDomain_bounds h2).2.2.1
    simp only [S, Finset.mem_Ico] at hx
    simp only [Finset.mem_range]
    omega
  have hd : (K : Set (ℤ × ℤ)).PairwiseDisjoint S := by
    intro p hp q hq hpq
    have hdis := hK.2 p hp q hq hpq
    refine Finset.disjoint_left.2 fun x hx hx' =>
      (Finset.disjoint_left.1 hdis) (show (x : ℤ) ∈ Finset.Ico p.1 (p.1 + p.2) from ?_) ?_
    · obtain ⟨h0, -, h2⟩ := hK.1 p hp
      have := (mem_c3NarrowTableDomain_bounds h2).2.2.1
      simp only [S, Finset.mem_Ico] at hx
      simp only [Finset.mem_Ico]
      omega
    · obtain ⟨h0, -, h2⟩ := hK.1 q hq
      have := (mem_c3NarrowTableDomain_bounds h2).2.2.1
      simp only [S, Finset.mem_Ico] at hx'
      simp only [Finset.mem_Ico]
      omega
  have hmain := norm_sum_le_card_sub_sum_of_pairwiseDisjoint hS hd (f := f)
    (fun a _ => (norm_exp_chPacket_summand a θ).le)
  have hpacket : ∀ p ∈ K, (p.2 : ℝ) * (1 - (c3NarrowTable (o - p.1) p.2 : ℝ)) ≤
      ((S p).card : ℝ) - ‖∑ a ∈ S p, f a‖ := by
    intro p hp
    obtain ⟨h0, -, h2⟩ := hK.1 p hp
    obtain ⟨hs1, -, ht2, -⟩ := mem_c3NarrowTableDomain_bounds h2
    obtain ⟨i, t⟩ := p
    lift i to ℕ using h0
    lift t to ℕ using (by omega)
    obtain ⟨s, hs⟩ : ∃ s : ℕ, (o : ℤ) - i = s := ⟨((o : ℤ) - i).toNat, by omega⟩
    have hso : o = i + s := by omega
    simp only [hs] at h2 ⊢
    have h := norm_sum_Ico_exp_le_c3NarrowTable hso h2 hb hβ
    simp only [S, Int.toNat_natCast, Nat.card_Ico, add_tsub_cancel_left, Int.cast_natCast]
    linarith
  have hW : (c3PacketWeight o K : ℝ) ≤ ∑ p ∈ K, (((S p).card : ℝ) - ‖∑ a ∈ S p, f a‖) := by
    simp only [c3PacketWeight, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_sub,
      Rat.cast_one]
    exact Finset.sum_le_sum hpacket
  simp only [Finset.card_range] at hmain
  have hrw : 1 - (c3PacketWeight o K : ℝ) / N = (N - c3PacketWeight o K) / N := by
    field_simp
  rw [chPacketFn_def, hrw, one_div, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (by linarith) hNpos.le

/-- **The narrow factor.** Let `c, o` be integers with `3 ≤ c ≤ 16` and `1 ≤ o`, `b` an odd
integer and `β` a real number with `|β| ≤ 10⁻⁶`. Then the capped factor satisfies
`Φ^cap_c((b + β)/2^o) ≤ 1 - δ'_{c,o}`. -/
@[collatz_pos_dens "lem_c3_narrow_factor"]
theorem trCapFactor_le_one_sub_c3NarrowDeficit {c o : ℤ} (hc₁ : 3 ≤ c) (hc₂ : c ≤ 16)
    (ho : 1 ≤ o) {b : ℤ} (hb : Odd b) {β : ℝ} (hβ : |β| ≤ 1 / 10 ^ 6) :
    trCapFactor c ((b + β) / 2 ^ o) ≤ 1 - (c3NarrowDeficit c o : ℝ) := by
  lift o to ℕ using (by omega)
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, c = N + 1 := ⟨(c - 1).toNat, by omega⟩
  have hN : 2 ≤ N := by omega
  obtain ⟨K, hK, hKw⟩ := exists_c3PacketDeficit_eq ((N : ℤ) + 1) o
  have hφ : chPacketFn N ((b + β) / 2 ^ o) ≤
      1 - (c3PacketDeficit ((N : ℤ) + 1) o : ℝ) / N := by
    rw [← hKw]
    exact chPacketFn_le_one_sub_c3PacketWeight (by omega) hK hb hβ
  rw [zpow_natCast, trCapFactor_of_mem hc₁ hc₂, show ((N : ℤ) + 1 - 1).toNat = N by omega]
  refine max_le ?_ ?_
  · refine hφ.trans ?_
    have h := c3NarrowDeficit_le_div ((N : ℤ) + 1) o
    have h' : ((c3NarrowDeficit ((N : ℤ) + 1) o : ℚ) : ℝ) ≤
        ((c3PacketDeficit ((N : ℤ) + 1) o / ((N : ℤ) + 1 - 1) : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    simp only [add_sub_cancel_right] at h'
    linarith
  · have h := c3NarrowDeficit_le_cap ((N : ℤ) + 1) o
    have h' : ((c3NarrowDeficit ((N : ℤ) + 1) o : ℚ) : ℝ) ≤ ((1 - (2 ^ 16 : ℚ)⁻¹ : ℚ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    rw [zpow_neg, zpow_ofNat]
    linarith

end CollatzPosDens
