/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrTreeCost
public import CollatzPosDens.StoppingTrace.TrWhitePolicy
public import CollatzPosDens.StoppingTrace.TrZeroCutoff

/-!
# Reflection of the gap-zero tree

The gap-zero tree cost is invariant under the reflection `X ↦ 2^{17} - X`, provided the
white-test policy is reflected along with it: for every integer `m` and all reals `a`, `b`,
`X`, the cost `trTreeCost trZeroCutoff (trWhitePolicy 0 12 14 (2 ^ 17 - m) (-b) (-a)) 0 0` at
`2 ^ 17 - X` equals `trTreeCost trZeroCutoff (trWhitePolicy 0 12 14 m a b) 0 0` at `X`.

Two facts combine. First, the two policies coincide: the cell `[-b, -a]` has midpoint
`-(a + b)/2` and length `b - a`, and for `h + c ≤ 14`,
`9^r (2^{17} - m - (a + b)/2) / 2^{h+c} = 9^r 2^{17-h-c} - 9^r (m + (a + b)/2) / 2^{h+c}`
differs from the negative of the original angle by an integer, while `dist(·, ℤ)` is invariant
under `y ↦ k - y` for `k ∈ ℤ`. Second, the packet function satisfies `Φ_t(-θ) = Φ_t(θ)`
(complex conjugation) and has period `1`, so every retained factor `ψ^{cut}_{r,h,c}` with
`h + c ≤ N` is invariant under `X ↦ 2^N - X`; a downward induction on `h` then shows the tree
cost is invariant for every policy.

## Main results

* `CollatzPosDens.chPacketFn_neg`: `Φ_t(-θ) = Φ_t(θ)`.
* `CollatzPosDens.trCapFactor_intCast_sub`: `Φ^cap_c(k - θ) = Φ^cap_c(θ)` for `k ∈ ℤ`.
* `CollatzPosDens.trTreeCost_two_pow_sub`: the tree cost is invariant under `X ↦ 2^N - X`
  whenever the cutoff satisfies `h + c ≤ N` for all retained lengths `2 ≤ c ≤ cut(h)`.
* `CollatzPosDens.trWhitePolicy_reflect`: `W^{0,C,H'}_{2^N-m,-b,-a} = W^{0,C,H'}_{m,a,b}`
  for `H' ≤ N`.
* `CollatzPosDens.trTreeCost_trZeroCutoff_reflect`: the reflection identity of the gap-zero tree.

## Implementation notes

The hypothesis `a ≤ b` is not needed and is omitted.

## References

* [Mazur, *Collatz positive density*], §9.8.
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- The packet function is even: `Φ_t(-θ) = Φ_t(θ)`. -/
theorem chPacketFn_neg (t : ℕ) (θ : ℝ) : chPacketFn t (-θ) = chPacketFn t θ := by
  simp only [chPacketFn_def]
  congr 1
  rw [← Complex.norm_conj, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

/-- The packet function is invariant under `θ ↦ k - θ` for `k ∈ ℤ`. -/
theorem chPacketFn_intCast_sub (t : ℕ) (k : ℤ) (θ : ℝ) :
    chPacketFn t (k - θ) = chPacketFn t θ := by
  rw [sub_eq_neg_add, chPacketFn_add_intCast, chPacketFn_neg]

/-- The capped packet factor is invariant under `θ ↦ k - θ` for `k ∈ ℤ`. -/
theorem trCapFactor_intCast_sub (c k : ℤ) (θ : ℝ) :
    trCapFactor c (k - θ) = trCapFactor c θ := by
  simp only [trCapFactor, chPacketFn_intCast_sub]

/-- The retained factor is invariant under `X ↦ 2^N - X` whenever `2 ≤ c ≤ cut(h)` forces
`h + c ≤ N`. -/
theorem trTreeFactor_two_pow_sub {cut : ℕ → ℕ} {N : ℕ}
    (hcut : ∀ h c : ℕ, 2 ≤ c → c ≤ cut h → h + c ≤ N) (r h : ℕ) (c : ℤ) (X : ℝ) :
    trTreeFactor cut r h c (2 ^ N - X) = trTreeFactor cut r h c X := by
  by_cases hc : 2 ≤ c ∧ c ≤ (cut h : ℤ)
  · rw [trTreeFactor_of_mem hc.1 hc.2, trTreeFactor_of_mem hc.1 hc.2]
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, c = n := ⟨c.toNat, by omega⟩
    have hn : h + n ≤ N := hcut h n (by exact_mod_cast hc.1) (by exact_mod_cast hc.2)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hn
    have h2 : (2 : ℝ) ^ ((h : ℤ) + (n : ℤ)) = 2 ^ (h + n) := by
      rw [← zpow_natCast]; push_cast; rfl
    have key : (9 : ℝ) ^ r * (2 ^ N - X) / 2 ^ ((h : ℤ) + (n : ℤ)) =
        (((9 ^ r * 2 ^ d : ℕ) : ℤ) : ℝ) - 9 ^ r * X / 2 ^ ((h : ℤ) + (n : ℤ)) := by
      rw [h2, hd, pow_add]
      push_cast
      field_simp
    rw [key, trCapFactor_intCast_sub]
  · rw [trTreeFactor_of_not_mem hc, trTreeFactor_of_not_mem hc]

open Classical in
/-- The tree cost is invariant under `X ↦ 2^N - X`, for every policy `W`, whenever every
retained length `2 ≤ c ≤ cut(h)` satisfies `h + c ≤ N`. -/
theorem trTreeCost_two_pow_sub {cut : ℕ → ℕ} {N : ℕ}
    (hcut : ∀ h c : ℕ, 2 ≤ c → c ≤ cut h → h + c ≤ N) (W : Set (ℕ × ℕ × ℕ)) (r h : ℕ)
    (X : ℝ) : trTreeCost cut W r h (2 ^ N - X) = trTreeCost cut W r h X := by
  suffices ∀ n r h, policyBound W + 1 - h = n →
      trTreeCost cut W r h (2 ^ N - X) = trTreeCost cut W r h X from this _ r h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r h hn
    rw [trTreeCost, trTreeCost]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [trTreeFactor_two_pow_sub hcut]
    congr 3
    split_ifs with hc
    · exact ih _ (by omega) _ _ rfl
    · rfl

/-- Reflecting the cell `[a, b]` to `[-b, -a]` and `m` to `2^N - m` leaves the white-test policy
`W^{0,C,H'}` unchanged, provided `H' ≤ N`. -/
theorem trWhitePolicy_reflect {N : ℕ} {C H' : ℤ} (hH : H' ≤ N) (m : ℤ) (a b : ℝ) :
    trWhitePolicy 0 C H' (2 ^ N - m) (-b) (-a) = trWhitePolicy 0 C H' m a b := by
  ext ⟨r, h, c⟩
  simp only [mem_trWhitePolicy]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  refine ⟨fun ⟨hHc, h'⟩ => ⟨hHc, ?_⟩, fun ⟨hHc, h'⟩ => ⟨hHc, ?_⟩⟩ <;>
  · have hn : h + c ≤ N := by omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hn
    set y : ℝ := (9 : ℝ) ^ r * (2 ^ 0 * m + (a + b) / 2) / 2 ^ (h + c) with hy
    have key : (9 : ℝ) ^ r * (2 ^ 0 * ((2 ^ N - m : ℤ) : ℝ) + (-b + -a) / 2) / 2 ^ (h + c) =
        (((9 ^ r * 2 ^ d : ℕ) : ℤ) : ℝ) - y := by
      rw [hy, hd, pow_add]
      push_cast
      field_simp
      ring
    have hdist : ∀ (k : ℤ) (x : ℝ), |(k - x) - round (k - x)| = |x - round x| := by
      intro k x
      refine le_antisymm ?_ ?_
      · calc |(k - x) - round (k - x)| ≤ |(k - x) - ((k - round x : ℤ) : ℝ)| := round_le _ _
          _ = |x - round x| := by rw [← abs_neg]; push_cast; ring_nf
      · calc |x - round x| ≤ |x - ((k - round (k - x) : ℤ) : ℝ)| := round_le _ _
          _ = |(k - x) - round (k - x)| := by rw [← abs_neg]; push_cast; ring_nf
    have hba : -a - -b = b - a := by ring
    simp only [key, hdist, hba] at h' ⊢
    exact h'

/-- **Reflection of the gap-zero tree.** For every integer `m` and all reals `a`, `b`, `X`, the
gap-zero tree cost with the reflected white-test policy
`trWhitePolicy 0 12 14 (2 ^ 17 - m) (-b) (-a)` at `2 ^ 17 - X` equals the gap-zero tree cost with
`trWhitePolicy 0 12 14 m a b` at `X`. -/
@[collatz_pos_dens "lem_tr_zero_reflect"]
theorem trTreeCost_trZeroCutoff_reflect (m : ℤ) (a b X : ℝ) :
    trTreeCost trZeroCutoff (trWhitePolicy 0 12 14 (2 ^ 17 - m) (-b) (-a)) 0 0 (2 ^ 17 - X) =
      trTreeCost trZeroCutoff (trWhitePolicy 0 12 14 m a b) 0 0 X := by
  have hpol := trWhitePolicy_reflect (N := 17) (C := 12) (H' := 14) (by norm_num) m a b
  rw [hpol]
  refine trTreeCost_two_pow_sub (fun h c hc hle => ?_) _ 0 0 X
  have hh : h ≤ 17 := by
    by_contra hh
    rw [trZeroCutoff_of_lt (by omega)] at hle
    omega
  have := add_trZeroCutoff_le_seventeen hh
  omega

end CollatzPosDens
