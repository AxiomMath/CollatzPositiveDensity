/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FcSurvivorCount
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.FirstCrossing.BarrierMono

/-!
# Exact mass of a first-crossing subfamily

Let `H = H_{b,r_b}` and let `ℓ_b < L ≤ R ≤ h_b`. For a function `μ` of the length, consider the
words `w ∈ 𝒲(b, r_b, K)` with `L ≤ |w| ≤ R` and `A(w) ≥ H(|w|) + μ(|w|)`. Their geometric mass
is computed exactly by the surviving prefix counts `c_{b,i}(s)`:
$$\mathbf p = \sum_{d=L}^{R} \Bigl(\sum_{s \ge 0} c_{b,d-1}(s)\Bigr)
  \frac{2^{K+1-\mu(d)}-1}{2^{H(d)+K}}.$$

Indeed a word of length `d` in the family is `w = p (a)` where `p` is a surviving prefix of
length `d - 1` and some sum `t < H(d - 1) ≤ H(d)`, and the total `n = t + a` ranges over
`H(d) + μ(d) ≤ n ≤ H(d) + K`. Since `t < H(d) ≤ n`, the last letter `a = n - t` is positive for
every such `n`, so for each `n` these words are in bijection with the surviving prefixes, each of
mass `2^{-n}`; summing the geometric series in `n` gives the formula.

## Main results

* `CollatzPosDens.geomMass_firstCrossing_window_eq`: the exact mass formula.

## Implementation notes

The statement is usually given for integers `b ≥ 1`, `K ≥ 0` and `μ : {L, …, R} → ℕ` with
`μ(d) ≤ K + 1`. Here `b`, `K`, `L`, `R` are natural numbers, `μ : ℕ → ℕ` is arbitrary off
`{L, …, R}`, and the hypotheses `b ≥ 1`, `L ≤ R` and `μ(d) ≤ K + 1` are dropped: for
`μ(d) > K + 1` both the family at length `d` and the factor `2^{K+1-μ(d)} - 1 = 2^0 - 1` vanish
(truncated subtraction), and for `L > R` both sides are `0`. The mass and the right-hand side live
in `ℝ≥0∞`; the inner sum `∑_{s ≥ 0}` is a `tsum` over `ℕ` and `2^{H(d)+K}` is an integer power,
since `H(d)` is an integer.

## References

* [Mazur, *Collatz positive density*], §15.5.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The word `p (a)` whose last letter `a = n - A(p)` brings the total to `n`. -/
private def dpWord (p : Word) (n : ℤ) : Word := p ++ [Nat.toPNat' (n - p.valSum).toNat]

private theorem valSum_dpWord {p : Word} {n : ℤ} (h : (p.valSum : ℤ) < n) :
    ((dpWord p n).valSum : ℤ) = n := by
  simp only [dpWord, Word.valSum_append, Word.valSum_singleton, Nat.toPNat'_coe]
  split_ifs with h' <;> omega

/-- The index type of the decomposition: a length `d ∈ [L, R]`, a prefix sum `s`, a surviving
prefix of length `d - 1` and sum `s`, and an offset `m < K + 1 - μ(d)` of the total above
`H(d) + μ(d)`. -/
private abbrev DpIndex (b K L R : ℕ) (μ : ℕ → ℕ) : Type :=
  Σ d : Finset.Icc L R, Σ s : ℕ, (fcSurvivorSet b ((d : ℕ) - 1) s) × Fin (K + 1 - μ d)

/-- The word of the family attached to an index. -/
private noncomputable def dpMap (b K L R : ℕ) (μ : ℕ → ℕ) (x : DpIndex b K L R μ) : Word :=
  dpWord x.2.2.1 (barrier b (rb b) x.1 + μ x.1 + (x.2.2.2 : ℕ))

/-- A surviving prefix of length `d - 1 ≥ ℓ_b` has sum below `H(d)`. -/
private theorem valSum_lt_of_mem_fcSurvivorSet {b d : ℕ} {s : ℤ} {p : Word}
    (hd : lb b < d) (hp : p ∈ fcSurvivorSet b (d - 1) s) :
    (p.valSum : ℤ) < barrier b (rb b) d := by
  obtain ⟨hlen, hsum, hbar⟩ := hp
  have h1 := hbar (d - 1) (by omega) le_rfl
  rw [← hlen, List.take_length, hlen] at h1
  have h2 := barrier_le_barrier_succ b (rb b) (d - 1)
  rw [Nat.sub_add_cancel (by omega)] at h2
  exact h1.trans_le h2

private theorem valSum_dpWord_of_mem {b d : ℕ} {s : ℤ} {p : Word}
    (hd : lb b < d) (hp : p ∈ fcSurvivorSet b (d - 1) s) (k m : ℕ) :
    ((dpWord p (barrier b (rb b) d + k + m)).valSum : ℤ) = barrier b (rb b) d + k + m := by
  have := valSum_lt_of_mem_fcSurvivorSet hd hp
  exact valSum_dpWord (by omega)

private theorem dpMap_injective {b K L R : ℕ} {μ : ℕ → ℕ} (hL : lb b < L) :
    Function.Injective (dpMap b K L R μ) := by
  rintro ⟨d, s, ⟨p, hp⟩, m⟩ ⟨d', s', ⟨p', hp'⟩, m'⟩ h
  dsimp only [dpMap] at h
  have hp1 := hp.1
  have hp1' := hp'.1
  have hdL := (Finset.mem_Icc.1 d.2).1
  have hdL' := (Finset.mem_Icc.1 d'.2).1
  have hlen := congrArg List.length h
  simp only [dpWord, List.length_append, List.length_singleton] at hlen
  obtain rfl : d = d' := Subtype.ext (by omega)
  obtain rfl : p = p' := List.append_inj_left' h (by simp)
  obtain rfl : s = s' := by
    have := hp.2.1
    have := hp'.2.1
    omega
  have hv := congrArg (fun w : Word => (w.valSum : ℤ)) h
  rw [valSum_dpWord_of_mem (by omega) hp, valSum_dpWord_of_mem (by omega) hp] at hv
  obtain rfl : m = m' := Fin.ext (by omega)
  rfl

private theorem dpMap_range {b K L R : ℕ} {μ : ℕ → ℕ} (hL : lb b < L) (hR : R ≤ hb b) :
    Set.range (dpMap b K L R μ) = {w | w ∈ firstCrossing b (rb b) K ∧ L ≤ w.length ∧
      w.length ≤ R ∧ barrier b (rb b) w.length + μ w.length ≤ (w.valSum : ℤ)} := by
  ext w
  constructor
  · rintro ⟨⟨d, s, ⟨p, hp⟩, m⟩, rfl⟩
    dsimp only [dpMap]
    obtain ⟨hdL, hdR⟩ := Finset.mem_Icc.1 d.2
    have hv := valSum_dpWord_of_mem (by omega) hp (μ d) m
    obtain ⟨hlen, -, hbar⟩ := hp
    have hm := m.isLt
    have hlen' : (dpWord p (barrier b (rb b) d + μ d + (m : ℕ))).length = d := by
      simp only [dpWord, List.length_append, List.length_singleton, hlen]
      omega
    simp only [Set.mem_ofPred_eq, mem_firstCrossing, hlen', hv]
    refine ⟨⟨by omega, by omega, fun i hi1 hi2 => ?_, by omega, by omega⟩, hdL, hdR, by omega⟩
    simp only [dpWord]
    rw [List.take_append_of_le_length (by omega)]
    exact hbar i hi1 (by omega)
  · rintro ⟨hw, hLw, hRw, hμ⟩
    obtain ⟨hlb, -, hbar, hlo, hhi⟩ := hw
    obtain ⟨p, a, rfl⟩ : ∃ p a, w = p ++ [a] := by
      rcases List.eq_nil_or_concat w with rfl | ⟨p, a, h⟩
      · simp at hlb
      · exact ⟨p, a, by rw [h, List.concat_eq_append]⟩
    simp only [List.length_append, List.length_singleton, Word.valSum_append,
      Word.valSum_singleton] at *
    have hd : p.length + 1 ∈ Finset.Icc L R := Finset.mem_Icc.2 ⟨hLw, hRw⟩
    have hp : p ∈ fcSurvivorSet b ((p.length + 1) - 1) (Word.valSum p : ℤ) := by
      refine ⟨by simp, rfl, fun j hj1 hj2 => ?_⟩
      have := hbar j hj1 (by omega)
      rwa [List.take_append_of_le_length (by grind)] at this
    refine ⟨⟨⟨p.length + 1, hd⟩, Word.valSum p, ⟨p, hp⟩,
      ⟨((a : ℕ) + Word.valSum p - barrier b (rb b) (p.length + 1) -
        μ (p.length + 1)).toNat, by dsimp only; omega⟩⟩, ?_⟩
    dsimp only [dpMap]
    simp only [dpWord, List.append_cancel_left_eq, List.cons.injEq, and_true]
    apply PNat.eq
    rw [Nat.toPNat'_coe]
    have := a.pos
    split_ifs <;> omega

/-- The geometric series `∑_{m < K+1-μ} 2^{-(h+μ+m)} = (2^{K+1-μ} - 1) / 2^{h+K}`. -/
private theorem tsum_fin_inv_two_pow (h K μ : ℕ) :
    ∑' m : Fin (K + 1 - μ), (2⁻¹ : ℝ≥0∞) ^ (((h : ℤ) + μ + (m : ℕ)).toNat) =
      (2 ^ (K + 1 - μ) - 1) / 2 ^ ((h : ℤ) + K) := by
  rw [tsum_fintype,
    Fin.sum_univ_eq_sum_range (fun m => (2⁻¹ : ℝ≥0∞) ^ (((h : ℤ) + μ + m).toNat)),
    (Nat.cast_add h K).symm, zpow_natCast, div_eq_mul_inv, ENNReal.inv_pow]
  set N := K + 1 - μ with hN
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · simp [h0]
  have hsum : ∀ m ∈ Finset.range N, (2⁻¹ : ℝ≥0∞) ^ (((h : ℤ) + μ + m).toNat) =
      2 ^ (N - 1 - m) * 2⁻¹ ^ (h + K) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have he : (((h : ℤ) + μ + m).toNat) + (N - 1 - m) = h + K := by omega
    rw [← he, pow_add, mul_comm, mul_assoc, ← mul_pow,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, mul_one]
  rw [Finset.sum_congr rfl hsum, ← Finset.sum_mul,
    Finset.sum_range_reflect (fun j => (2 : ℝ≥0∞) ^ j)]
  congr 1
  have : ∑ j ∈ Finset.range N, (2 : ℝ≥0∞) ^ j =
      ((∑ j ∈ Finset.range N, 2 ^ j : ℕ) : ℝ≥0∞) := by
    push_cast
    rfl
  rw [this, Nat.geomSum_eq le_rfl, Nat.div_one, ENNReal.natCast_sub]
  norm_num

/-- A finite set of words, summed with constant weight `c`, has sum `|S| c`. -/
private theorem tsum_const_of_finite {S : Set Word} (hS : S.Finite) (c : ℝ≥0∞) :
    ∑' _ : S, c = S.ncard * c := by
  have := hS.fintype
  rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- **Exact mass of a first-crossing subfamily.** With `H = H_{b,r_b}` and `ℓ_b < L`,
`R ≤ h_b`, the words `w ∈ 𝒲(b, r_b, K)` with `L ≤ |w| ≤ R` and `A(w) ≥ H(|w|) + μ(|w|)` have
geometric mass `∑_{d=L}^{R} (∑_{s≥0} c_{b,d-1}(s)) (2^{K+1-μ(d)} - 1) / 2^{H(d)+K}`. -/
@[collatz_pos_dens "lem_fc_dp_mass"]
theorem geomMass_firstCrossing_window_eq (b K L R : ℕ) (μ : ℕ → ℕ) (hL : lb b < L)
    (hR : R ≤ hb b) :
    geomMass {w | w ∈ firstCrossing b (rb b) K ∧ L ≤ w.length ∧ w.length ≤ R ∧
        barrier b (rb b) w.length + μ w.length ≤ (w.valSum : ℤ)} =
      ∑ d ∈ Finset.Icc L R, (∑' s : ℕ, (fcSurvivorCount b (d - 1) s : ℝ≥0∞)) *
        ((2 ^ (K + 1 - μ d) - 1) / 2 ^ (barrier b (rb b) d + K)) := by
  rw [← dpMap_range hL hR, geomMass_def,
    tsum_range (fun w : Word => w.massWeight) (dpMap_injective hL), ENNReal.tsum_sigma',
    tsum_fintype]
  refine (Finset.sum_coe_sort (Finset.Icc L R) (fun d =>
    ∑' c : Σ s : ℕ, (fcSurvivorSet b (d - 1) s) × Fin (K + 1 - μ d),
      (dpWord c.2.1 (barrier b (rb b) d + μ d + (c.2.2 : ℕ))).massWeight)).trans
    (Finset.sum_congr rfl fun d hd => ?_)
  have hdL := (Finset.mem_Icc.1 hd).1
  have hw : ∀ (s : ℕ) (p : fcSurvivorSet b (d - 1) s) (m : Fin (K + 1 - μ d)),
      (dpWord p (barrier b (rb b) d + μ d + (m : ℕ))).massWeight =
        2⁻¹ ^ ((barrier b (rb b) d + μ d + (m : ℕ)).toNat) := by
    intro s p m
    have h := valSum_dpWord_of_mem (by omega) p.2 (μ d) m
    unfold Word.massWeight
    congr 1
    omega
  have hs : ∀ s : ℕ, ∑' q : (fcSurvivorSet b (d - 1) s) × Fin (K + 1 - μ d),
      (dpWord q.1 (barrier b (rb b) d + μ d + (q.2 : ℕ))).massWeight =
        fcSurvivorCount b (d - 1) s *
          ∑' m : Fin (K + 1 - μ d), 2⁻¹ ^ ((barrier b (rb b) d + μ d + (m : ℕ)).toNat) := by
    intro s
    rw [ENNReal.tsum_prod (f := fun (p : fcSurvivorSet b (d - 1) s) (m : Fin (K + 1 - μ d)) =>
      (dpWord p (barrier b (rb b) d + μ d + (m : ℕ))).massWeight)]
    simp_rw [hw]
    rw [tsum_const_of_finite (fcSurvivorSet_finite _ _ _), ← fcSurvivorCount_def]
  rw [ENNReal.tsum_sigma']
  dsimp only
  rw [tsum_congr hs, ENNReal.tsum_mul_right]
  by_cases hZ : ∑' s : ℕ, (fcSurvivorCount b (d - 1) s : ℝ≥0∞) = 0
  · rw [hZ, zero_mul, zero_mul]
  congr 1
  obtain ⟨s, hs⟩ : ∃ s : ℕ, fcSurvivorCount b (d - 1) s ≠ 0 := by
    by_contra! h
    exact hZ (ENNReal.tsum_eq_zero.2 fun s => by simp [h s])
  obtain ⟨p, hp⟩ := Set.nonempty_of_ncard_ne_zero hs
  have hpos := valSum_lt_of_mem_fcSurvivorSet (by omega) hp
  obtain ⟨h, hh⟩ : ∃ h : ℕ, barrier b (rb b) d = h := ⟨(barrier b (rb b) d).toNat, by omega⟩
  rw [hh]
  exact tsum_fin_inv_two_pow h K (μ d)

end CollatzPosDens
