/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.FieldTheory.Finite.Basic
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Qstar
public import CollatzPosDens.Recipe.NValue
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.PullbackEval
public import CollatzPosDens.Seed.PullbackMean
public import CollatzPosDens.Seed.PullbackNonunit
public import CollatzPosDens.Seed.TupleMass
public import CollatzPosDens.Seed.RepunitResidues
public import CollatzPosDens.Seed.SeedCandidate
public import CollatzPosDens.Maps.SyrPeriodicFiber
public import CollatzPosDens.Maps.Syracuse

/-!
# Existence of an `s`-good seed

For every integer `s ≥ 1` with `3 ∤ s` there is an `s`-good seed.

Put `e = e_0(s)` and `c = 2^e s`. Since `3 ∤ s`, `c ≡ 1 (mod 3)`, so the seed candidates satisfy
`3 𝖬_s(v) + 1 = 4^v c = 2^{e + 2v} s` exactly, and `𝖬_s` is strictly increasing.

The pulled-back reference density `Ψ` on `G_{q_*}` vanishes on nonunits and has mean
`⟨Ψ⟩_{q_*} = 2/3 · P` with `P = ∑_{t ∈ 𝔗_{N_*}} 2^{-A(ŵ(t))}`. Since `q_* ≥ 1`, exactly
`2 · 3^{q_* - 1}` residues of `G_{q_*}` are units, so the average of `Ψ` over the units is `P`,
and some unit `y` has `Ψ(y) ≥ P > 2^{-23}` (as `N_* ≥ 5`).

The repunit residue lemma gives `v₁ < 3^{q_*} ≤ v₂ < 2 · 3^{q_*}` with `𝖬_s(v_i) ≡ y`
(mod `3^{q_*}`). Each of the two candidates `M` is odd, prime to `3`, satisfies
`16^{b_0} s < M < 𝓜(s)` and `3M + 1 = 2^k s`, has `Z_{N_*}(M) = Ψ(y) > 2^{-23}`, and has Syracuse
image `s / 2^{v₂(s)}`. Two distinct Syracuse-periodic integers cannot share a Syracuse image, so
one of the two candidates is not Syracuse-periodic; it is an `s`-good seed.

## Main results

* `CollatzPosDens.exists_goodSeed_isUnit_le`: a function on `G_q`, `q ≥ 1`, vanishing on
  nonunits with mean `2/3 · P` takes a value `≥ P` at some unit.
* `CollatzPosDens.three_mul_seedCandidate_add_one`: `3 𝖬_s(v) + 1 = 2^{e_0(s) + 2v} s`.
* `CollatzPosDens.collatzAccel_seedCandidate`: `S(𝖬_s(v)) = s / 2^{v₂(s)}`.
* `CollatzPosDens.exists_seedCandidate_cast_eq`: every class of `G_q` contains a seed candidate
  `𝖬_s(v)` with `a ≤ v < a + 3^q`.
* `CollatzPosDens.goodSeed_seedCandidate`: a non-periodic candidate in a favourable unit class
  is an `s`-good seed.
* `CollatzPosDens.exists_goodSeed`: for `s ≥ 1` with `3 ∤ s` there is an `s`-good seed.

## Implementation notes

The averaging step produces a unit `y` with `Ψ(y) ≥ P`, and the strict bound `P > 2^{-23}` is
applied afterwards. The mass bound is an unconditional sum in `ℝ≥0∞` over the finite set
`𝔗_{N_*}`, which is converted to the finite real sum occurring in the mean of `Ψ`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Finset
open scoped ENNReal

/-- An averaging principle on `G_q`, `q ≥ 1`: if `f` vanishes on nonunits and
`⟨f⟩_q = 2/3 · P`, then some unit `y` has `P ≤ f y`, since there are exactly `2 · 3^{q-1}`
units. -/
theorem exists_goodSeed_isUnit_le {q : ℕ} (hq : 1 ≤ q)
    {f : ResidueGroup q → ℝ} (hf : ∀ y : ResidueGroup q, 3 ∣ y.val → f y = 0) {P : ℝ}
    (hmean : residueAvg q f = 2 / 3 * P) : ∃ y : ResidueGroup q, IsUnit y ∧ P ≤ f y := by
  by_contra hcon
  push Not at hcon
  have hsum : ∑ y, f y = ∑ y ∈ univ.filter IsUnit, f y := by
    rw [sum_filter]
    refine sum_congr rfl fun y _ => ?_
    split_ifs with h
    · rfl
    · refine hf y ?_
      have := (isResidueUnit_iff_isUnit hq y).not.2 h
      rwa [IsResidueUnit, not_not] at this
  have hcard : ((univ.filter (IsUnit : ResidueGroup q → Prop)).card : ℝ) =
      2 * 3 ^ (q - 1) := by
    have h1 : (univ.filter (IsUnit : ResidueGroup q → Prop)).card =
        Fintype.card (ResidueGroup q)ˣ := by
      rw [← Fintype.card_subtype]
      exact Fintype.card_congr Submonoid.unitsTypeEquivIsUnitSubmonoid.toEquiv.symm
    rw [h1, ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_three (by omega)]
    push_cast
    ring
  have hlt : ∑ y ∈ univ.filter IsUnit, f y <
      ∑ _y ∈ univ.filter (IsUnit : ResidueGroup q → Prop), P :=
    sum_lt_sum_of_nonempty ⟨1, by simp⟩ fun y hy => hcon y (mem_filter.1 hy).2
  rw [sum_const, nsmul_eq_mul, hcard, ← hsum] at hlt
  rw [residueAvg_def] at hmean
  have h3 : (3 : ℝ) ^ q = 3 * 3 ^ (q - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : (0 : ℝ) < 3 ^ q := by positivity
  have : ∑ y, f y = 3 ^ q * (2 / 3 * P) := by
    rw [← hmean, mul_inv_cancel_left₀ hpos.ne']
  rw [this, h3] at hlt
  linarith

/-- The seed exponent is `38` or `39`. -/
theorem seedExponent_mem (s : ℕ) : 38 ≤ seedExponent s ∧ seedExponent s ≤ 39 := by
  unfold seedExponent
  split_ifs <;> norm_num

/-- For `3 ∤ s`, `2^{e_0(s) + 2v} s ≡ 1 (mod 3)`. -/
theorem two_pow_seedExponent_add_mul_mod_three {s : ℕ} (hs3 : ¬ 3 ∣ s) (v : ℕ) :
    2 ^ (seedExponent s + 2 * v) * s % 3 = 1 := by
  have h4 : (2 ^ 2) ^ v % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have he : 2 ^ seedExponent s * s % 3 = 1 := by
    unfold seedExponent
    split_ifs with h
    · rw [Nat.mul_mod, h]; norm_num
    · have : s % 3 = 2 := by omega
      rw [Nat.mul_mod, this]; norm_num
  rw [pow_add, pow_mul, mul_comm (2 ^ seedExponent s), mul_assoc, Nat.mul_mod, h4, he]

/-- The seed candidates are exact: `3 𝖬_s(v) + 1 = 2^{e_0(s) + 2v} s` for `s ≥ 1`, `3 ∤ s`. -/
theorem three_mul_seedCandidate_add_one {s : ℕ} (hs : 0 < s) (hs3 : ¬ 3 ∣ s) (v : ℕ) :
    3 * seedCandidate s v + 1 = 2 ^ (seedExponent s + 2 * v) * s := by
  have hmod := two_pow_seedExponent_add_mul_mod_three hs3 v
  have hpos : 0 < 2 ^ (seedExponent s + 2 * v) * s := Nat.mul_pos (by positivity) hs
  unfold seedCandidate
  omega

/-- The seed candidates are strictly increasing in `v`. -/
theorem seedCandidate_strictMono {s : ℕ} (hs : 0 < s) (hs3 : ¬ 3 ∣ s) :
    StrictMono (seedCandidate s) := by
  intro v w hvw
  have h1 := three_mul_seedCandidate_add_one hs hs3 v
  have h2 := three_mul_seedCandidate_add_one hs hs3 w
  have : 2 ^ (seedExponent s + 2 * v) * s < 2 ^ (seedExponent s + 2 * w) * s :=
    Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by norm_num) (by omega)) hs
  omega

/-- The Syracuse image of a seed candidate is the odd part of `s`:
`S(𝖬_s(v)) = s / 2^{v₂(s)}`. -/
theorem collatzAccel_seedCandidate {s : ℕ} (hs : 0 < s) (hs3 : ¬ 3 ∣ s) (v : ℕ) :
    collatzAccel (seedCandidate s v) = s / 2 ^ padicValNat 2 s := by
  rw [collatzAccel_def, three_mul_seedCandidate_add_one hs hs3,
    padicValNat.mul (by positivity) hs.ne', padicValNat.prime_pow,
    pow_add 2 (seedExponent s + 2 * v), Nat.mul_div_mul_left _ _ (by positivity)]

/-- For `s ≥ 1` with `3 ∤ s`, every class `y ∈ G_q` contains a seed candidate `𝖬_s(v)` with
`a ≤ v < a + 3^q`. -/
theorem exists_seedCandidate_cast_eq {s : ℕ} (hs : 0 < s) (hs3 : ¬ 3 ∣ s) (a q : ℕ)
    (y : ResidueGroup q) :
    ∃ v : ℕ, a ≤ v ∧ v < a + 3 ^ q ∧ (seedCandidate s v : ResidueGroup q) = y := by
  have hc : ((2 ^ seedExponent s * s : ℕ) : ℤ) ≡ 1 [ZMOD 3] := by
    have := two_pow_seedExponent_add_mul_mod_three hs3 0
    rw [mul_zero, add_zero] at this
    generalize 2 ^ seedExponent s * s = X at this ⊢
    unfold Int.ModEq
    omega
  obtain ⟨v, hv1, hv2, hvy⟩ := exists_four_pow_sub_one_div_three_modEq hc a q (y.val : ℤ)
  have hM : (4 : ℤ) ^ v * ((2 ^ seedExponent s * s : ℕ) : ℤ) =
      3 * (seedCandidate s v : ℤ) + 1 := by
    have : 3 * seedCandidate s v + 1 = 4 ^ v * (2 ^ seedExponent s * s) := by
      rw [three_mul_seedCandidate_add_one hs hs3, pow_add, pow_mul]
      ring
    exact_mod_cast this.symm
  rw [hM, pow_succ'] at hvy
  have hvy' : (seedCandidate s v : ℤ) ≡ (y.val : ℤ) [ZMOD 3 ^ q] :=
    Int.ModEq.mul_left_cancel' (c := 3) (by norm_num) (Int.ModEq.add_right_cancel' 1 (by
      rw [add_comm 1 (3 * (y.val : ℤ))] at hvy; exact hvy))
  refine ⟨v, hv1, hv2, ?_⟩
  have := (ZMod.intCast_eq_intCast_iff (seedCandidate s v : ℤ) (y.val : ℤ) (3 ^ q)).2
    (by exact_mod_cast hvy')
  rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val] at this
  exact this

/-- The mass bound of the selected tuples, as a finite real sum:
`2^{-23} < ∑_{t ∈ 𝔗_n} 2^{-A(ŵ(t))}` for `n ≥ 5`. -/
private theorem two_inv_pow_lt_sum_selectedTuples_real (n : ℕ) (hn : 5 ≤ n) :
    (2 : ℝ)⁻¹ ^ 23 < ∑ t ∈ (selectedTuples_finite n).toFinset,
      (2 : ℝ) ^ (-((concatWord t).valSum : ℤ)) := by
  have h := two_inv_pow_lt_tsum_selectedTuples n hn
  set s := (selectedTuples_finite n).toFinset
  have hs : selectedTuples n = (s : Set (Fin n → Word)) :=
    (Set.Finite.coe_toFinset _).symm
  have heq : ∑' t : selectedTuples n, (2⁻¹ : ℝ≥0∞) ^ (concatWord (t : Fin n → Word)).valSum =
      ∑ t ∈ s, (2⁻¹ : ℝ≥0∞) ^ (concatWord t).valSum := by
    rw [← Finset.tsum_subtype s (fun t => (2⁻¹ : ℝ≥0∞) ^ (concatWord t).valSum)]
    rw [hs]
    rfl
  rw [heq] at h
  have hne : ∑ t ∈ s, (2⁻¹ : ℝ≥0∞) ^ (concatWord t).valSum ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun _ _ => ENNReal.pow_ne_top (by simp)
  have := (ENNReal.toReal_lt_toReal (by simp) hne).2 h
  rw [ENNReal.toReal_sum fun _ _ => ENNReal.pow_ne_top (by simp)] at this
  simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at this
  convert this using 2 with t
  rw [zpow_neg, zpow_natCast, inv_pow]

/-- A seed candidate `𝖬_s(v)` with `v < 2 · 3^{q_*}` in a unit class `y` of `G_{q_*}` with
`Ψ(y) > 2^{-23}` which is not Syracuse-periodic is an `s`-good seed. -/
theorem goodSeed_seedCandidate {s v : ℕ} (hs : 0 < s) (hs3 : ¬ 3 ∣ s)
    (hv : v < 2 * 3 ^ conductor) {y : ResidueGroup conductor} (hyu : IsUnit y)
    (hy : (2 : ℝ)⁻¹ ^ 23 < pullbackDensity y)
    (hyM : (seedCandidate s v : ResidueGroup conductor) = y)
    (hper : ¬ SyrPeriodic (seedCandidate s v)) : GoodSeed s (seedCandidate s v) := by
  set M := seedCandidate s v with hMdef
  have hk := three_mul_seedCandidate_add_one hs hs3 v
  rw [← hMdef] at hk
  obtain ⟨he1, he2⟩ := seedExponent_mem s
  set k := seedExponent s + 2 * v with hkdef
  have hq : 1 ≤ conductor := conductor_pos
  refine ⟨?_, ?_, ?_, ?_, ⟨k, hk⟩, hper, ?_⟩
  · rw [Nat.odd_iff]
    obtain ⟨u, hu⟩ : ∃ u, k = u + 1 := ⟨k - 1, by omega⟩
    rw [hu, pow_succ', mul_assoc] at hk
    omega
  · intro h3
    have hunit := (isResidueUnit_iff_isUnit hq y).2 hyu
    rw [IsResidueUnit, ← hyM, ZMod.val_natCast] at hunit
    exact hunit ((Nat.dvd_mod_iff (dvd_pow_self 3 (by omega))).2 h3)
  · rw [scale_zero]
    have h36 : 2 ^ 38 * s ≤ 2 ^ k * s :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h16 : (16 : ℕ) ^ 9 = 2 ^ 36 := by norm_num
    rw [h16]
    have h1 : 1 ≤ s := hs
    have : 2 ^ 38 * s = 4 * (2 ^ 36 * s) := by ring
    have : 2 ^ 36 ≤ 2 ^ 36 * s := Nat.le_mul_of_pos_right _ hs
    omega
  · rw [seedBound_eq_two_pow]
    have h1 : 2 ^ k * s ≤ 2 ^ (37 + 4 * 3 ^ conductor) * s :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have : s * 2 ^ (38 + 4 * 3 ^ conductor) = 2 * (2 ^ (37 + 4 * 3 ^ conductor) * s) := by
      ring
    omega
  · have hZ := weightedCentralSum_eq_pullbackDensity (M : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast, hyM] at hZ
    rw [hZ]
    exact hy

/-- **Existence of an `s`-good seed**. For every integer `s ≥ 1` with
`3 ∤ s` there is an `s`-good seed. -/
@[collatz_pos_dens "lem_good_seed_exists"]
theorem exists_goodSeed : ∀ s : ℕ, 0 < s → ¬ 3 ∣ s → ∃ M : ℕ, GoodSeed s M := by
  intro s hs hs3
  have hq : 1 ≤ conductor := conductor_pos
  obtain ⟨y, hyu, hy⟩ := exists_goodSeed_isUnit_le hq
    (fun y hy => pullbackDensity_eq_zero_of_three_dvd hy) residueAvg_pullbackDensity
  have hy' : (2 : ℝ)⁻¹ ^ 23 < pullbackDensity y :=
    (two_inv_pow_lt_sum_selectedTuples_real _
      (by rw [generationThreshold_eq]; norm_num)).trans_le hy
  obtain ⟨v₁, -, hv₁, hy₁⟩ := exists_seedCandidate_cast_eq hs hs3 0 conductor y
  obtain ⟨v₂, hv₂, hv₂', hy₂⟩ := exists_seedCandidate_cast_eq hs hs3 (3 ^ conductor) conductor y
  by_cases h₁ : SyrPeriodic (seedCandidate s v₁)
  · by_cases h₂ : SyrPeriodic (seedCandidate s v₂)
    · have heq := h₁.eq_of_collatzAccel_eq h₂ (by
        rw [collatzAccel_seedCandidate hs hs3, collatzAccel_seedCandidate hs hs3])
      exact absurd heq (seedCandidate_strictMono hs hs3 (by omega : v₁ < v₂)).ne
    · exact ⟨_, goodSeed_seedCandidate hs hs3 (by omega) hyu hy' hy₂ h₂⟩
  · exact ⟨_, goodSeed_seedCandidate hs hs3 (by omega) hyu hy' hy₁ h₁⟩

end CollatzPosDens
