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

/-!
# Existence of a good seed

There is a good seed.

The pulled-back reference density `Ψ` on `G_{q_*}` vanishes on nonunits and has mean
`⟨Ψ⟩_{q_*} = 2/3 · P` with `P = ∑_{t ∈ 𝔗_{N_*}} 2^{-A(ŵ(t))}`. Since `q_* ≥ 1`, exactly
`2 · 3^{q_* - 1}` residues of `G_{q_*}` are units, so the average of `Ψ` over the units is `P`,
and some unit `y` has `Ψ(y) ≥ P`. As `N_* ≥ 5`, the mass of the selected tuples gives
`P > 2^{-23}`. A base-four repunit `M = (4^v - 1)/3` with `19 ≤ v < 19 + 3^{q_*}` and
`M ≡ y (mod 3^{q_*})` is then a good seed: `3M + 1 = 4^v`, `M` is odd and prime to `3`,
`16^{b_0} < M < 𝓜`, and `Z_{N_*}(M) = Ψ(y) > 2^{-23}`.

## Main results

* `CollatzPosDens.exists_goodSeed_isUnit_le`: a function on `G_q`, `q ≥ 1`, vanishing on
  nonunits with mean `2/3 · P` takes a value `≥ P` at some unit.
* `CollatzPosDens.exists_goodSeed_repunit`: every unit class modulo `3^q` contains a
  base-four repunit with the size and divisibility properties of a good seed.
* `CollatzPosDens.exists_goodSeed`: there is a good seed.

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

/-- For `a, q ≥ 1` and a unit `y ∈ G_q`, some base-four repunit `M = (4^v - 1)/3` with
`a ≤ v < a + 3^q` lies in the class `y`; it is odd, prime to `3`, and satisfies
`(4^a - 1)/3 ≤ M < 4^{a + 3^q}`. -/
theorem exists_goodSeed_repunit {a q : ℕ} (ha : 1 ≤ a) (hq : 1 ≤ q)
    {y : ResidueGroup q} (hy : IsUnit y) :
    ∃ M : ℕ, Odd M ∧ ¬ 3 ∣ M ∧ 4 ^ a ≤ 3 * M + 1 ∧ M < 4 ^ (a + 3 ^ q) ∧
      (∃ k : ℕ, 3 * M + 1 = 4 ^ k) ∧ (M : ResidueGroup q) = y := by
  obtain ⟨v, hv1, hv2, hvy⟩ := exists_four_pow_sub_one_div_three_modEq a q (y.val : ℤ)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 3 * M + 1 = 4 ^ v := by
    have hd : 3 ∣ 4 ^ v - 1 := by simpa using Nat.sub_dvd_pow_sub_pow 4 1 v
    have h1 : 1 ≤ 4 ^ v := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨M, hM⟩ := hd
    exact ⟨M, by omega⟩
  have hMZ : ((4 : ℤ) ^ v - 1) / 3 = (M : ℤ) := by
    have : (3 : ℤ) * M + 1 = 4 ^ v := by exact_mod_cast hM
    omega
  rw [hMZ] at hvy
  have hyM : ((M : ℕ) : ResidueGroup q) = y := by
    have := (ZMod.intCast_eq_intCast_iff (M : ℤ) (y.val : ℤ) (3 ^ q)).2
      (by exact_mod_cast hvy)
    rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val] at this
    exact this
  refine ⟨M, ?_, ?_, ?_, ?_, ⟨v, hM⟩, hyM⟩
  · rw [Nat.odd_iff]
    obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
    rw [pow_succ] at hM
    omega
  · intro h3
    have hunit := (isResidueUnit_iff_isUnit hq y).2 hy
    rw [IsResidueUnit, ← hyM, ZMod.val_natCast] at hunit
    exact hunit ((Nat.dvd_mod_iff (dvd_pow_self 3 (by omega))).2 h3)
  · rw [hM]
    exact Nat.pow_le_pow_right (by norm_num) hv1
  · have : 4 ^ v < 4 ^ (a + 3 ^ q) := Nat.pow_lt_pow_right (by norm_num) hv2
    omega

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

/-- There is a good seed: some `M : ℕ` satisfies `GoodSeed M`. -/
@[collatz_pos_dens "lem_good_seed_exists"]
theorem exists_goodSeed : ∃ M : ℕ, GoodSeed M := by
  have hq : 1 ≤ conductor := conductor_pos
  obtain ⟨y, hyu, hy⟩ := exists_goodSeed_isUnit_le hq
    (fun y hy => pullbackDensity_eq_zero_of_three_dvd hy) residueAvg_pullbackDensity
  obtain ⟨M, hodd, h3, hlow, hup, hpow, hyM⟩ :=
    exists_goodSeed_repunit (a := 19) (by norm_num) hq hyu
  refine ⟨M, hodd, h3, ?_, ?_, hpow, ?_⟩
  · rw [scale_zero]
    norm_num at hlow ⊢
    omega
  · rw [seedBound_def]
    exact hup
  · have hZ := weightedCentralSum_eq_pullbackDensity (M : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast, hyM] at hZ
    rw [hZ]
    exact (two_inv_pow_lt_sum_selectedTuples_real _
      (by rw [generationThreshold_eq]; norm_num)).trans_le hy

end CollatzPosDens
