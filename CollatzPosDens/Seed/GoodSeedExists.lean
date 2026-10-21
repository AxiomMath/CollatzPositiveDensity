/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.PhQstarFloor
public import CollatzPosDens.Recipe.Qstar
public import CollatzPosDens.Recipe.SeedMargin
public import CollatzPosDens.Recipe.SeedShift
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.PullbackEval
public import CollatzPosDens.Seed.RepunitResidues
public import CollatzPosDens.Seed.S05GoodResidue
public import CollatzPosDens.Seed.SeedCandidate
public import CollatzPosDens.Maps.SyrPeriodicFiber
public import CollatzPosDens.Maps.Syracuse

/-!
# Existence of a `t`-good seed

For every integer `t ≥ 1` with `3 ∤ t` there is a `t`-good seed.

Put `e = e_0(t)` and `c = 2^e t`. Since `3 ∤ t`, `c ≡ 1 (mod 3)`, so the seed candidates satisfy
`3 𝖼_t(v) + 1 = 4^v c = 2^{e + 2v} t` exactly, and `𝖼_t` is strictly increasing.

There is a residue `y ∈ G_{q_*}` at which the pulled-back reference density satisfies
`Ψ(y) > 13/15`. The repunit residue lemma gives `v₁ < 3^{q_*} ≤ v₂ < 2 · 3^{q_*}` with
`𝖼_t(v_i) ≡ y (mod 3^{q_*})`. Each of the two candidates `t₁` is odd, satisfies
`3t₁ + 1 = 2^a t` with `σ_sd + 2 ≤ a ≤ σ_sd + 1 + 4 · 3^{q_*}`, hence `2^{σ_sd} t < t₁`, and,
as `σ_sd + 1 = 66177 ≤ 3^{11} ≤ 3^{q_*}`, `t₁ < 2^{5 · 3^{q_*}} t = 𝓜(t)`; it
has `Z_{N_*}(t₁) = Ψ(y) > 13/15 > θ_tl + ε_Z`, and has Syracuse image `t / 2^{v₂(t)}`. Two
distinct Syracuse-periodic integers cannot share a Syracuse image, so one of the two candidates is
not Syracuse-periodic; it is a `t`-good seed.

## Main results

* `CollatzPosDens.three_mul_seedCandidate_add_one`: `3 𝖼_t(v) + 1 = 2^{e_0(t) + 2v} t`.
* `CollatzPosDens.seedCandidate_strictMono`: `𝖼_t` is strictly increasing.
* `CollatzPosDens.collatzAccel_seedCandidate`: `S(𝖼_t(v)) = t / 2^{v₂(t)}`.
* `CollatzPosDens.exists_seedCandidate_cast_eq`: every class of `G_q` contains a seed candidate
  `𝖼_t(v)` with `a ≤ v < a + 3^q`.
* `CollatzPosDens.seedShift_add_one_le_three_pow_conductor`: `σ_sd + 1 ≤ 3^{q_*}`.
* `CollatzPosDens.goodSeed_seedCandidate`: a non-periodic candidate `𝖼_t(v)`, `v < 2 · 3^{q_*}`,
  in a class `y` with `Ψ(y) > θ_tl + ε_Z` is a `t`-good seed.
* `CollatzPosDens.exists_goodSeed`: for `t ≥ 1` with `3 ∤ t` there is a `t`-good seed.

## Implementation notes

The arithmetic bounds on the exponent are proved for an arbitrary shift `σ` and an arbitrary `Q`
in place of `σ_sd` and `3^{q_*}`, since `3^{q_*}` may not be evaluated. The properties of `σ_sd`
used are `σ_sd ≥ 1` and `σ_sd + 1 ≤ 3^{q_*}`; the latter is reached through `3^{11}` and the
floor `q_* ≥ 352`, so `3^{q_*}` is never evaluated.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The seed shift is positive. -/
private theorem seedShift_pos : 0 < seedShift := by
  rw [seedShift_eq]
  norm_num

/-- For `3 ∤ s`, `2^{e_0(s) + 2v} s ≡ 1 (mod 3)`. -/
theorem two_pow_seedExponent_add_mul_mod_three {s : ℕ} (hs3 : ¬ 3 ∣ s) (v : ℕ) :
    2 ^ (seedExponent s + 2 * v) * s % 3 = 1 := by
  have h4 : (2 ^ 2) ^ v % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have he := two_pow_seedExponent_mul_mod_three hs3
  rw [pow_add, pow_mul, mul_comm (2 ^ seedExponent s), mul_assoc, Nat.mul_mod, h4, he]

/-- The seed candidates are exact: `3 𝖼_s(v) + 1 = 2^{e_0(s) + 2v} s` for `s ≥ 1`, `3 ∤ s`. -/
theorem three_mul_seedCandidate_add_one {s : ℕ} (hs : 0 < s) (hs3 : ¬ 3 ∣ s) (v : ℕ) :
    3 * seedCandidate s v + 1 = 2 ^ (seedExponent s + 2 * v) * s := by
  have hmod := two_pow_seedExponent_add_mul_mod_three hs3 v
  have hpos : 0 < 2 ^ (seedExponent s + 2 * v) * s := Nat.mul_pos (by positivity) hs
  unfold seedCandidate
  generalize 2 ^ (seedExponent s + 2 * v) * s = X at hmod hpos ⊢
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
`S(𝖼_s(v)) = s / 2^{v₂(s)}`. -/
theorem collatzAccel_seedCandidate {s : ℕ} (hs : 0 < s) (hs3 : ¬ 3 ∣ s) (v : ℕ) :
    collatzAccel (seedCandidate s v) = s / 2 ^ padicValNat 2 s := by
  rw [collatzAccel_def, three_mul_seedCandidate_add_one hs hs3,
    padicValNat.mul (by positivity) hs.ne', padicValNat.prime_pow,
    pow_add 2 (seedExponent s + 2 * v), Nat.mul_div_mul_left _ _ (by positivity)]

/-- For `s ≥ 1` with `3 ∤ s`, every class `y ∈ G_q` contains a seed candidate `𝖼_s(v)` with
`a ≤ v < a + 3^q`. -/
theorem exists_seedCandidate_cast_eq {s : ℕ} (hs : 0 < s) (hs3 : ¬ 3 ∣ s) (a q : ℕ)
    (y : ResidueGroup q) :
    ∃ v : ℕ, a ≤ v ∧ v < a + 3 ^ q ∧ (seedCandidate s v : ResidueGroup q) = y := by
  have hc : ((2 ^ seedExponent s * s : ℕ) : ℤ) ≡ 1 [ZMOD 3] := by
    have := two_pow_seedExponent_mul_mod_three hs3
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

/-- If `3M + 1 = 2^k s` with `k ≤ σ + 1 + 4Q` and `σ + 1 ≤ Q`, then `M < 2^{5Q} s`. -/
theorem lt_two_pow_mul_of_three_mul_add_one_eq {M k s σ Q : ℕ} (hk : k ≤ σ + 1 + 4 * Q)
    (hσQ : σ + 1 ≤ Q) (h : 3 * M + 1 = 2 ^ k * s) : M < 2 ^ (5 * Q) * s := by
  have h1 : 2 ^ k * s ≤ 2 ^ (5 * Q) * s :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega

/-- `σ_sd + 1 ≤ 3^q` for `q ≥ 11`, since `σ_sd + 1 = 66177 ≤ 3^{11}`. -/
theorem seedShift_add_one_le_three_pow {q : ℕ} (hq : 11 ≤ q) : seedShift + 1 ≤ 3 ^ q := by
  have h := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hq
  rw [seedShift_eq]
  norm_num at h
  omega

/-- The seed shift is small against the conductor power: `σ_sd + 1 ≤ 3^{q_*}`, since
`11 ≤ 352 ≤ q_*`. -/
theorem seedShift_add_one_le_three_pow_conductor : seedShift + 1 ≤ 3 ^ conductor :=
  seedShift_add_one_le_three_pow (le_trans (by norm_num) three_hundred_fifty_two_le_conductor)

/-- If `3M + 1 = 2^k s` with `σ + 2 ≤ k`, `σ ≥ 1` and `s ≥ 1`, then `2^σ s < M`. -/
theorem two_pow_mul_lt_of_three_mul_add_one_eq {M k s σ : ℕ} (hσ : 0 < σ) (hs : 0 < s)
    (hk : σ + 2 ≤ k) (h : 3 * M + 1 = 2 ^ k * s) : 2 ^ σ * s < M := by
  have h1 : 2 ^ (σ + 2) * s ≤ 2 ^ k * s :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hk)
  rw [pow_add, mul_right_comm] at h1
  have h2 : 2 ≤ 2 ^ σ * s :=
    (Nat.le_self_pow hσ.ne' 2).trans (Nat.le_mul_of_pos_right _ hs)
  generalize 2 ^ σ * s = X at h1 h2 ⊢
  omega

/-- A seed candidate `𝖼_s(v)` with `v < 2 · 3^{q_*}` in a class `y` of `G_{q_*}` with
`Ψ(y) > θ_tl + ε_Z` which is not Syracuse-periodic is an `s`-good seed. -/
theorem goodSeed_seedCandidate {s v : ℕ} (hs : 0 < s) (hs3 : ¬ 3 ∣ s)
    (hv : v < 2 * 3 ^ conductor) {y : ResidueGroup conductor}
    (hy : (tailMargin : ℝ) + (centralSumMargin : ℝ) < pullbackDensity y)
    (hyM : (seedCandidate s v : ResidueGroup conductor) = y)
    (hper : ¬ SyrPeriodic (seedCandidate s v)) : GoodSeed s (seedCandidate s v) := by
  set M := seedCandidate s v with hMdef
  have hk := three_mul_seedCandidate_add_one hs hs3 v
  rw [← hMdef] at hk
  obtain ⟨he1, he2⟩ := seedExponent_bounds s
  set k := seedExponent s + 2 * v with hkdef
  have hσ := seedShift_pos
  have hkup : k ≤ seedShift + 1 + 4 * 3 ^ conductor := by
    generalize 3 ^ conductor = Q at hv ⊢
    generalize seedShift = σ at he1 he2 ⊢
    omega
  refine ⟨⟨k, ?_, hk⟩, ?_, hper, ?_, ?_, ?_⟩
  · generalize 3 ^ conductor = Q at hkup ⊢
    omega
  · rw [Nat.odd_iff]
    obtain ⟨u, hu⟩ : ∃ u, k = u + 1 := ⟨k - 1, by omega⟩
    rw [hu, pow_succ', mul_assoc] at hk
    omega
  · exact two_pow_mul_lt_of_three_mul_add_one_eq hσ hs (by omega) hk
  · rw [seedBound_def]
    exact lt_two_pow_mul_of_three_mul_add_one_eq hkup
      seedShift_add_one_le_three_pow_conductor hk
  · have hZ := weightedCentralSum_eq_pullbackDensity (M : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast, hyM] at hZ
    rw [hZ]
    exact hy

/-- **Existence of a `t`-good seed**. For every integer `t ≥ 1` with `3 ∤ t` there is a
`t`-good seed. -/
@[collatz_pos_dens "lem_good_seed_exists"]
theorem exists_goodSeed : ∀ t : ℕ, 0 < t → ¬ 3 ∣ t → ∃ M : ℕ, GoodSeed t M := by
  intro s hs hs3
  obtain ⟨y, hy⟩ := exists_lt_pullbackDensity
  have hmargin : ((tailMargin + centralSumMargin : ℚ) : ℝ) < ((13 / 15 : ℚ) : ℝ) :=
    Rat.cast_lt.2 tailMargin_add_centralSumMargin_lt
  rw [Rat.cast_add] at hmargin
  have hy' : (tailMargin : ℝ) + (centralSumMargin : ℝ) < pullbackDensity y :=
    hmargin.trans (by convert hy using 1; push_cast; ring)
  obtain ⟨v₁, -, hv₁, hy₁⟩ := exists_seedCandidate_cast_eq hs hs3 0 conductor y
  obtain ⟨v₂, hv₂, hv₂', hy₂⟩ := exists_seedCandidate_cast_eq hs hs3 (3 ^ conductor) conductor y
  have hv : v₁ < v₂ ∧ v₁ < 2 * 3 ^ conductor ∧ v₂ < 2 * 3 ^ conductor := by
    generalize 3 ^ conductor = Q at hv₁ hv₂ hv₂' ⊢
    omega
  by_cases h₁ : SyrPeriodic (seedCandidate s v₁)
  · by_cases h₂ : SyrPeriodic (seedCandidate s v₂)
    · have heq := h₁.eq_of_collatzAccel_eq h₂ (by
        rw [collatzAccel_seedCandidate hs hs3, collatzAccel_seedCandidate hs hs3])
      exact absurd heq (seedCandidate_strictMono hs hs3 hv.1).ne
    · exact ⟨_, goodSeed_seedCandidate hs hs3 hv.2.2 hy' hy₂ h₂⟩
  · exact ⟨_, goodSeed_seedCandidate hs hs3 hv.2.1 hy' hy₁ h₁⟩

end CollatzPosDens
