/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Recipe.CovExp
public import CollatzPosDens.Recipe.CovGen
public import CollatzPosDens.Recipe.TargetExp
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.CountExp
public import CollatzPosDens.Recipe.SeedShift
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Recipe.TowerConstant
public import CollatzPosDens.Recipe.PhTowerConstantExp
public import CollatzPosDens.Recipe.PhQstarFloor
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.GoodSeedExists
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Terminal.ULower
public import CollatzPosDens.Terminal.Charge
public import CollatzPosDens.Terminal.Coverage
public import CollatzPosDens.Terminal.SourceWindow
public import CollatzPosDens.OrdinaryTime.SourceOdd
public import CollatzPosDens.OrdinaryTime.Time
public import CollatzPosDens.OrdinaryTime.CkAccelTime

/-!
# Joint count with the tower constant

Let `D_A = tow₃(E_tow)` be the tower constant (`towerConstant`) and `κ_t = 25/11` the target
exponent (`targetExp`). Fix an integer `t ≥ 1` with `3 ∤ t`. For every real `X ≥ D_A t`, at
least `X / (t ^ κ_t D_A)` odd integers `1 ≤ n < X` reach `t` within `⌊(523/50) log(n/t)⌋₊`
Collatz steps and reach the odd part `t / 2^{v₂(t)}` within `⌊(34881/10000) log(n/t)⌋₊`
accelerated Collatz steps.

The proof fixes a `t`-good seed `t₁ < 𝓜(t) = 2^{5·3^{q_*}} t`, puts `Z = X / 32`, which is at
least `2^{Λ_cov} t₁` (with `Λ_cov = covExp = 2^352`) because `D_A = 2^T` with
`5 + Λ_cov + 5·3^{q_*} < 16·3^{q_*} < T`, chooses a generation `j ≥ J_c` (`covGen`) for which
`Z` is admissible, and counts the source set `𝒮_{j,Z}(t₁)`: the unweighted terminal mass bound
and the source charge give `#𝒮_{j,Z}(t₁) ≥ 2^{-212} t₁^{-κ_t} X ≥ X / (t ^ κ_t D_A)`, the source
window places `𝒮_{j,Z}(t₁)` in `[X/32, X)`, every source is odd, and the two time lemmas give
both clocks on every source.

## Main results

* `CollatzPosDens.div_rpow_mul_towerConstant_le_ncard_reach`: the joint count
  `X / (t ^ κ_t D_A) ≤ #{…}` for `X ≥ D_A t`.

## Implementation notes

The counted set is a subset of `ℕ` and its size is `Set.ncard`; the set is finite, being
contained in `{n | n < X}`, so this is its genuine number of elements. The source set lives in
`ℤ` and is transported to `ℕ` along `Int.toNat`, which is injective on positive integers. The
quotient `n / t` inside the logarithm is real division, and `t / 2^{v₂(t)}` is division in `ℕ`,
which is exact. The hypothesis `t ≥ 1` is omitted: it follows from `3 ∤ t`.

The final comparison `2^{212} 𝓜(t)^{κ_t} ≤ D_A t^{κ_t}` uses `κ_t ≤ 3`, so that
`(2^{5·3^{q_*}})^{κ_t} ≤ 2^{15·3^{q_*}}` and `212 + 15·3^{q_*} < 16·3^{q_*}`; this replaces the
real exponent `212 + (125/11)·3^{q_*}` by a natural one. The tower constant and `3 ^ q_*` are
never evaluated: the exponent comparisons are proved for variables `q`, `Λ`, `E` and then
instantiated at `q_*`, `Λ_cov` and `E_tow`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The exponent comparisons behind the tower constant, for variables `q`, `L`, `E` with `5 ≤ q`,
`L ≤ 3^q` and `16·3^q < 2^2^E`: `2^5 · 2^L · 2^{5·3^q} ≤ tow₃(E)` and
`2^{212} · (2^{5·3^q})^3 ≤ tow₃(E)`. -/
private theorem mnInternal_two_pow_le_tower {q L E : ℕ} (hq : 5 ≤ q) (hL : L ≤ 3 ^ q)
    (hT : 16 * 3 ^ q < 2 ^ 2 ^ E) :
    2 ^ 5 * 2 ^ L * 2 ^ (5 * 3 ^ q) ≤ tower 3 E ∧
      2 ^ 212 * (2 ^ (5 * 3 ^ q)) ^ 3 ≤ tower 3 E := by
  have h5 : 3 ^ 5 ≤ 3 ^ q := Nat.pow_le_pow_right (by norm_num) hq
  rw [tower_three, ← pow_add, ← pow_add, ← pow_mul, ← pow_add]
  generalize 3 ^ q = x at h5 hL hT ⊢
  generalize 2 ^ 2 ^ E = T at hT ⊢
  norm_num at h5
  exact ⟨Nat.pow_le_pow_right (by norm_num) (by omega),
    Nat.pow_le_pow_right (by norm_num) (by omega)⟩

/-- `2^n ≤ 3^q` for variables `n ≤ q`. -/
private theorem mnInternal_two_pow_le_three_pow {n q : ℕ} (hq : n ≤ q) : 2 ^ n ≤ 3 ^ q :=
  (Nat.pow_le_pow_right Nat.two_pos hq).trans (Nat.pow_le_pow_left (by decide) q)

/-- The real form of `mnInternal_two_pow_le_tower`, with the factor `P = 2^{5·3^q}`:
`1 ≤ P`, `32 · 2^L · P ≤ tow₃(E)` and `2^{212} · P^3 ≤ tow₃(E)`. -/
private theorem mnInternal_tower_bounds {q L E : ℕ} (hq : 5 ≤ q) (hL : L ≤ 3 ^ q)
    (hT : 16 * 3 ^ q < 2 ^ 2 ^ E) :
    1 ≤ 2 ^ (5 * 3 ^ q) ∧ (32 : ℝ) * 2 ^ L * ((2 ^ (5 * 3 ^ q) : ℕ) : ℝ) ≤ (tower 3 E : ℝ) ∧
      (2 : ℝ) ^ 212 * ((2 ^ (5 * 3 ^ q) : ℕ) : ℝ) ^ 3 ≤ (tower 3 E : ℝ) := by
  obtain ⟨h1, h2⟩ := mnInternal_two_pow_le_tower hq hL hT
  refine ⟨Nat.one_le_two_pow, ?_, ?_⟩
  · have h1' : ((2 ^ 5 * 2 ^ L * 2 ^ (5 * 3 ^ q) : ℕ) : ℝ) ≤ (tower 3 E : ℝ) := by
      exact_mod_cast h1
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow] at h1'
    norm_num at h1' ⊢
    exact h1'
  · have h2' : ((2 ^ 212 * (2 ^ (5 * 3 ^ q)) ^ 3 : ℕ) : ℝ) ≤ (tower 3 E : ℝ) := by
      exact_mod_cast h2
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow] at h2'
    exact_mod_cast h2'

/-- The seed factor of the joint count: `𝓜(t) = P t` for a natural number `P ≥ 1` with
`32 · 2^{Λ_cov} · P ≤ D_A` and `2^{212} · P^3 ≤ D_A` (namely `P = 2^{5·3^{q_*}}`). -/
private theorem mnInternal_exists_seedFactor (t : ℕ) :
    ∃ P : ℕ, 1 ≤ P ∧ (32 : ℝ) * 2 ^ covExp * P ≤ towerConstant ∧
      (2 : ℝ) ^ 212 * (P : ℝ) ^ 3 ≤ towerConstant ∧ seedBound t = P * t := by
  have hq : 352 ≤ conductor := three_hundred_fifty_two_le_conductor
  have hL : covExp ≤ 3 ^ conductor := covExp_def ▸ mnInternal_two_pow_le_three_pow hq
  obtain ⟨h1, h2, h3⟩ := mnInternal_tower_bounds (le_trans (by norm_num) hq) hL
    sixteen_mul_three_pow_conductor_lt_two_pow_two_pow_towerExp
  rw [towerConstant_eq_tower]
  exact ⟨_, h1, h2, h3, seedBound_def t⟩

/-- For every integer `t` with `3 ∤ t` (hence `t ≥ 1`) and every real `X ≥ D_A t`, at least
`X / (t ^ κ_t D_A)` odd integers `1 ≤ n < X` reach `t` within `⌊(523/50) log(n/t)⌋₊` Collatz
steps and reach `t / 2^{v₂(t)}` within `⌊(34881/10000) log(n/t)⌋₊` accelerated Collatz steps;
here `D_A = towerConstant`, `κ_t = targetExp` and `t ^ κ_t` is a real power. -/
@[collatz_pos_dens "prop_mn_internal"]
theorem div_rpow_mul_towerConstant_le_ncard_reach {t : ℕ} (ht3 : ¬ 3 ∣ t)
    {X : ℝ} (hX : (towerConstant : ℝ) * t ≤ X) :
    X / ((t : ℝ) ^ (targetExp : ℝ) * towerConstant) ≤
      ({n : ℕ | 1 ≤ n ∧ (n : ℝ) < X ∧
        (Odd n ∧ ReachWithin collatz t n ⌊(523 / 50 : ℝ) * Real.log ((n : ℝ) / t)⌋₊ ∧
          ReachWithin collatzAccel (t / 2 ^ padicValNat 2 t) n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / t)⌋₊)}.ncard : ℝ) := by
  have ht : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; exact ht3 (dvd_zero 3))
  obtain ⟨P, hP1, hD1R, hD2R, hseed⟩ := mnInternal_exists_seedFactor t
  obtain ⟨M, hM⟩ := exists_goodSeed t ht ht3
  have h16 : targetFloor ≤ M := by
    have hlow := hM.lower
    rw [seedShift_def] at hlow
    rw [targetFloor_def]
    generalize scale 0 = b at hlow ⊢
    have h2 : 16 ^ b = 2 ^ (4 * b) := by rw [pow_mul]; norm_num
    rw [h2]
    exact (Nat.le_mul_of_pos_right _ ht).trans hlow.le
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM.pos
  have hupper : M < P * t := hseed ▸ hM.upper
  have hupperR : (M : ℝ) < P * t := by exact_mod_cast hupper
  have hP1R : (1 : ℝ) ≤ P := by exact_mod_cast hP1
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hC : (0 : ℝ) ≤ 2 ^ covExp := by positivity
  generalize (towerConstant : ℝ) = D at hX hD1R hD2R ⊢
  set Z : ℝ := X / 32 with hZdef
  have hZge : (2 : ℝ) ^ covExp * (M : ℝ) ≤ Z := by
    rw [hZdef, le_div_iff₀ (by norm_num)]
    generalize (2 : ℝ) ^ covExp = C at hD1R hC ⊢
    calc C * M * 32 ≤ C * (P * t) * 32 := by gcongr
      _ = (32 * C * P) * t := by ring
      _ ≤ D * t := by gcongr
      _ ≤ X := hX
  have hX0 : 0 < X := by
    have h32 : (32 : ℝ) ≤ 32 * 2 ^ covExp * P := by
      have hC1 : (1 : ℝ) ≤ 2 ^ covExp := one_le_pow₀ (by norm_num)
      generalize (2 : ℝ) ^ covExp = C at hC1 ⊢
      nlinarith
    nlinarith
  obtain ⟨j, hj, hZ⟩ := exists_isAdmissibleScale_of_goodSeed hM.odd h16 hZge
  have hZpos : 0 < Z := hZ.pos
  set S := sources j Z (M : ℚ) with hSdef
  have hU := lt_unweightedMass_of_goodSeed hM.odd h16 hM.not_syrPeriodic
    hM.lt_weightedCentralSum hj hZ
  have hch := mul_unweightedMass_le_of_odd hM.odd h16 hM.not_syrPeriodic hZ
  have hcount : X / ((t : ℝ) ^ (targetExp : ℝ) * D) ≤ (S.ncard : ℝ) := by
    have hκ : (targetExp : ℝ) = 25 / 11 := targetExp_cast
    set κ : ℝ := (targetExp : ℝ) with hκdef
    set e : ℝ := (M : ℝ) ^ (-κ) with he
    have hsplit : (M : ℝ) ^ (1 - κ) = M * e := by
      rw [he, sub_eq_add_neg, rpow_add hMpos, rpow_one]
    rw [hsplit] at hU
    have h1 : M * ((2 : ℝ) ^ (-(countExp : ℤ)) * e * Z) ≤ M * (S.ncard : ℝ) := by
      calc M * ((2 : ℝ) ^ (-(countExp : ℤ)) * e * Z)
          = Z * ((2 : ℝ) ^ (-(countExp : ℤ)) * (M * e)) := by ring
        _ ≤ Z * unweightedMass j Z M := mul_le_mul_of_nonneg_left hU.le hZpos.le
        _ ≤ M * S.ncard := hch
    have h2 : (2 : ℝ) ^ (-(countExp : ℤ)) * e * Z ≤ S.ncard := le_of_mul_le_mul_left h1 hMpos
    rw [countExp_def] at h2
    have hPt : (0 : ℝ) < P * t := by positivity
    set A : ℝ := ((P : ℝ) * t) ^ κ with hAdef
    have hA : 0 < A := rpow_pos_of_pos hPt _
    have hAe : A⁻¹ ≤ e := by
      rw [hAdef, ← rpow_neg hPt.le]
      exact rpow_le_rpow_of_nonpos hMpos hupperR.le (by rw [hκ]; norm_num)
    have hPκ : (P : ℝ) ^ κ ≤ (P : ℝ) ^ (3 : ℕ) := by
      rw [← rpow_natCast]
      exact rpow_le_rpow_of_exponent_le hP1R (by rw [hκ]; norm_num)
    have htκ : 0 ≤ (t : ℝ) ^ κ := by positivity
    have hden : (2 : ℝ) ^ 212 * A ≤ (t : ℝ) ^ κ * D := by
      rw [hAdef, mul_rpow (by positivity) (by positivity)]
      calc (2 : ℝ) ^ 212 * ((P : ℝ) ^ κ * (t : ℝ) ^ κ)
          ≤ (2 : ℝ) ^ 212 * ((P : ℝ) ^ 3 * (t : ℝ) ^ κ) := by gcongr
        _ = (t : ℝ) ^ κ * ((2 : ℝ) ^ 212 * (P : ℝ) ^ 3) := by ring
        _ ≤ (t : ℝ) ^ κ * D := by gcongr
    calc X / ((t : ℝ) ^ κ * D) ≤ X / ((2 : ℝ) ^ 212 * A) :=
          div_le_div_of_nonneg_left hX0.le (by positivity) hden
      _ = (2 : ℝ) ^ (-((207 : ℕ) : ℤ)) * A⁻¹ * Z := by
          rw [hZdef, zpow_neg, zpow_natCast]
          field_simp
          ring
      _ ≤ (2 : ℝ) ^ (-((207 : ℕ) : ℤ)) * e * Z := by gcongr
      _ ≤ S.ncard := h2
  have hwin : ∀ x ∈ S, Z ≤ (x : ℝ) ∧ (x : ℝ) < 32 * Z := fun x hx => by
    have := sources_subset_Ico_of_odd (t := (M : ℤ)) (by exact_mod_cast hM.odd)
      (by exact_mod_cast h16) (by simpa only [Int.cast_natCast] using hZ)
      ⟨x, by simpa only [Int.cast_natCast] using hx, rfl⟩
    exact this
  have hsub : Int.toNat '' S ⊆ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < X ∧
        (Odd n ∧ ReachWithin collatz t n ⌊(523 / 50 : ℝ) * Real.log ((n : ℝ) / t)⌋₊ ∧
          ReachWithin collatzAccel (t / 2 ^ padicValNat 2 t) n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / t)⌋₊)} := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hlo, hhi⟩ := hwin x hx
    obtain ⟨hxpos, hxodd⟩ := hM.pos_odd_of_mem_sources hx
    have hx' : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hxpos.le
    have hcast : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
      rw [← Int.cast_natCast, hx']
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · rw [hcast, hZdef] at *; linarith
    · rw [← hx'] at hxodd; exact_mod_cast hxodd
    · rw [hcast]; exact collatzOneWithin_of_mem_sources hM ht hj hx
    · rw [hcast]; exact collatzAccelOneWithin_of_mem_sources ht hM hj hx
  have hinj : Set.InjOn Int.toNat S := by
    intro a ha b hb hab
    have ha0 : 0 ≤ a := (hM.pos_odd_of_mem_sources ha).1.le
    have hb0 : 0 ≤ b := (hM.pos_odd_of_mem_sources hb).1.le
    simpa [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0] using
      congrArg (fun k : ℕ => (k : ℤ)) hab
  have hfin : {n : ℕ | 1 ≤ n ∧ (n : ℝ) < X ∧
        (Odd n ∧ ReachWithin collatz t n ⌊(523 / 50 : ℝ) * Real.log ((n : ℝ) / t)⌋₊ ∧
          ReachWithin collatzAccel (t / 2 ^ padicValNat 2 t) n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / t)⌋₊)}.Finite := by
    refine (Set.finite_Iio ⌈X⌉₊).subset fun k hk => ?_
    exact Set.mem_Iio.2 (Nat.lt_ceil.2 hk.2.1)
  rw [← hinj.ncard_image] at hcount
  exact hcount.trans (by exact_mod_cast Set.ncard_le_ncard hsub hfin)

end CollatzPosDens
