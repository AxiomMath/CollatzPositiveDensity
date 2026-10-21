/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Maps.CollatzOfInverse
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.OrdinaryTime.S07FullWord
public import CollatzPosDens.Transfer.S03Log3Bounds
public import CollatzPosDens.Recipe.SeedShift
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Transfer.S02Log2Lower
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.OrdinaryTime.S07SelectedPair
public import CollatzPosDens.OrdinaryTime.CkOrdinaryResidual
public import CollatzPosDens.OrdinaryTime.Kappa
public import CollatzPosDens.OrdinaryTime.Telescope

/-!
# Ordinary time bound for counted sources

Let `t ≥ 1`, `t₁` a `t`-good seed, `n ≥ covGen = 23000` and `X` real. Every source
`x ∈ sources n X t₁` reaches `t` under the Collatz map within `⌊(523/50) log (x / t)⌋₊` steps.

Writing `x` as the source of a selected pair `(h, w)` with full word `𝐰` of length `d`, the
inverse orbit of `𝐰` from `t₁` is undone by the Collatz map in `d + A(𝐰)` steps, so
`T^{d + A(𝐰)}(x) = t₁`; since `t₁` is odd and `3t₁ + 1 = 2^a t`, a further `1 + a` steps reach
`t`. As `a log 2 = log (3t₁ + 1) - log t ≤ log t₁ + c_step - log t`, the number of steps
`r = (d + 1) + (A(𝐰) + a)` satisfies
`r log 2 ≤ (d + 1)(log 2 + c_step) + log (x / t) ≤ (c_acc (log 2 + c_step) + 1) log (x / t)`
by the telescoping bound and the ordinary-time constant `c_acc = 34881/10000`, where
`c_step = log (3 + 1/4096)` (valid as `t₁ > 2^{σ_sd} t ≥ 4096`), and
`c_acc (log 2 + c_step) + 1 ≤ (523/50) log 2` is an explicit numerical check.

## Main results

* `CollatzPosDens.collatzOneWithin_of_mem_sources`: every counted source reaches `t` within
  `⌊(523/50) log (x / t)⌋₊` Collatz steps.

## Implementation notes

Sources are integers while the Collatz map acts on `ℕ`; the statement applies the predicate to
`x.toNat`, which is `x` itself since every source is positive. The good seed `t₁` is a natural
number, cast to `ℚ` as the starting point of the source set. The source states the result for
`3 ∤ t` and `X > 0`; neither hypothesis is used, so both are dropped. The numerical check uses
the bounds `log₂ 3 < 317/200` and `693147180/10^9 < log 2`, and
the exact value of the ordinary-clock residual.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- If `w` is admissible from a positive odd integer `R`, then `src(w, R)` is a natural number
`m` with `T^{|w| + A(w)}(m) = R`: the Collatz map undoes the whole inverse orbit. -/
private theorem time_exists_src_eq_collatz_iterate :
    ∀ (w : Word) {R : ℕ}, 0 < R → Odd R → Admissible (R : ℚ) w →
      ∃ m : ℕ, src w R = m ∧ collatz^[w.length + Word.valSum w] m = R
  | [], R, _, _, _ => ⟨R, by simp⟩
  | a :: v, R, hpos, hodd, hw => by
    rw [show a :: v = [a] ++ v from rfl, admissible_append] at hw
    obtain ⟨ha, hv⟩ := hw
    have ha' : Admissible ((R : ℤ) : ℚ) [a] := by rwa [Int.cast_natCast]
    have hposZ : (0 : ℤ) < R := by exact_mod_cast hpos
    have hoddZ : Odd (R : ℤ) := by exact_mod_cast hodd
    obtain ⟨m, k, hm, hk, hmk⟩ :=
      ha'.exists_collatz_iterate_inverseOrbit hposZ hoddZ (i := 0) (by simp)
    obtain ⟨z, hz, hzpos, hzodd⟩ := ha'.exists_src_eq_pos_odd hposZ hoddZ
    rw [Int.cast_natCast] at hm hk hz
    have hsm : src [a] (R : ℚ) = m := by
      rw [← hm]; rfl
    have hkR : k = R := by
      rw [inverseOrbit_zero] at hk; exact_mod_cast hk.symm
    have hzm : (z : ℤ) = m := by
      have := hz.symm.trans hsm; exact_mod_cast this
    have hmpos : 0 < m := by omega
    have hmodd : Odd m := by
      have : Odd (m : ℤ) := hzm ▸ hzodd
      exact_mod_cast this
    rw [hsm] at hv
    obtain ⟨p, hp, hpm⟩ := time_exists_src_eq_collatz_iterate v hmpos hmodd hv
    refine ⟨p, ?_, ?_⟩
    · rw [show a :: v = [a] ++ v from rfl, src_append, hsm, hp]
    · simp only [List.getElem_cons_zero] at hmk
      rw [List.length_cons, Word.valSum_cons,
        show v.length + 1 + ((a : ℕ) + Word.valSum v) =
          (1 + (a : ℕ)) + (v.length + Word.valSum v) by ring,
        Function.iterate_add_apply, hpm, hmk, hkR]

/-- If `3t₁ + 1 = 2^k t` with `t₁` odd, then `T^{1 + k}(t₁) = t`. -/
private theorem time_collatz_iterate_seed {t t₁ k : ℕ} (hodd : Odd t₁)
    (hk : 3 * t₁ + 1 = 2 ^ k * t) : collatz^[1 + k] t₁ = t := by
  rw [add_comm, Function.iterate_add_apply, Function.iterate_one, collatz_of_odd hodd, hk,
    collatz_iterate_two_pow_mul]

/-- **Ordinary time bound for counted sources.** Let `t ≥ 1`, `t₁` a `t`-good seed,
`n ≥ covGen = 23000` and `X` real. Every `x ∈ sources n X t₁` reaches `t` under the Collatz map
within `⌊(523/50) log (x / t)⌋₊` steps. -/
@[collatz_pos_dens "lem_time"]
theorem collatzOneWithin_of_mem_sources {t t₁ : ℕ} (ht₁ : GoodSeed t t₁) (ht : 0 < t) {n : ℕ}
    (hn : covGen ≤ n) {X : ℝ} {x : ℤ} (hx : x ∈ sources n X (t₁ : ℚ)) :
    ReachWithin collatz t x.toNat ⌊(523 / 50 : ℝ) * Real.log ((x : ℝ) / t)⌋₊ := by
  obtain ⟨⟨h, w⟩, hp, hsrc⟩ := mem_sources.1 hx
  have hp : IsSelectedPair n X t₁ h w := hp
  set W := fullWord h w with hW
  have hadm : Admissible (t₁ : ℚ) W := by
    rw [hW, fullWord, admissible_append]
    refine ⟨admissible_concatWord_of_mem_centralHistories hp.mem_centralHistories, ?_⟩
    have := hp.admissible
    rwa [historyEndpoint_eq_src] at this
  have hsrcW : src W (t₁ : ℚ) = x := by
    rw [← hsrc, historyEndpoint_eq_src, hW, fullWord, src_append]
  obtain ⟨m, hm, hmM⟩ := time_exists_src_eq_collatz_iterate W ht₁.pos ht₁.odd hadm
  have hxm : x = m := by
    have := hsrcW.symm.trans hm; exact_mod_cast this
  subst hxm
  obtain ⟨k, -, hk⟩ := ht₁.two_pow_mul
  have hiter : collatz^[(1 + k) + (W.length + Word.valSum W)] m = t := by
    rw [Function.iterate_add_apply, hmM, time_collatz_iterate_seed ht₁.odd hk]
  refine ⟨_, ?_, by simpa using hiter⟩
  have hp' : IsSelectedPair n X ((t₁ : ℤ) : ℚ) h w := by rwa [Int.cast_natCast]
  have ht₁floor : targetFloor ≤ t₁ := by
    have hσ : (2 : ℕ) ^ seedShift = targetFloor := by
      rw [seedShift_def, targetFloor_def, pow_mul, show (2 : ℕ) ^ 4 = 16 from rfl]
    rw [← hσ]
    exact (Nat.le_mul_of_pos_right _ ht).trans ht₁.lower.le
  have htel := valSum_fullWord_mul_log_two_le (by exact_mod_cast ht₁.odd)
    (by exact_mod_cast ht₁floor) hp'
  simp only [Int.cast_natCast] at htel
  clear ht₁floor
  have hkap := length_fullWord_add_one_le_kappa_mul_log ht₁ ht hn hp
  rw [← hW] at htel hkap
  have hxR : ((selectedPairSource (t₁ : ℚ) h w : ℚ) : ℝ) = (m : ℝ) := by
    rw [selectedPairSource, hsrc]; push_cast; rfl
  rw [hxR] at htel hkap
  clear_value W
  clear hxR hx hp hp' hsrc hsrcW hadm hW hm
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have ht₁pos : (0 : ℝ) < t₁ := by exact_mod_cast ht₁.pos
  have hmpos : (0 : ℝ) < m := by
    have hfix : ∀ j : ℕ, collatz^[j] 0 = 0 := fun j => by
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', ih]; rfl
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; have := ht₁.pos; rw [hfix] at hmM; omega
    · exact_mod_cast h0
  set ℓ := log ((m : ℝ) / t) with hℓ
  have hℓeq : ℓ = log (m : ℝ) - log t := log_div hmpos.ne' htpos.ne'
  set d : ℝ := (W.length : ℝ) with hd
  set A : ℝ := (Word.valSum W : ℝ) with hA
  set L := log 2 with hL
  set θ := log (3 + 1 / 4096) with hθ
  have hLpos : 0 < L := log_pos one_lt_two
  have ht₁4096 : (4096 : ℝ) ≤ t₁ := by
    have h36 : (2 : ℝ) ^ 36 ≤ t₁ := by exact_mod_cast (ht₁.two_pow_thirtySix_lt ht).le
    linarith [show (4096 : ℝ) ≤ 2 ^ 36 by norm_num]
  have hseed : (k : ℝ) * L ≤ log t₁ + θ - log t := by
    have h1 : ((3 * t₁ + 1 : ℕ) : ℝ) = t₁ * (3 + 1 / t₁) := by
      push_cast; field_simp
    have h2 : (k : ℝ) * L = log ((3 * t₁ + 1 : ℕ) : ℝ) - log t := by
      rw [hk, Nat.cast_mul, Nat.cast_pow, log_mul (by positivity) htpos.ne', log_pow]
      push_cast; ring
    have h3 : log (3 + 1 / (t₁ : ℝ)) ≤ θ :=
      log_le_log (by positivity) (by gcongr)
    rw [h2, h1, log_mul ht₁pos.ne' (by positivity)]
    linarith
  have hlog3 : log 3 ≤ 317 / 200 * L := by
    have := logb_two_three_bounds.2
    rw [logb, div_lt_iff₀ hLpos] at this
    linarith
  have hθhi : θ ≤ log 3 + 1 / 12288 := by
    have hθeq : θ = log 3 + log (1 + 1 / 12288) := by
      rw [hθ, ← log_mul (by norm_num) (by norm_num)]; norm_num
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / 12288 by norm_num)
    linarith
  have hL2 := log_two_gt_693147180
  have hres := ckOrdinaryResidual_eq (K := ℝ)
  have hθpos : 0 < θ := log_pos (by norm_num)
  have hℓ0 : 0 ≤ ℓ := by
    have : (0 : ℝ) ≤ d + 1 := by positivity
    nlinarith
  have hconst : (34881 / 10000 : ℝ) * (L + θ) + 1 ≤ 523 / 50 * L := by
    rw [← hL] at hL2
    nlinarith
  have hrL : ((1 + k + (W.length + Word.valSum W) : ℕ) : ℝ) * L ≤
      (34881 / 10000 * (L + θ) + 1) * ℓ := by
    have e : ((1 + k + (W.length + Word.valSum W) : ℕ) : ℝ) * L =
        (d + 1) * L + A * L + (k : ℝ) * L := by
      rw [hd, hA]; push_cast; ring
    have k1 : (d + 1) * (L + θ) ≤ (34881 / 10000 * ℓ) * (L + θ) :=
      mul_le_mul_of_nonneg_right hkap (by positivity)
    rw [e]
    linarith
  have hfin : ((1 + k + (W.length + Word.valSum W) : ℕ) : ℝ) ≤ 523 / 50 * ℓ := by
    have : ((1 + k + (W.length + Word.valSum W) : ℕ) : ℝ) * L ≤ (523 / 50 * ℓ) * L := by
      have := mul_le_mul_of_nonneg_right hconst hℓ0
      nlinarith
    exact le_of_mul_le_mul_right this hLpos
  have hcast : ((m : ℤ) : ℝ) = (m : ℝ) := rfl
  simp only [hcast]
  exact Nat.le_floor hfin

end CollatzPosDens
