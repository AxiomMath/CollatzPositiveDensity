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
public import CollatzPosDens.OrdinaryTime.FullWord
public import CollatzPosDens.OrdinaryTime.Log2Sharp
public import CollatzPosDens.Transfer.Log3Bounds
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.OrdinaryTime.SelectedPair
public import CollatzPosDens.OrdinaryTime.CkOrdinaryResidual
public import CollatzPosDens.OrdinaryTime.Kappa
public import CollatzPosDens.OrdinaryTime.Telescope

/-!
# Ordinary time bound for counted sources

Let `M` be a good seed, `n ≥ 2 · 10^10` and `X > 0`. Every source `x ∈ 𝒮_{n,X}(M)` reaches `1`
under the Collatz map within `⌊(523/50) log x⌋₊` steps.

Writing `x` as the source of a selected pair `(h, w)` with full word `𝐰` of length `d`, the
inverse orbit of `𝐰` from `M` is undone by the Collatz map in `d + A(𝐰)` steps, so
`T^{d + A(𝐰)}(x) = M`; since `3M + 1 = 4^v`, a further `1 + 2v` steps reach `1`. The number of
steps `r = (d + 1) + (A(𝐰) + 2v)` satisfies
`r log 2 ≤ (d + 1)(log 2 + θ) + log x ≤ (κ (log 2 + θ) + 1) log x`
by the telescoping bound and the ordinary-time constant `κ = 34881/10000`, where
`θ = log (3 + 1/4096)`, and `κ (log 2 + θ) + 1 ≤ (523/50) log 2` is an explicit numerical check.

## Main results

* `CollatzPosDens.collatzOneWithin_of_mem_sources`: every source `x ∈ 𝒮_{n,X}(M)` reaches `1`
  within `⌊(523/50) log x⌋₊` Collatz steps.

## Implementation notes

Sources are integers while the Collatz map acts on `ℕ`; the statement applies the predicate to
`x.toNat`, which is `x` itself since every source is positive. The good seed `M` is a natural
number, cast to `ℚ` as the starting point of the source set.

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

/-- If `3M + 1 = 4^v` with `M` odd, then `T^{1 + 2v}(M) = 1`. -/
private theorem time_collatz_iterate_seed {M v : ℕ} (hodd : Odd M) (hv : 3 * M + 1 = 4 ^ v) :
    collatz^[1 + 2 * v] M = 1 := by
  rw [add_comm, Function.iterate_add_apply, Function.iterate_one, collatz_of_odd hodd, hv,
    show (4 : ℕ) ^ v = 2 ^ (2 * v) * 1 by rw [pow_mul]; norm_num, collatz_iterate_two_pow_mul]

/-- Let `M` be a good seed, `n ≥ 2 · 10^10` and `X > 0`. Every source `x ∈ 𝒮_{n,X}(M)` reaches `1`
under the Collatz map within `⌊(523/50) log x⌋₊` steps. -/
@[collatz_pos_dens "lem_time"]
theorem collatzOneWithin_of_mem_sources {M : ℕ} (hM : GoodSeed M) {n : ℕ}
    (hn : 2 * 10 ^ 10 ≤ n) {X : ℝ} (hX : 0 < X) {x : ℤ} (hx : x ∈ sources n X (M : ℚ)) :
    CollatzOneWithin x.toNat ⌊(523 / 50 : ℝ) * log x⌋₊ := by
  obtain ⟨⟨h, w⟩, hp, hsrc⟩ := mem_sources.1 hx
  have hp : IsSelectedPair n X M h w := hp
  set W := fullWord h w with hW
  have hadm : Admissible (M : ℚ) W := by
    rw [hW, fullWord, admissible_append]
    refine ⟨admissible_concatWord_of_mem_centralHistories hp.mem_centralHistories, ?_⟩
    have := hp.admissible
    rwa [historyEndpoint_eq_src] at this
  have hsrcW : src W (M : ℚ) = x := by
    rw [← hsrc, historyEndpoint_eq_src, hW, fullWord, src_append]
  obtain ⟨m, hm, hmM⟩ := time_exists_src_eq_collatz_iterate W hM.pos hM.odd hadm
  have hxm : x = m := by
    have := hsrcW.symm.trans hm; exact_mod_cast this
  subst hxm
  obtain ⟨v, hv⟩ := hM.pow_four
  have hiter : collatz^[(1 + 2 * v) + (W.length + Word.valSum W)] m = 1 := by
    rw [Function.iterate_add_apply, hmM, time_collatz_iterate_seed hM.odd hv]
  refine ⟨_, ?_, by simpa using hiter⟩
  have htel := valSum_fullWord_mul_log_two_le hM hX hp
  have hkap := length_fullWord_add_one_le_kappa_mul_log hM hn hX hp
  rw [← hW] at htel hkap
  have hxR : ((selectedPairSource (M : ℚ) h w : ℚ) : ℝ) = (m : ℝ) := by
    rw [selectedPairSource, hsrc]; push_cast; rfl
  rw [hxR] at htel hkap
  set ℓ := log (m : ℝ) with hℓ
  set d : ℝ := (W.length : ℝ) with hd
  set A : ℝ := (Word.valSum W : ℝ) with hA
  set L := log 2 with hL
  set θ := log (3 + 1 / 4096) with hθ
  have hLpos : 0 < L := log_pos one_lt_two
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM.pos
  have hM4096 : (4096 : ℝ) ≤ M := by
    have h16 : ((16 : ℝ) ^ scale 0) ≤ M := by exact_mod_cast hM.lower.le
    rw [scale_zero] at h16
    linarith
  have hseed : (2 * v : ℝ) * L ≤ log M + θ := by
    have h1 : ((3 * M + 1 : ℕ) : ℝ) = M * (3 + 1 / M) := by
      push_cast; field_simp
    have h2 : (2 * v : ℝ) * L = log ((3 * M + 1 : ℕ) : ℝ) := by
      rw [hv, Nat.cast_pow, log_pow, show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, log_pow]
      push_cast; ring
    have h3 : log (3 + 1 / (M : ℝ)) ≤ θ :=
      log_le_log (by positivity) (by gcongr)
    rw [h2, h1, log_mul hMpos.ne' (by positivity)]
    linarith
  have hlog3 : log 3 ≤ 317 / 200 * L := by
    have := logb_two_three_bounds.2
    rw [logb, div_le_iff₀ hLpos] at this
    linarith
  have hθhi : θ ≤ log 3 + 1 / 12288 := by
    have hθeq : θ = log 3 + log (1 + 1 / 12288) := by
      rw [hθ, ← log_mul (by norm_num) (by norm_num)]; norm_num
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / 12288 by norm_num)
    linarith
  have hL2 := log_two_gt_sharp
  have hres := ckOrdinaryResidual_eq (K := ℝ)
  have hθpos : 0 < θ := log_pos (by norm_num)
  have hℓ0 : 0 ≤ ℓ := by
    have : (0 : ℝ) ≤ d + 1 := by positivity
    nlinarith
  have hconst : (34881 / 10000 : ℝ) * (L + θ) + 1 ≤ 523 / 50 * L := by
    rw [← hL] at hL2
    nlinarith
  have hrL : ((1 + 2 * v + (W.length + Word.valSum W) : ℕ) : ℝ) * L ≤
      (34881 / 10000 * (L + θ) + 1) * ℓ := by
    have e : ((1 + 2 * v + (W.length + Word.valSum W) : ℕ) : ℝ) * L =
        (d + 1) * L + A * L + (2 * v : ℝ) * L := by
      rw [hd, hA]; push_cast; ring
    have k1 : (d + 1) * (L + θ) ≤ (34881 / 10000 * ℓ) * (L + θ) :=
      mul_le_mul_of_nonneg_right hkap (by positivity)
    rw [e]
    linarith
  have hfin : ((1 + 2 * v + (W.length + Word.valSum W) : ℕ) : ℝ) ≤ 523 / 50 * ℓ := by
    have : ((1 + 2 * v + (W.length + Word.valSum W) : ℕ) : ℝ) * L ≤ (523 / 50 * ℓ) * L := by
      have := mul_le_mul_of_nonneg_right hconst hℓ0
      nlinarith
    exact le_of_mul_le_mul_right this hLpos
  have hcast : ((m : ℤ) : ℝ) = (m : ℝ) := rfl
  simp only [hcast]
  exact Nat.le_floor hfin

end CollatzPosDens
