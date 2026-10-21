/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Maps.Syracuse
public import CollatzPosDens.Maps.SyracuseOfInverse
public import CollatzPosDens.Maps.OrbitHitsSeedOnce
public import CollatzPosDens.Maps.InverseOrbitOdd
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.OrdinaryTime.S07FullWord
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.OrdinaryTime.S07SelectedPair
public import CollatzPosDens.OrdinaryTime.Kappa

/-!
# Accelerated stopping time of the sources

Let `t ≥ 1`, `t₁` a `t`-good seed, `n ≥ covGen = 23000` and `X` real. Every source
`x ∈ sources n X t₁` reaches the odd part `t / 2^{v₂(t)}` of `t` under the accelerated Collatz
map `collatzAccel` within `⌊(34881/10000) log(x/t)⌋₊` steps.

Write `x` as the source of a selected pair `(h, w)` with full word `fullWord h w` of length `d`.
The full word is admissible from `t₁`, and along an admissible word from a positive odd integer
each step of the inverse orbit is undone by one application of the Syracuse map, which coincides
with `collatzAccel`; hence `collatzAccel^d(x) = t₁`. Since `3t₁ + 1 = 2^a t = 2^{a + v₂(t)} t'`
with `t'` odd, `collatzAccel(t₁) = t' = t / 2^{v₂(t)}`. The bound
`length_fullWord_add_one_le_kappa_mul_log` gives `d + 1 ≤ (34881/10000) log(x/t)` (it uses the
lower bound `2^{σ_sd} t < t₁` of a good seed), so `r = d + 1` is an admissible time.

## Main results

* `CollatzPosDens.collatzAccelOneWithin_of_mem_sources`: every source reaches `t / 2^{v₂(t)}`
  within `⌊(34881/10000) log(x/t)⌋₊` accelerated steps.

## Implementation notes

Sources are integers while `collatzAccel` acts on `ℕ`; the reach predicate is applied to
`x.toNat`, which is `x` itself since every source is positive. The real number `log(x/t)` is
`Real.log` of the real quotient of the casts, `⌊·⌋₊` is the floor with positive part, and `v₂` is
`padicValNat 2`. The statement holds without the hypotheses `3 ∤ t` and `X > 0`, so it is stated
without them.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Accelerated stopping time of the sources.** Let `t ≥ 1`, `t₁` a `t`-good seed,
`n ≥ covGen` and `X` real. Every `x ∈ sources n X t₁` reaches `t / 2^{v₂(t)}` under
`collatzAccel` within `⌊(34881/10000) log(x/t)⌋₊` steps. -/
@[collatz_pos_dens "lem_ck_accel_time"]
theorem collatzAccelOneWithin_of_mem_sources {t t₁ : ℕ} (ht : 0 < t) (ht₁ : GoodSeed t t₁)
    {n : ℕ} (hn : covGen ≤ n) {X : ℝ} {x : ℤ} (hx : x ∈ sources n X (t₁ : ℚ)) :
    ReachWithin collatzAccel (t / 2 ^ padicValNat 2 t) x.toNat
      ⌊(34881 / 10000 : ℝ) * log ((x : ℝ) / t)⌋₊ := by
  obtain ⟨⟨h, w⟩, hpair, hsrc⟩ := hx
  have hp : IsSelectedPair n X (t₁ : ℚ) h w := hpair
  dsimp only at hsrc
  set W := fullWord h w with hW
  have hadm : Admissible (t₁ : ℚ) W := by
    rw [hW, fullWord, admissible_append]
    refine ⟨hp.mem_centralHistories.2, ?_⟩
    have := hp.admissible
    rwa [historyEndpoint_eq_src] at this
  have hsrcW : src W (t₁ : ℚ) = x := by
    rw [← hsrc, historyEndpoint_eq_src, hW, fullWord, src_append]
  have hadmZ : Admissible ((t₁ : ℤ) : ℚ) W := by rwa [Int.cast_natCast]
  have hmpos : (0 : ℤ) < t₁ := by exact_mod_cast ht₁.pos
  obtain ⟨m, hm, hmt₁⟩ :=
    hadmZ.exists_collatzAccel_iterate_src hmpos (by exact_mod_cast ht₁.odd)
  rw [Int.cast_natCast] at hm
  replace hmt₁ : collatzAccel^[W.length] m = t₁ := by exact_mod_cast hmt₁
  have hxm : x = m := by
    have := hsrcW.symm.trans hm; exact_mod_cast this
  subst hxm
  obtain ⟨a, -, ha⟩ := ht₁.two_pow_mul
  have ht₁t : collatzAccel t₁ = t / 2 ^ padicValNat 2 t := by
    rw [collatzAccel_def, ha, padicValNat.mul (by positivity) ht.ne', padicValNat.prime_pow,
      pow_add, Nat.mul_div_mul_left _ _ (by positivity)]
  have hkap := length_fullWord_add_one_le_kappa_mul_log ht₁ ht hn hp
  rw [← hW, selectedPairSource, hsrc, Rat.cast_intCast] at hkap
  have hle : W.length + 1 ≤ ⌊(34881 / 10000 : ℝ) * log (((m : ℤ) : ℝ) / t)⌋₊ :=
    Nat.le_floor (by exact_mod_cast hkap)
  refine ⟨W.length + 1, hle, ?_⟩
  rw [Int.toNat_natCast, Function.iterate_succ_apply', hmt₁, ht₁t]

end CollatzPosDens
