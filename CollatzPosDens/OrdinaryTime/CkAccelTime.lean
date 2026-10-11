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
public import CollatzPosDens.OrdinaryTime.FullWord
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.OrdinaryTime.SelectedPair
public import CollatzPosDens.OrdinaryTime.Kappa

/-!
# Accelerated stopping time of the sources

Let `s ≥ 1` be odd, `M` an `s`-good seed, `n ≥ 2 · 10^10` and `X > 0`. Every source
`x ∈ 𝒮_{n,X}(M)` reaches `s` under the accelerated Collatz map `T_acc` within
`⌊(34881/10000) log(x/s)⌋₊` steps.

Write `x` as the source of a selected pair `(h, w)` with full word `𝐰` of length `d`. The full
word is admissible from `M`, and along an admissible word from a positive odd integer each step
of the inverse orbit is undone by one application of the Syracuse map, which coincides with
`T_acc`; hence `T_acc^d(x) = M`. Since `3M + 1 = 2^k s` with `s` odd, `T_acc(M) = s`. The
ordinary-time constant gives `d + 1 ≤ (34881/10000) log(x/s)`, so `r = d + 1` is an admissible
time.

## Main results

* `CollatzPosDens.collatzAccelOneWithin_of_mem_sources`: every `x ∈ 𝒮_{n,X}(M)` reaches `1`
  under `T_acc` within `⌊(34881/10000) log x⌋₊` steps.

## Implementation notes

Sources are integers while `T_acc` acts on `ℕ`; the reach predicate is applied to `x.toNat`,
which is `x` itself since every source is positive. The real number `log(x/s)` is `Real.log` of
the real quotient of the casts, and `⌊·⌋₊` is the floor with positive part.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Accelerated stopping time of the sources**. Let `s ≥ 1` be
odd, `M` an `s`-good seed, `n ≥ 2 · 10^10` and `X > 0`. Every `x ∈ 𝒮_{n,X}(M)` reaches `s` under
`T_acc` within `⌊(34881/10000) log(x/s)⌋₊` steps. -/
@[collatz_pos_dens "lem_ck_accel_time"]
theorem collatzAccelOneWithin_of_mem_sources {s M : ℕ} (hs : 0 < s) (hso : Odd s)
    (hM : GoodSeed s M) {n : ℕ} (hn : 2 * 10 ^ 10 ≤ n) {X : ℝ} (hX : 0 < X) {x : ℤ}
    (hx : x ∈ sources n X (M : ℚ)) :
    ReachWithin collatzAccel s x.toNat ⌊(34881 / 10000 : ℝ) * log ((x : ℝ) / s)⌋₊ := by
  obtain ⟨⟨h, w⟩, hpair, hsrc⟩ := hx
  have hp : IsSelectedPair n X (M : ℚ) h w := hpair
  dsimp only at hsrc
  set W := fullWord h w with hW
  have hadm : Admissible (M : ℚ) W := by
    rw [hW, fullWord, admissible_append]
    refine ⟨hp.mem_centralHistories.2, ?_⟩
    have := hp.admissible
    rwa [historyEndpoint_eq_src] at this
  have hsrcW : src W (M : ℚ) = x := by
    rw [← hsrc, historyEndpoint_eq_src, hW, fullWord, src_append]
  have hadmZ : Admissible ((M : ℤ) : ℚ) W := by rwa [Int.cast_natCast]
  have hmpos : (0 : ℤ) < M := by exact_mod_cast hM.pos
  obtain ⟨m, hm, hmM⟩ :=
    hadmZ.exists_collatzAccel_iterate_src hmpos (by exact_mod_cast hM.odd)
  rw [Int.cast_natCast] at hm
  replace hmM : collatzAccel^[W.length] m = M := by exact_mod_cast hmM
  have hxm : x = m := by
    have := hsrcW.symm.trans hm; exact_mod_cast this
  subst hxm
  -- `T_acc(M) = s`
  obtain ⟨k, hk⟩ := hM.two_pow_mul
  have hMs : collatzAccel M = s := collatzAccel_eq_of_three_mul_add_one_eq hk hso
  -- the step budget
  have hkap := length_fullWord_add_one_le_kappa_mul_log hM hs hn hX hp
  rw [← hW, selectedPairSource, hsrc, Rat.cast_intCast] at hkap
  have hle : W.length + 1 ≤ ⌊(34881 / 10000 : ℝ) * log (((m : ℤ) : ℝ) / s)⌋₊ :=
    Nat.le_floor (by exact_mod_cast hkap)
  refine ⟨W.length + 1, hle, ?_⟩
  rw [Int.toNat_natCast, Function.iterate_succ_apply', hmM, hMs]

end CollatzPosDens
