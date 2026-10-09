/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.OrdinaryTime.FullWord
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.OrdinaryTime.SelectedPair
public import CollatzPosDens.OrdinaryTime.OrbitLarge

/-!
# The telescoping bound for the valuation sum of a full word

Let `M` be a good seed, `n ∈ ℕ`, `X > 0`, and `(h, w)` a selected pair of level `(M, n, X)`
with full word `𝐰` of length `d` and source `x`. Then
`A(𝐰) log 2 ≤ log x - log M + d θ`, where `θ = log (3 + 1/4096)`.

Writing `𝐰 = (a₁, …, a_d)` with inverse orbit `R₀ = M, …, R_d = x`, the relation
`3 R_i + 1 = 2^{a_i} R_{i-1}` gives
`a_i log 2 = log R_i - log R_{i-1} + log (3 + 1/R_i)`, which telescopes; each correction
`log (3 + 1/R_i)` is at most `θ` because `R_i ≥ 4096`.

## Main results

* `CollatzPosDens.valSum_mul_log_two_le_of_le_inverseOrbit`: the telescoping bound for any
  word whose inverse orbit stays above a positive constant `c`.
* `CollatzPosDens.valSum_fullWord_mul_log_two_le`: the telescoping bound for the full word of a
  selected pair.

## Implementation notes

The constant `θ = log (12289/4096)` is not given a name; it is written out as
`Real.log (3 + 1 / 4096)`. The general form replaces `4096` by any positive lower bound `c` of
the inverse orbit and the selected pair by an arbitrary word.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The inverse orbit of `a :: v` from `R`, shifted by one, is the inverse orbit of `v` from
`invStep a R`. -/
private theorem telescope_inverseOrbit_cons_succ (a : ℕ+) (v : Word) (R : ℚ) (i : ℕ) :
    inverseOrbit (a :: v) R (i + 1) = inverseOrbit v (invStep a R) i := rfl

/-- One step of the telescope: if `R ≥ c` and `R' = (2^a R - 1)/3 ≥ c` with `c > 0`, then
`a log 2 ≤ log R' - log R + log (3 + 1/c)`. -/
private theorem telescope_step {a : ℕ} {R c : ℚ} (hc : 0 < c) (hR : c ≤ R)
    (hR' : c ≤ invStep a R) :
    (a : ℝ) * log 2 ≤ log (invStep a R : ℝ) - log (R : ℝ) + log (3 + 1 / (c : ℝ)) := by
  have hc' : (0 : ℝ) < c := Rat.cast_pos.2 hc
  have hr : (c : ℝ) ≤ R := Rat.cast_le.2 hR
  have hr' : (c : ℝ) ≤ invStep a R := Rat.cast_le.2 hR'
  set r : ℝ := (R : ℝ)
  set r' : ℝ := (invStep a R : ℝ)
  have hrpos : 0 < r := hc'.trans_le hr
  have hr'pos : 0 < r' := hc'.trans_le hr'
  have hrel : (2 : ℝ) ^ a * r = r' * (3 + 1 / r') := by
    have : r' = ((2 : ℝ) ^ a * r - 1) / 3 := by
      simp only [r', r, invStep]; push_cast; ring
    field_simp
    linarith
  have hlog : (a : ℝ) * log 2 + log r = log r' + log (3 + 1 / r') := by
    rw [← log_pow, ← log_mul (by positivity) hrpos.ne', hrel,
      log_mul hr'pos.ne' (by positivity)]
  have hmono : log (3 + 1 / r') ≤ log (3 + 1 / (c : ℝ)) :=
    log_le_log (by positivity) (by gcongr)
  linarith

/-- **Telescoping bound.** If every term of the inverse orbit of `v` from `R` is at least
`c > 0`, then `A(v) log 2 ≤ log src(v, R) - log R + |v| log (3 + 1/c)`. -/
theorem valSum_mul_log_two_le_of_le_inverseOrbit {c : ℚ} (hc : 0 < c) :
    ∀ (v : Word) (R : ℚ), (∀ i ≤ v.length, c ≤ inverseOrbit v R i) →
      (Word.valSum v : ℝ) * log 2 ≤
        log (src v R : ℝ) - log (R : ℝ) + v.length * log (3 + 1 / (c : ℝ))
  | [], R, _ => by simp
  | a :: v, R, hv => by
    have hR : c ≤ R := by simpa using hv 0 (Nat.zero_le _)
    have hR' : c ≤ invStep a R := by
      simpa [telescope_inverseOrbit_cons_succ] using hv 1 (by simp)
    have ih := valSum_mul_log_two_le_of_le_inverseOrbit hc v (invStep a R) fun i hi => by
      rw [← telescope_inverseOrbit_cons_succ]
      exact hv (i + 1) (by simpa using hi)
    have hstep := telescope_step hc hR hR'
    simp only [Word.valSum_cons, src_cons, List.length_cons]
    push_cast
    nlinarith

/-- **Telescoping bound for full words.** Let `M` be a good seed, `n ∈ ℕ`, `X > 0`, and
`(h, w)` a selected pair of level `(M, n, X)` with full word `𝐰` of length `d` and source
`x = src(w, R_h)`. Then `A(𝐰) log 2 ≤ log x - log M + d θ`, where `θ = log (3 + 1/4096)`. -/
@[collatz_pos_dens "lem_telescope"]
theorem valSum_fullWord_mul_log_two_le {n : ℕ} {M : ℕ} (hM : GoodSeed M) {X : ℝ}
    (hX : 0 < X) {h : Fin n → Word} {w : Word} (hp : IsSelectedPair n X M h w) :
    (Word.valSum (fullWord h w) : ℝ) * log 2 ≤
      log (selectedPairSource M h w : ℝ) - log (M : ℝ) +
        (fullWord h w).length * log (3 + 1 / 4096) := by
  have key := valSum_mul_log_two_le_of_le_inverseOrbit (c := 4096) (by norm_num)
    (fullWord h w) M fun i hi => four_thousand_ninety_six_le_inverseOrbit_fullWord hM hX hp hi
  have hsrc : src (fullWord h w) (M : ℚ) = selectedPairSource M h w := by
    rw [selectedPairSource, historyEndpoint_eq_src, fullWord, src_append]
  rw [hsrc] at key
  simpa using key

end CollatzPosDens
