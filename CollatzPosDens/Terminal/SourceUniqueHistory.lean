/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Maps.DistinctSources
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Maps.SyrPeriodic
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.HistoryDetermined
public import CollatzPosDens.Seed.S05ConcatWord
public import CollatzPosDens.Seed.S05Tuples
public import CollatzPosDens.Terminal.UnweightedMass

/-!
# A counted pair is determined by its source

Let `t` be an odd positive integer that is not Syracuse-periodic, and let `j ≥ 0`. If `(h, w)` and
`(h', w')` lie in `unweightedMassPairs j X t` and `src w (historyEndpoint t h)` equals
`src w' (historyEndpoint t h')`, then `(h, w) = (h', w')`. Indeed the words `concatWord h ++ w`
and `concatWord h' ++ w'` are both admissible from `t` and have the same source. Since `t` is odd,
positive and not Syracuse-periodic, two words admissible from `t` with the same source are equal
(`Admissible.eq_of_src_eq_of_not_syrPeriodic`). Finally each history takes its values in the
prefix-free families `centralFamily`, so the factorisation `concatWord h ++ w` is unique
(`historyDetermined`), giving `h = h'` and `w = w'`.

## Main results

* `CollatzPosDens.eq_of_src_eq_of_mem_unweightedMassPairs`: the map
  `(h, w) ↦ src w (historyEndpoint t h)` is injective on `unweightedMassPairs j X t`.

## Implementation notes

A history `(w_0, …, w_{j-1})` is a map `Fin j → Word`. No positivity hypothesis on `X` is needed:
`X` is an arbitrary real.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Counted pairs are determined by their source.** Let `t` be an odd positive integer that is
not Syracuse-periodic. If `(h, w)` and `(h', w')` lie in `unweightedMassPairs j X t` and
`src w (historyEndpoint t h) = src w' (historyEndpoint t h')`, then `(h, w) = (h', w')`. -/
@[collatz_pos_dens "lem_source_unique_history"]
theorem eq_of_src_eq_of_mem_unweightedMassPairs {t : ℕ} (hpos : 0 < t) (hodd : Odd t)
    (hper : ¬ SyrPeriodic t) {j : ℕ} {X : ℝ} {h h' : Fin j → Word} {w w' : Word}
    (hp : (h, w) ∈ unweightedMassPairs j X t) (hq : (h', w') ∈ unweightedMassPairs j X t)
    (hsrc : src w (historyEndpoint t h) = src w' (historyEndpoint t h')) :
    (h, w) = (h', w') := by
  obtain ⟨hh, -, -, hw⟩ := mem_unweightedMassPairs.mp hp
  obtain ⟨hh', -, -, hw'⟩ := mem_unweightedMassPairs.mp hq
  have hc : Admissible ((t : ℤ) : ℚ) (concatWord h ++ w) := by
    rw [Int.cast_natCast]
    exact admissible_append.mpr ⟨hh.2, historyEndpoint_eq_src (t : ℚ) h ▸ hw⟩
  have hc' : Admissible ((t : ℤ) : ℚ) (concatWord h' ++ w') := by
    rw [Int.cast_natCast]
    exact admissible_append.mpr ⟨hh'.2, historyEndpoint_eq_src (t : ℚ) h' ▸ hw'⟩
  have hs : src (concatWord h ++ w) ((t : ℤ) : ℚ) =
      src (concatWord h' ++ w') ((t : ℤ) : ℚ) := by
    rw [Int.cast_natCast, src_append, src_append, ← historyEndpoint_eq_src,
      ← historyEndpoint_eq_src, hsrc]
  have heq := Admissible.eq_of_src_eq_of_not_syrPeriodic hpos hodd hper hc hc' hs
  obtain ⟨rfl, rfl⟩ := historyDetermined scale cap hh.1.1 hh'.1.1 heq
  rfl

end CollatzPosDens
