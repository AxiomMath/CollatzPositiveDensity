/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Maps.OrbitHitsSeedOnce
public import CollatzPosDens.Maps.WordDetermined
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.HistoryDetermined
public import CollatzPosDens.Terminal.UnweightedMass

/-!
# A counted pair is determined by its source

Let `s ≥ 1`, let `M` be an `s`-good seed and `n ≥ 0`. If `(h, w)` and `(h', w')` are counted
pairs of `Υ_{n,X}(M)` with `src(w, R_h) = src(w', R_{h'})`, then `(h, w) = (h', w')`. Indeed the
words `c = ŵ(h) w` and `c' = ŵ(h') w'` are both admissible from `M` with the common source
`src(c, M) = src(w, R_h)`. Since `M` is odd, positive and not Syracuse-periodic, the Syracuse
orbit of a source hits `M` only once, so `|c| = |c'|`; a word admissible from an odd positive
integer is determined by its length and source, so `c = c'`. Finally the central families
`𝒞(b_j, K_j)` are prefix-free, so the factorisation `c = w₀ ⋯ w_{n-1} w` is unique,
giving `h = h'` and `w = w'`.

## Main results

* `CollatzPosDens.eq_of_src_eq_of_mem_unweightedMassPairs`: the map
  `(h, w) ↦ src w (historyEndpoint M h)` is injective on `unweightedMassPairs n X M`.

## Implementation notes

The hypotheses `X > 0` and `s ≥ 1` are not needed and are dropped: `X` is an arbitrary real
and `s` an arbitrary natural number, since only oddness, positivity and non-periodicity of
`M` enter the argument.

## References

* [Mazur, *Collatz positive density*], §18.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Counted pairs are determined by their source.** If `M` is an `s`-good seed and `(h, w)`,
`(h', w')` are counted pairs of `Υ_{n,X}(M)` with `src(w, R_h) = src(w', R_{h'})`, then
`(h, w) = (h', w')`. -/
@[collatz_pos_dens "lem_source_unique_history"]
theorem eq_of_src_eq_of_mem_unweightedMassPairs {s M : ℕ} (hM : GoodSeed s M) {n : ℕ} {X : ℝ}
    {h h' : Fin n → Word} {w w' : Word} (hp : (h, w) ∈ unweightedMassPairs n X M)
    (hq : (h', w') ∈ unweightedMassPairs n X M)
    (hsrc : src w (historyEndpoint M h) = src w' (historyEndpoint M h')) :
    (h, w) = (h', w') := by
  obtain ⟨hh, -, -, hw⟩ := mem_unweightedMassPairs.mp hp
  obtain ⟨hh', -, -, hw'⟩ := mem_unweightedMassPairs.mp hq
  have hc : Admissible ((M : ℤ) : ℚ) (concatWord h ++ w) := by
    rw [Int.cast_natCast]
    exact admissible_append.mpr ⟨hh.2, historyEndpoint_eq_src (M : ℚ) h ▸ hw⟩
  have hc' : Admissible ((M : ℤ) : ℚ) (concatWord h' ++ w') := by
    rw [Int.cast_natCast]
    exact admissible_append.mpr ⟨hh'.2, historyEndpoint_eq_src (M : ℚ) h' ▸ hw'⟩
  have hs : src (concatWord h ++ w) ((M : ℤ) : ℚ) =
      src (concatWord h' ++ w') ((M : ℤ) : ℚ) := by
    rw [Int.cast_natCast, src_append, src_append, ← historyEndpoint_eq_src,
      ← historyEndpoint_eq_src, hsrc]
  have hlen := Admissible.length_eq_of_src_eq hM.pos hM.odd hM.not_syrPeriodic hc hc' hs
  have hodd : Odd (M : ℤ) := by exact_mod_cast hM.odd
  have heq := Admissible.eq_of_src_eq (by exact_mod_cast hM.pos) hodd hlen hc hc' hs
  obtain ⟨rfl, rfl⟩ := historyDetermined scale cap hh.1.1 hh'.1.1 heq
  rfl

end CollatzPosDens
