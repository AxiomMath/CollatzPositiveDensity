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

Let `M` be a good seed and `n : ℕ`. If `(h, w)` and `(h', w')` lie in
`unweightedMassPairs n X M` and `src w (historyEndpoint M h) = src w' (historyEndpoint M h')`,
then `(h, w) = (h', w')`. Indeed the words `concatWord h ++ w` and `concatWord h' ++ w'` are both
admissible from `M` with a common source. Since `M > 1` is odd and `3M + 1` is a power of `4`,
hence of `2`, the Syracuse orbit of this source hits `M` only once, so the two words have the
same length; a word admissible from an odd positive integer is determined by its length and
source, so the two words are equal. Finally the central families are prefix-free, so the
factorisation of `concatWord h ++ w` is unique, giving `h = h'` and `w = w'`.

## Main results

* `CollatzPosDens.eq_of_src_eq_of_mem_unweightedMassPairs`: the map
  `(h, w) ↦ src w (historyEndpoint M h)` is injective on `unweightedMassPairs n X M`.

## Implementation notes

No positivity hypothesis on `X` is needed; `X` is an arbitrary real.

## References

* [Mazur, *Collatz positive density*], §18.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `M` is a good seed and `(h, w)`, `(h', w')` lie in `unweightedMassPairs n X M` with
`src w (historyEndpoint M h) = src w' (historyEndpoint M h')`, then `(h, w) = (h', w')`. -/
@[collatz_pos_dens "lem_source_unique_history"]
theorem eq_of_src_eq_of_mem_unweightedMassPairs {M : ℕ} (hM : GoodSeed M) {n : ℕ} {X : ℝ}
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
  have hM1 : 1 < (M : ℤ) := by
    have hl := hM.lower
    generalize scale 0 = b at hl
    have := Nat.one_le_pow b 16 (by norm_num)
    omega
  have hodd : Odd (M : ℤ) := by exact_mod_cast hM.odd
  have hpow : ∃ k : ℕ, 3 * (M : ℤ) + 1 = 2 ^ k := by
    obtain ⟨k, hk⟩ := hM.pow_four
    exact ⟨2 * k, by rw [pow_mul]; exact_mod_cast hk⟩
  have hlen := Admissible.length_eq_of_src_eq hM1 hodd hpow hc hc' hs
  have heq := Admissible.eq_of_src_eq (by omega) hodd hlen hc hc' hs
  obtain ⟨rfl, rfl⟩ := historyDetermined scale cap hh.1.1 hh'.1.1 heq
  rfl

end CollatzPosDens
