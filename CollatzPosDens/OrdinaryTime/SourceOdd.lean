/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Maps.InverseOrbitOdd
public import CollatzPosDens.OrdinaryTime.FullWord
public import CollatzPosDens.OrdinaryTime.SelectedPair
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.Terminal.UnweightedMass

/-!
# Counted sources are odd

Let `M` be a positive odd integer, `n ∈ ℕ` and `X` real. Every source `x ∈ 𝒮_{n,X}(M)` is a
positive odd integer. Indeed, write `x = src(w, R_h)` for a selected pair `(h, w)` of level
`(M, n, X)`. The concatenated central blocks `ŵ(h)` are admissible from `M` and `w` is admissible
from `R_h = src(ŵ(h), M)`, so the full word `𝐰 = ŵ(h) w` is admissible from `M`, and its source
from `M` is `src(w, R_h) = x`. The last term of the inverse orbit of a positive odd integer along
an admissible word is a positive odd integer.

This applies in particular to an `s`-good seed `M`, which is odd and positive.

## Main results

* `CollatzPosDens.pos_odd_of_mem_sources_of_pos_odd`: the statement for a positive odd starting
  point `M`.
* `CollatzPosDens.GoodSeed.pos_odd_of_mem_sources`: every `x ∈ 𝒮_{n,X}(M)` for an `s`-good seed
  `M` is a positive odd integer.
* `CollatzPosDens.GoodSeed.odd_toNat_of_mem_sources`: the natural number `x.toNat` counted for
  such a source is `x` itself and is odd.

## Implementation notes

The source set consists of integers, while the Collatz map acts on `ℕ`; the corollary
`CollatzPosDens.GoodSeed.odd_toNat_of_mem_sources` records the statement for `x.toNat`. Neither
`s ≥ 1` nor `X > 0` is needed: only the oddness and positivity of the seed enter.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {X : ℝ}

/-- If `M` is a positive odd integer, every source `x ∈ 𝒮_{n,X}(M)` is a positive odd integer. -/
theorem pos_odd_of_mem_sources_of_pos_odd {M : ℤ} (hpos : 0 < M) (hodd : Odd M) {x : ℤ}
    (hx : x ∈ sources n X (M : ℚ)) : 0 < x ∧ Odd x := by
  obtain ⟨⟨h, w⟩, hp, hsrc⟩ := mem_sources.1 hx
  have hp : IsSelectedPair n X M h w := hp
  have hadm : Admissible (M : ℚ) (fullWord h w) := by
    rw [fullWord, admissible_append]
    refine ⟨admissible_concatWord_of_mem_centralHistories hp.mem_centralHistories, ?_⟩
    have := (isSelectedPair_iff.1 hp).2.2.2
    rwa [historyEndpoint_eq_src] at this
  have hsrcW : src (fullWord h w) (M : ℚ) = x := by
    rw [← hsrc, historyEndpoint_eq_src, fullWord, src_append]
  obtain ⟨m, hm, hmpos, hmodd⟩ := hadm.exists_src_eq_pos_odd hpos hodd
  have hxm : x = m := by
    have := hsrcW.symm.trans hm
    exact_mod_cast this
  subst hxm
  exact ⟨hmpos, hmodd⟩

/-- **Counted sources are odd**. If `M` is an `s`-good seed, every
`x ∈ 𝒮_{n,X}(M)` is a positive odd integer. -/
@[collatz_pos_dens "lem_source_odd"]
theorem GoodSeed.pos_odd_of_mem_sources {s M : ℕ} (hM : GoodSeed s M) {x : ℤ}
    (hx : x ∈ sources n X (M : ℚ)) : 0 < x ∧ Odd x :=
  pos_odd_of_mem_sources_of_pos_odd (M := (M : ℤ)) (by exact_mod_cast hM.pos)
    (by exact_mod_cast hM.odd) (by exact_mod_cast hx)

/-- If `M` is an `s`-good seed and `x ∈ 𝒮_{n,X}(M)`, then `x.toNat` is `x` itself and is odd. -/
theorem GoodSeed.odd_toNat_of_mem_sources {s M : ℕ} (hM : GoodSeed s M) {x : ℤ}
    (hx : x ∈ sources n X (M : ℚ)) : ((x.toNat : ℕ) : ℤ) = x ∧ Odd x.toNat := by
  obtain ⟨hpos, hodd⟩ := hM.pos_odd_of_mem_sources hx
  have hx' : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hpos.le
  refine ⟨hx', ?_⟩
  rw [← hx'] at hodd
  exact_mod_cast hodd

end CollatzPosDens
