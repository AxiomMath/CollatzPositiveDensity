/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Maps.InverseOrbitOdd
public import CollatzPosDens.OrdinaryTime.S07FullWord
public import CollatzPosDens.OrdinaryTime.S07SelectedPair
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.Terminal.UnweightedMass

/-!
# Counted sources are odd

Let `t₁` be a positive odd integer, `n ∈ ℕ` and `X` real. Every source `x ∈ sources n X t₁` is a
positive odd integer. Indeed, `x` is the source `src w R` of the second component of a selected
pair `(h, w)` (`IsSelectedPair n X t₁ h w`), where `R` is the endpoint of the history `h`. The
concatenated central blocks `concatWord h` are admissible from `t₁` and `w` is admissible from `R`,
so `fullWord h w` is admissible from `t₁`, and its source from `t₁` is `x`. The last term of the
inverse orbit of a positive odd integer along an admissible word is a positive odd integer.

This applies in particular to a `t`-good seed `t₁` (`GoodSeed t t₁`), which is odd and positive.

## Main results

* `CollatzPosDens.pos_odd_of_mem_sources_of_pos_odd`: the statement for a positive odd starting
  point `t₁`.
* `CollatzPosDens.GoodSeed.pos_odd_of_mem_sources`: every source `x ∈ sources n X t₁` of a
  `t`-good seed `t₁` is a positive odd integer.
* `CollatzPosDens.GoodSeed.odd_toNat_of_mem_sources`: the natural number `x.toNat` counted for
  such a source is `x` itself and is odd.

## Implementation notes

The source set consists of integers, while the Collatz map acts on `ℕ`; the corollary
`CollatzPosDens.GoodSeed.odd_toNat_of_mem_sources` records the statement for `x.toNat`. None of
`t ≥ 1`, `3 ∤ t` or `X > 0` is needed: only the oddness and positivity of the seed enter.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {X : ℝ}

/-- If `t₁` is a positive odd integer, every source `x ∈ 𝒮_{n,X}(t₁)` is a positive odd
integer. -/
theorem pos_odd_of_mem_sources_of_pos_odd {t₁ : ℤ} (hpos : 0 < t₁) (hodd : Odd t₁) {x : ℤ}
    (hx : x ∈ sources n X (t₁ : ℚ)) : 0 < x ∧ Odd x := by
  obtain ⟨⟨h, w⟩, hp, hsrc⟩ := mem_sources.1 hx
  have hp : IsSelectedPair n X t₁ h w := hp
  have hadm : Admissible (t₁ : ℚ) (fullWord h w) := by
    rw [fullWord, admissible_append]
    refine ⟨admissible_concatWord_of_mem_centralHistories hp.mem_centralHistories, ?_⟩
    have := (isSelectedPair_iff.1 hp).2.2.2
    rwa [historyEndpoint_eq_src] at this
  have hsrcW : src (fullWord h w) (t₁ : ℚ) = x := by
    rw [← hsrc, historyEndpoint_eq_src, fullWord, src_append]
  obtain ⟨m, hm, hmpos, hmodd⟩ := hadm.exists_src_eq_pos_odd hpos hodd
  have hxm : x = m := by
    have := hsrcW.symm.trans hm
    exact_mod_cast this
  subst hxm
  exact ⟨hmpos, hmodd⟩

/-- If `t₁` is a `t`-good seed, every `x ∈ 𝒮_{n,X}(t₁)` is a positive odd integer. -/
@[collatz_pos_dens "lem_source_odd"]
theorem GoodSeed.pos_odd_of_mem_sources {t t₁ : ℕ} (ht₁ : GoodSeed t t₁) {x : ℤ}
    (hx : x ∈ sources n X (t₁ : ℚ)) : 0 < x ∧ Odd x :=
  pos_odd_of_mem_sources_of_pos_odd (t₁ := (t₁ : ℤ)) (by exact_mod_cast ht₁.pos)
    (by exact_mod_cast ht₁.odd) (by exact_mod_cast hx)

/-- If `t₁` is a `t`-good seed and `x ∈ 𝒮_{n,X}(t₁)`, then `x.toNat` is `x` itself and is odd. -/
theorem GoodSeed.odd_toNat_of_mem_sources {t t₁ : ℕ} (ht₁ : GoodSeed t t₁) {x : ℤ}
    (hx : x ∈ sources n X (t₁ : ℚ)) : ((x.toNat : ℕ) : ℤ) = x ∧ Odd x.toNat := by
  obtain ⟨hpos, hodd⟩ := ht₁.pos_odd_of_mem_sources hx
  have hx' : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hpos.le
  refine ⟨hx', ?_⟩
  rw [← hx'] at hodd
  exact_mod_cast hodd

end CollatzPosDens
