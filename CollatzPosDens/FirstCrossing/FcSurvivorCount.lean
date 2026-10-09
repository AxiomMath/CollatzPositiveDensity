/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.Lb
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.Maps.Valsum
public import Mathlib.Data.Set.Card

/-!
# Surviving prefix counts `c_{b,i}(s)`

For a level `b`, a length `i` and an integer `s`, the surviving prefix count `c_{b,i}(s)` is the
number of words `x ∈ ℤ_{≥1}^i` with valuation sum `A(x) = s` (`Word.valSum`) whose prefixes stay
strictly below the barrier: `A(x_{≤ j}) < H_{b,r_b}(j)` for every `ℓ_b ≤ j ≤ i`, where
`H_{b,r_b}` is `barrier b (rb b)` and `ℓ_b` is `lb b`. These are the words that have not yet
crossed the barrier `H_{b,r_b}` by time `i`.

## Main definitions

* `CollatzPosDens.fcSurvivorSet`: the set of surviving words of length `i` and sum `s`.
* `CollatzPosDens.fcSurvivorCount`: its cardinality `c_{b,i}(s)`.

## Main results

* `CollatzPosDens.mem_fcSurvivorSet`: the defining membership condition.
* `CollatzPosDens.fcSurvivorSet_finite`: the set of surviving words is finite, so
  `c_{b,i}(s)` is a genuine count.
* `CollatzPosDens.fcSurvivorCount_of_neg`: `c_{b,i}(s) = 0` for `s < 0`.

## Implementation notes

The count is defined for arbitrary natural numbers `b` and `i`, not only for `b ≥ 1` and
`i ≥ ℓ_b`; the definition makes sense for all of them. A word of `ℤ_{≥1}^i` is a
word (a list of positive integers) of length `i`, and the prefix `x_{≤ j}` is `x.take j`. The
natural-number valuation sum is compared with the integer `s` and with the integer barrier after
casting to `ℤ`. The count is the `Set.ncard` of the set of surviving words, which is finite
(`fcSurvivorSet_finite`): every letter of a word of sum `s` is at most `s`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The set of words `x ∈ ℤ_{≥1}^i` with `A(x) = s` and `A(x_{≤ j}) < H_{b,r_b}(j)` for every
`ℓ_b ≤ j ≤ i`. -/
@[collatz_pos_dens "def_fc_survivor_count"]
def fcSurvivorSet (b i : ℕ) (s : ℤ) : Set Word :=
  {x | x.length = i ∧ (x.valSum : ℤ) = s ∧
    ∀ j, lb b ≤ j → j ≤ i → (Word.valSum (x.take j) : ℤ) < barrier b (rb b) j}

/-- The surviving prefix count `c_{b,i}(s)`: the number of words `x ∈ ℤ_{≥1}^i` with
`A(x) = s` and `A(x_{≤ j}) < H_{b,r_b}(j)` for every `ℓ_b ≤ j ≤ i`. -/
@[collatz_pos_dens "def_fc_survivor_count"]
noncomputable def fcSurvivorCount (b i : ℕ) (s : ℤ) : ℕ :=
  (fcSurvivorSet b i s).ncard

/-- Unfolding lemma for `fcSurvivorCount`. -/
theorem fcSurvivorCount_def (b i : ℕ) (s : ℤ) :
    fcSurvivorCount b i s = (fcSurvivorSet b i s).ncard := rfl

/-- Membership in the set of surviving words. -/
theorem mem_fcSurvivorSet {b i : ℕ} {s : ℤ} {x : Word} :
    x ∈ fcSurvivorSet b i s ↔ x.length = i ∧ (x.valSum : ℤ) = s ∧
      ∀ j, lb b ≤ j → j ≤ i → (Word.valSum (x.take j) : ℤ) < barrier b (rb b) j :=
  Iff.rfl

/-- The set of surviving words is finite. -/
theorem fcSurvivorSet_finite (b i : ℕ) (s : ℤ) : (fcSurvivorSet b i s).Finite :=
  (Word.finite_setOf_valSum_le s.toNat).subset fun _ hx => by have := hx.2.1; simp; omega

/-- For a negative total `s`, no word has valuation sum `s`, so `c_{b,i}(s) = 0`. -/
theorem fcSurvivorCount_of_neg {b i : ℕ} {s : ℤ} (hs : s < 0) : fcSurvivorCount b i s = 0 := by
  rw [fcSurvivorCount_def, Set.ncard_eq_zero (fcSurvivorSet_finite b i s)]
  ext x
  simp only [mem_fcSurvivorSet, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ h
  omega

end CollatzPosDens
