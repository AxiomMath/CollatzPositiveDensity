/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.Lb
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Maps.Word

/-!
# The first-crossing family `𝒲(b, u, K)`

For a level `b`, an integer offset `u` and an overshoot bound `K ≥ 0`, the first-crossing
family `𝒲(b, u, K)` is the set of words `w ∈ 𝕎` of length `s` with `ℓ_b < s ≤ h_b` whose
prefix valuation sums stay strictly below the barrier, `A(w_{≤ i}) < H_{b,u}(i)` for
`ℓ_b ≤ i < s`, and which cross it at time `s` with overshoot at most `K`:
`H_{b,u}(s) ≤ A(w) ≤ H_{b,u}(s) + K`.

## Main definitions

* `CollatzPosDens.firstCrossing`: the family `𝒲(b, u, K)`, as a set of words.

## Main results

* `CollatzPosDens.mem_firstCrossing`: the defining membership condition.
* `CollatzPosDens.lb_lt_length_of_mem_firstCrossing`,
  `CollatzPosDens.length_le_hb_of_mem_firstCrossing`: the length window `ℓ_b < |w| ≤ h_b`.
* `CollatzPosDens.valSum_take_lt_of_mem_firstCrossing`: the prefixes stay below the barrier.
* `CollatzPosDens.barrier_le_valSum_of_mem_firstCrossing`,
  `CollatzPosDens.valSum_le_barrier_add_of_mem_firstCrossing`: the crossing with overshoot
  at most `K`.

## Implementation notes

The level `b` and the overshoot bound `K` are arbitrary natural numbers; in particular the
case `b = 0` is allowed. The valuation sum `A` is natural-number valued and is compared with
the integer barrier after casting to `ℤ`. The prefix `w_{≤ i}` is `w.take i`. The barrier is
`H_{b,u}`, whose shift is the radius `r_b`.

## References

* [Mazur, *Collatz positive density*], §15.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The first-crossing family `𝒲(b, u, K)`: words `w` of length `s` with `ℓ_b < s ≤ h_b`,
`A(w_{≤ i}) < H_{b,u}(i)` for every `ℓ_b ≤ i < s`, and `H_{b,u}(s) ≤ A(w) ≤ H_{b,u}(s) + K`. -/
@[collatz_pos_dens "def_first_crossing"]
def firstCrossing (b : ℕ) (u : ℤ) (K : ℕ) : Set Word :=
  {w | lb b < w.length ∧ w.length ≤ hb b ∧
    (∀ i, lb b ≤ i → i < w.length → (Word.valSum (w.take i) : ℤ) < barrier b u i) ∧
    barrier b u w.length ≤ (w.valSum : ℤ) ∧ (w.valSum : ℤ) ≤ barrier b u w.length + K}

/-- Membership in the first-crossing family `𝒲(b, u, K)`. -/
theorem mem_firstCrossing {b : ℕ} {u : ℤ} {K : ℕ} {w : Word} :
    w ∈ firstCrossing b u K ↔ lb b < w.length ∧ w.length ≤ hb b ∧
      (∀ i, lb b ≤ i → i < w.length → (Word.valSum (w.take i) : ℤ) < barrier b u i) ∧
      barrier b u w.length ≤ (w.valSum : ℤ) ∧
      (w.valSum : ℤ) ≤ barrier b u w.length + K :=
  Iff.rfl

variable {b : ℕ} {u : ℤ} {K : ℕ} {w : Word}

/-- A word of `𝒲(b, u, K)` is longer than `ℓ_b`. -/
theorem lb_lt_length_of_mem_firstCrossing (hw : w ∈ firstCrossing b u K) :
    lb b < w.length :=
  hw.1

/-- A word of `𝒲(b, u, K)` has length at most `h_b`. -/
theorem length_le_hb_of_mem_firstCrossing (hw : w ∈ firstCrossing b u K) :
    w.length ≤ hb b :=
  hw.2.1

/-- A word of `𝒲(b, u, K)` is nonempty. -/
theorem ne_nil_of_mem_firstCrossing (hw : w ∈ firstCrossing b u K) : w ≠ [] := by
  rintro rfl
  exact Nat.not_lt_zero _ hw.1

/-- The prefixes `w_{≤ i}`, `ℓ_b ≤ i < |w|`, of a word of `𝒲(b, u, K)` lie below the
barrier. -/
theorem valSum_take_lt_of_mem_firstCrossing (hw : w ∈ firstCrossing b u K) {i : ℕ}
    (hi : lb b ≤ i) (his : i < w.length) : (Word.valSum (w.take i) : ℤ) < barrier b u i :=
  hw.2.2.1 i hi his

/-- A word of `𝒲(b, u, K)` reaches the barrier: `H_{b,u}(|w|) ≤ A(w)`. -/
theorem barrier_le_valSum_of_mem_firstCrossing (hw : w ∈ firstCrossing b u K) :
    barrier b u w.length ≤ (w.valSum : ℤ) :=
  hw.2.2.2.1

/-- A word of `𝒲(b, u, K)` overshoots the barrier by at most `K`. -/
theorem valSum_le_barrier_add_of_mem_firstCrossing (hw : w ∈ firstCrossing b u K) :
    (w.valSum : ℤ) ≤ barrier b u w.length + K :=
  hw.2.2.2.2

/-- The first-crossing families increase with the overshoot bound `K`. -/
theorem firstCrossing_mono {K K' : ℕ} (h : K ≤ K') :
    firstCrossing b u K ⊆ firstCrossing b u K' := fun _ hw =>
  ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.trans (by gcongr)⟩

end CollatzPosDens
