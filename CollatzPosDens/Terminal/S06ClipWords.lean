/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Rat.Cast.Order
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Terminal.S06ClipWindow
public import CollatzPosDens.Terminal.S06ClipCap

/-!
# Clipped words

For integers `m ≥ 1`, `n ≥ 2` and a real `B > 0`, the *clipped words* are the words of length
`m` whose valuation sum lies in the clipping degree window `CollatzPosDens.clipWindow m n B` and
whose offset is at most the clipping offset cap `CollatzPosDens.clipCap m n B`:
$$\mathcal V^{\mathrm{clp}}_{m,n,B} = \{u \in ℤ_{≥1}^m : A(u) \in I^{\mathrm{clp}}_{m,n,B}
  \text{ and } \mathrm{off}(u) ≤ L^{\mathrm{clp}}_{m,n,B}\}.$$

## Main definitions

* `CollatzPosDens.clipWords m n B`: the set `𝒱^clp_{m,n,B}` of clipped words.

## Main results

* `CollatzPosDens.mem_clipWords`: membership is the defining condition.
* `CollatzPosDens.length_of_mem_clipWords`: clipped words have length `m`.
* `CollatzPosDens.le_valSum_of_mem_clipWords`: `m ≤ A(u)` for a clipped word `u`.

## Implementation notes

A tuple `u ∈ ℤ_{≥1}^m` is a word (`List ℕ+`) of length `m`. The valuation sum `A(u) ∈ ℕ` is
cast to `ℤ` to be compared with the window, and the offset `off(u) ∈ ℚ` is cast to `ℝ` to be
compared with the cap.

## References

* [Mazur, *Collatz positive density*], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The set `𝒱^clp_{m,n,B}` of clipped words: the words `u` of length `m` whose valuation sum
lies in `clipWindow m n B` and whose offset is at most `clipCap m n B`. -/
@[collatz_pos_dens "def_s06_clip_words"]
def clipWords (m n : ℕ) (B : ℝ) : Set Word :=
  {u | u.length = m ∧ (u.valSum : ℤ) ∈ clipWindow m n B ∧ (off u : ℝ) ≤ clipCap m n B}

/-- Membership in the set of clipped words. -/
@[simp]
theorem mem_clipWords {m n : ℕ} {B : ℝ} {u : Word} :
    u ∈ clipWords m n B ↔
      u.length = m ∧ (u.valSum : ℤ) ∈ clipWindow m n B ∧ (off u : ℝ) ≤ clipCap m n B :=
  Iff.rfl

/-- A clipped word has length `m`. -/
theorem length_of_mem_clipWords {m n : ℕ} {B : ℝ} {u : Word} (h : u ∈ clipWords m n B) :
    u.length = m :=
  h.1

/-- A clipped word has valuation sum at least `m`. -/
theorem le_valSum_of_mem_clipWords {m n : ℕ} {B : ℝ} {u : Word} (h : u ∈ clipWords m n B) :
    m ≤ u.valSum := by
  exact_mod_cast le_of_mem_clipWindow h.2.1

/-- A clipped word has valuation sum at least the clipping degree floor. -/
theorem clipFloor_le_valSum_of_mem_clipWords {m n : ℕ} {B : ℝ} {u : Word}
    (h : u ∈ clipWords m n B) : clipFloor m B ≤ u.valSum :=
  clipFloor_le_of_mem_clipWindow h.2.1

/-- A clipped word has offset at most the clipping offset cap. -/
theorem off_le_clipCap_of_mem_clipWords {m n : ℕ} {B : ℝ} {u : Word}
    (h : u ∈ clipWords m n B) : (off u : ℝ) ≤ clipCap m n B :=
  h.2.2

end CollatzPosDens
