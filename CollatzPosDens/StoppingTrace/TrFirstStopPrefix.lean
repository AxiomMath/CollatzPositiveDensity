/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrFirstStopSet
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrSublist
public import CollatzPosDens.StoppingTrace.TrTrace
public import CollatzPosDens.StoppingTrace.TrNoLateHit

/-!
# First stops are read off the prefix

Let `o ∈ 𝒫`, `N ∈ ℕ` with `j(o) + N > J`, where `J = ⌊n/2⌋`, let `β ∈ 𝔅^N` be live and let
`x = (x_t(o, β))_{t ∈ ℕ}` be its path from `o`. The path of the prefix `β_{[1,q]}`, `q ≤ N`, agrees
with that of `β` up to time `q`, and a black point `x_q` forces `j(o) + q ≤ J < j(o) + N` (no black
point beyond the strip). Hence the first stopping time is read off the prefix: `ν(x) ≥ 1` and
`τ_1(x) = q` hold together iff `q ≤ N` and `β_{[1,q]} ∈ 𝒰(o)`.

## Main results

* `CollatzPosDens.trStopTime_one_eq_some_iff_trSublist_mem_trFirstStopSet`: the
  characterisation of the first stopping time by first-stop lists.
* `CollatzPosDens.trPath_trSublist_one_of_le`: the path of the prefix `β_{[1,q]}` agrees with
  the path of `β` up to time `q`.

## Implementation notes

The condition `o ∈ 𝒫` (`1 ≤ j(o)`) is an explicit hypothesis; it is used to get `q < J` in the
reverse direction. The list `β ∈ 𝔅^N` is a `List (List ℤ × ℤ)` with `N = β.length` and every
closing letter in `{4, 5}`, and `ε` is an arbitrary colour scale.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.2.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}

/-- Up to time `q ≤ N`, the path of the prefix `β_{[1,q]}` agrees with the path of `β`. -/
theorem trPath_trSublist_one_of_le (o : ℤ × ℤ) {β : List (List ℤ × ℤ)} {q t : ℕ}
    (hq : q ≤ β.length) (ht : t ≤ q) : trPath o (trSublist β 1 q) t = trPath o β t := by
  have hlen : (β.take q).length = q := by simp [hq]
  rw [trSublist_one]
  conv_rhs => rw [← List.take_append_drop q β]
  rw [trPath_append_of_le o _ _ (by omega)]

/-- **First stops are read off the prefix.** Let `o ∈ 𝒫`, let `β ∈ 𝔅^N` be live with
`j(o) + N > ⌊n/2⌋`, and let `x = (x_t(o, β))_t`. Then `ν(x) ≥ 1` and `τ_1(x) = q` hold together
iff `q ≤ N` and `β_{[1,q]} ∈ 𝒰(o)`. -/
@[collatz_pos_dens "lem_tr_first_stop_prefix"]
theorem trStopTime_one_eq_some_iff_trSublist_mem_trFirstStopSet {o : ℤ × ℤ}
    (ho : o ∈ bkPoints) (β : List (List ℤ × ℤ)) (hβ : ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ))
    (hlive : TrLive β) (hN : ((n / 2 : ℕ) : ℤ) < bkJ o + β.length) (q : ℕ) :
    (1 ≤ trNu n ξ ε (trPath o β) ∧ trStopTime n ξ ε (trPath o β) 1 = some q) ↔
      q ≤ β.length ∧ trSublist β 1 q ∈ trFirstStopSet n ξ ε o := by
  have ho1 : 1 ≤ bkJ o := ho
  have hlenq : ∀ {q : ℕ}, q ≤ β.length → (trSublist β 1 q).length = q :=
    fun hq => by simp [hq]
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨-, hhit, hmin⟩ := trStopTime_one_eq_some_iff.1 h
    rw [isTrHit_iff] at hhit
    have hlate := bkJ_add_le_of_bkJ_trPath_le o β hN hhit.bkJ_le
    have hqN : q ≤ β.length := by omega
    refine ⟨hqN, ?_⟩
    rw [mem_trFirstStopSet, hlenq hqN]
    refine ⟨fun b hb => hβ b (mem_of_mem_trSublist hb), hlive.sublist (trSublist_sublist _ _ _),
      ?_, fun t htq => ?_⟩
    · rwa [trPath_trSublist_one_of_le o hqN le_rfl]
    · rw [trPath_trSublist_one_of_le o hqN htq.le]
      exact hmin t htq
  · rintro ⟨hqN, hu⟩
    rw [mem_trFirstStopSet, hlenq hqN] at hu
    obtain ⟨-, -, hhit, hnot⟩ := hu
    rw [trPath_trSublist_one_of_le o hqN le_rfl] at hhit
    have hlate := bkJ_add_le_of_bkJ_trPath_le o β hN hhit.bkJ_le
    have h1 : trStopTime n ξ ε (trPath o β) 1 = some q := by
      refine trStopTime_one_eq_some_iff.2 ⟨by omega, hhit, fun s hs => ?_⟩
      rw [isTrHit_iff, ← trPath_trSublist_one_of_le o hqN hs.le]
      exact hnot s hs
    exact ⟨(isSome_trStopTime_iff.1 (by simp [h1])).2, h1⟩

end CollatzPosDens
