/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.InformationTheory.Coding.PrefixFree
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Word
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.Seed.S05ConcatWord

/-!
# Cuts are determined by the word

Let `n ∈ ℕ`, let `w_j, w'_j ∈ 𝒞(b_j, K_j)` for `0 ≤ j < n`, where `𝒞(b, K)` is the central family
`CollatzPosDens.centralFamily b K`, and let `w', w''` be words with
`w_0 ⋯ w_{n-1} w' = w'_0 ⋯ w'_{n-1} w''` (the products of blocks being empty if `n = 0`). Then
`(w_0, …, w_{n-1}, w') = (w'_0, …, w'_{n-1}, w'')`. More generally, a concatenation of words drawn
from a sequence of prefix-free families of lists factors uniquely.

## Main results

* `CollatzPosDens.historyDetermined_of_isPrefixFree`: unique factorisation over an arbitrary
  sequence of prefix-free families of lists.
* `CollatzPosDens.isPrefixFree_centralFamily`: the central family `𝒞(b, K)` is prefix-free.
* `CollatzPosDens.historyDetermined`: the statement for the central families `𝒞(b_j, K_j)`,
  `0 ≤ j < n`.

## Implementation notes

A tuple `(w_0, …, w_{n-1})` is a map `Fin n → Word`, its entry `k` being the word `w_k`, and its
concatenation is `CollatzPosDens.concatWord`; for `n = 0` the index type is empty. The levels
`b_j` and caps `K_j` are arbitrary sequences of natural numbers. The conclusion
`(w_0, …, w_{n-1}, w') = (w'_0, …, w'_{n-1}, w'')` is stated as the conjunction
`h = h' ∧ w' = w''`.

## References

* [Mazur, *Collatz positive density*], §16.3.
-/
@[expose] public section

namespace CollatzPosDens

/-- Unique factorisation over a sequence of prefix-free families: if `F j` is prefix-free for
every `j`, `h j, h' j ∈ F j` for `j < n`, and `h₀ ⋯ h_{n-1} x = h'₀ ⋯ h'_{n-1} y`, then
`h = h'` and `x = y`. -/
theorem historyDetermined_of_isPrefixFree {α : Type*} {F : ℕ → Set (List α)}
    (hF : ∀ j, InformationTheory.IsPrefixFree (F j)) :
    ∀ {n : ℕ} {h h' : Fin n → List α} {x y : List α},
      (∀ j : Fin n, h j ∈ F j) → (∀ j : Fin n, h' j ∈ F j) →
      (List.ofFn h).flatten ++ x = (List.ofFn h').flatten ++ y → h = h' ∧ x = y
  | 0, h, h', x, y, _, _, heq => by
    simpa [Subsingleton.elim h h'] using heq
  | n + 1, h, h', x, y, hh, hh', heq => by
    simp only [List.ofFn_succ, List.flatten_cons, List.append_assoc] at heq
    have h0 : h 0 = h' 0 := by
      rcases List.prefix_or_prefix_of_prefix (List.prefix_append (h 0) _)
          (heq ▸ List.prefix_append (h' 0) _) with hp | hp
      · exact hF 0 _ (hh 0) _ (hh' 0) hp
      · exact (hF 0 _ (hh' 0) _ (hh 0) hp).symm
    rw [h0, List.append_cancel_left_eq] at heq
    obtain ⟨htail, rfl⟩ := historyDetermined_of_isPrefixFree (F := fun j => F (j + 1))
      (fun j => hF (j + 1)) (h := fun i => h i.succ) (h' := fun i => h' i.succ)
      (fun j => hh j.succ) (fun j => hh' j.succ) heq
    exact ⟨funext fun i => Fin.cases h0 (congrFun htail) i, rfl⟩

/-- The central family `centralFamily b K` is prefix-free. -/
theorem isPrefixFree_centralFamily (b K : ℕ) :
    InformationTheory.IsPrefixFree (centralFamily b K) := fun _ hw _ hw' hp =>
  isPrefixFree_firstCrossing b (rb b) K _ (centralFamily_subset_firstCrossing b K hw) _
    (centralFamily_subset_firstCrossing b K hw') hp

/-- Cuts are determined by the word: if `w_j, w'_j ∈ 𝒞(b_j, K_j)` for `0 ≤ j < n` and
`w_0 ⋯ w_{n-1} w' = w'_0 ⋯ w'_{n-1} w''`, then `(w_0, …, w_{n-1}, w') = (w'_0, …, w'_{n-1}, w'')`.
-/
@[collatz_pos_dens "lem_history_determined"]
theorem historyDetermined {n : ℕ} (b K : ℕ → ℕ) {h h' : Fin n → Word} {w' w'' : Word}
    (hh : ∀ k : Fin n, h k ∈ centralFamily (b k) (K k))
    (hh' : ∀ k : Fin n, h' k ∈ centralFamily (b k) (K k))
    (heq : concatWord h ++ w' = concatWord h' ++ w'') : h = h' ∧ w' = w'' :=
  historyDetermined_of_isPrefixFree (F := fun k => centralFamily (b k) (K k))
    (fun k => isPrefixFree_centralFamily (b k) (K k)) hh hh' heq

end CollatzPosDens
