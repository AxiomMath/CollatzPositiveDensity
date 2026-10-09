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
public import CollatzPosDens.Seed.ConcatWord

/-!
# Cuts are determined by the word

Let `w_j, w'_j ∈ 𝒞(b_j, K_j)` for `j < n`, and let `w', w''` be words with
`w₀ ⋯ w_{n-1} w' = w'₀ ⋯ w'_{n-1} w''`. Then `w_j = w'_j` for every `j < n` and `w' = w''`.
This holds more generally for any sequence of prefix-free families, and `𝒞(b, K)` is
prefix-free since it is contained in the prefix-free family `𝒲(b, r_b, K)`.

## Main results

* `CollatzPosDens.historyDetermined_of_isPrefixFree`: the statement for an arbitrary
  sequence of prefix-free families of lists.
* `CollatzPosDens.isPrefixFree_centralFamily`: the central family `𝒞(b, K)` is prefix-free.
* `CollatzPosDens.historyDetermined`: the statement for the central families `𝒞(b_j, K_j)`.

## Implementation notes

A tuple `(w₀, …, w_{n-1})` is a function `Fin n → Word` and its concatenation is
`CollatzPosDens.concatWord`. The levels `b_j` and caps `K_j` are arbitrary sequences of
natural numbers. The conclusion `(w₀, …, w_{n-1}, w') = (w'₀, …, w'_{n-1}, w'')` is stated as
the conjunction `h = h' ∧ w' = w''`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
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
    refine ⟨funext fun i => ?_, rfl⟩
    refine Fin.cases h0 (fun i => ?_) i
    exact congrFun htail i

/-- The central family `𝒞(b, K)` is prefix-free, being contained in the prefix-free
family `𝒲(b, r_b, K)`. -/
theorem isPrefixFree_centralFamily (b K : ℕ) :
    InformationTheory.IsPrefixFree (centralFamily b K) :=
  (isPrefixFree_firstCrossing b (rb b) K).anti (centralFamily_subset_firstCrossing b K)

/-- Cuts are determined by the word: if `w_j, w'_j ∈ 𝒞(b_j, K_j)` for `j < n` and
`w₀ ⋯ w_{n-1} w' = w'₀ ⋯ w'_{n-1} w''`, then
`(w₀, …, w_{n-1}, w') = (w'₀, …, w'_{n-1}, w'')`. -/
@[collatz_pos_dens "lem_history_determined"]
theorem historyDetermined {n : ℕ} (b K : ℕ → ℕ) {h h' : Fin n → Word} {w' w'' : Word}
    (hh : ∀ j : Fin n, h j ∈ centralFamily (b j) (K j))
    (hh' : ∀ j : Fin n, h' j ∈ centralFamily (b j) (K j))
    (heq : concatWord h ++ w' = concatWord h' ++ w'') : h = h' ∧ w' = w'' :=
  historyDetermined_of_isPrefixFree (F := fun j => centralFamily (b j) (K j))
    (fun j => isPrefixFree_centralFamily (b j) (K j)) hh hh' heq

end CollatzPosDens
