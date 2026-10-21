/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.SelEnd
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Seed.S05OffsetCap

/-!
# The selector

For `n ∈ ℕ` and a tuple `τ = (w₀, …, w_{n-1})` of words (the empty tuple if `n = 0`), the
*selector* `Sel_n(τ)` is the proposition that
$$\mathrm{off}(w_0) \le \tfrac34 \ \text{ if } n \ge 1, \qquad
  \mathrm{off}(w_i) \le M_{\mathrm{sel}} \ \text{ for every } 0 < i < \min(n, j_e),$$
where `off` is the offset of a word, `M_sel = 2^600` the offset cap and `j_e = 29` the
generation `selEnd`. It restricts the first `29` words of a tuple; from generation `j_e` on it
imposes no further condition.

## Main definitions

* `CollatzPosDens.selector n τ`: the proposition `Sel_n(τ)`.

## Main results

* `CollatzPosDens.selector_iff`: the selector unfolded into its two conditions.
* `CollatzPosDens.selector_zero`: the selector holds for the empty tuple.
* `CollatzPosDens.selector.restrict`: `Sel_n(τ)` implies `Sel_j` of the restriction of `τ` to
  its first `j` entries, for `j ≤ n`.
* `CollatzPosDens.selector_restrict_iff`: for `j_e ≤ j ≤ n`, `Sel_j` of the restriction is
  equivalent to `Sel_n(τ)`.

## Implementation notes

A tuple `(w₀, …, w_{n-1})` is a map `τ : Fin n → Word`. The condition "if `n ≥ 1`" is a
dependent implication `∀ h : 0 < n, …`, whose proof is used to index the entry `w₀`. The offset
is rational, and the cap `M_sel ∈ ℕ` is compared with it through its cast to `ℚ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The selector `Sel_n(τ)` of a tuple `τ = (w₀, …, w_{n-1})`: `off(w₀) ≤ 3/4` if `n ≥ 1`, and
`off(w_i) ≤ M_sel` for every `0 < i < min(n, j_e)`. -/
@[collatz_pos_dens "def_s05_selector"]
def selector (n : ℕ) (τ : Fin n → Word) : Prop :=
  (∀ h : 0 < n, off (τ ⟨0, h⟩) ≤ 3 / 4) ∧
    ∀ (i : ℕ) (_ : 0 < i) (h' : i < min n selEnd),
      off (τ ⟨i, lt_of_lt_of_le h' (min_le_left _ _)⟩) ≤ offsetCap

/-- The selector as its two conditions. -/
theorem selector_iff {n : ℕ} {τ : Fin n → Word} :
    selector n τ ↔ (∀ h : 0 < n, off (τ ⟨0, h⟩) ≤ 3 / 4) ∧
      ∀ (i : ℕ) (_ : 0 < i) (h' : i < min n selEnd),
        off (τ ⟨i, lt_of_lt_of_le h' (min_le_left _ _)⟩) ≤ offsetCap :=
  Iff.rfl

/-- The empty tuple satisfies the selector. -/
theorem selector_zero (τ : Fin 0 → Word) : selector 0 τ :=
  ⟨fun h => absurd h (lt_irrefl 0), fun _ _ h' => absurd h' (by omega)⟩

/-- Under the selector, `off(w₀) ≤ 3/4` when `n ≥ 1`. -/
theorem selector.off_le_three_quarters {n : ℕ} {τ : Fin n → Word}
    (hτ : selector n τ) (h : 0 < n) : off (τ ⟨0, h⟩) ≤ 3 / 4 :=
  hτ.1 h

/-- Under the selector, `off(w_i) ≤ M_sel` for `0 < i < min(n, j_e)`. -/
theorem selector.off_le_offsetCap {n : ℕ} {τ : Fin n → Word}
    (hτ : selector n τ) {i : ℕ} (h : 0 < i) (h' : i < min n selEnd) :
    off (τ ⟨i, lt_of_lt_of_le h' (min_le_left _ _)⟩) ≤ offsetCap :=
  hτ.2 i h h'

/-- The selector passes to restrictions: if `j ≤ n` and `Sel_n(w₀, …, w_{n-1})`, then
`Sel_j(w₀, …, w_{j-1})`. -/
theorem selector.restrict {n j : ℕ} {τ : Fin n → Word} (hτ : selector n τ)
    (hj : j ≤ n) : selector j (fun k => τ (Fin.castLE hj k)) :=
  ⟨fun h => hτ.1 (by omega), fun i h h' => hτ.2 i h (by omega)⟩

/-- From generation `j_e` on the selector imposes no new condition: for `j_e ≤ j ≤ n`,
`Sel_j(w₀, …, w_{j-1})` holds if and only if `Sel_n(w₀, …, w_{n-1})` does. -/
theorem selector_restrict_iff {n j : ℕ} {τ : Fin n → Word} (hj : selEnd ≤ j)
    (hjn : j ≤ n) : selector j (fun k => τ (Fin.castLE hjn k)) ↔ selector n τ :=
  ⟨fun hτ => ⟨fun _ => hτ.1 (by rw [selEnd_eq] at hj; omega), fun i h h' => hτ.2 i h (by omega)⟩,
    fun hτ => hτ.restrict hjn⟩

end CollatzPosDens
