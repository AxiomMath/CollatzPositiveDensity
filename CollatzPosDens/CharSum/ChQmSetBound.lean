/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChDist
public import CollatzPosDens.CharSum.ChQRange

/-!
# An upper bound for the set defining `Q_m`

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For a real `A ≥ 0` and an integer
`m ≥ 0`, every element `d_J(p)^A Q(p)` of the set whose supremum is `Q_m = CollatzPosDens.chQm`
(with `p ∈ 𝒫` and `j(p) ≥ ⌊n/2⌋ ∸ m`) is at most `max(m, 1)^A`. Indeed `⌊n/2⌋ ∸ j(p) ≤ m`
gives `1 ≤ d_J(p) ≤ max(m, 1)`, the power `x ↦ x^A` is monotone on `[0, ∞)` for `A ≥ 0`, and
`0 ≤ Q(p) ≤ 1`.

## Main results

* `CollatzPosDens.chQm_set_le`: each element of the set defining `Q_m` is at most
  `max(m, 1)^A`.
* `CollatzPosDens.chQm_set_bddAbove`: that set is bounded above.

## Implementation notes

The power is the real power `Real.rpow`, matching `CollatzPosDens.chQm`. The threshold `ε`
is arbitrary, since the range bound `0 ≤ Q(p) ≤ 1` holds for every `ε`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.5.
-/

@[expose] public section

namespace CollatzPosDens

/-- **An upper bound for the set defining `Q_m`.** For real `A ≥ 0` and `m ≥ 0`, every element
`d_J(p)^A Q(p)` of the set defining `Q_m` is at most `max(m, 1)^A`. -/
@[collatz_pos_dens "lem_ch_Qm_set_bound"]
theorem chQm_set_le (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ} (hA : 0 ≤ A) (m : ℕ) {x : ℝ}
    (hx : x ∈ {x | ∃ p ∈ bkPoints, ((n / 2 - m : ℕ) : ℤ) ≤ bkJ p ∧
      x = (chDist n p : ℝ) ^ A * chQ n ξ ε p}) :
    x ≤ ((max m 1 : ℕ) : ℝ) ^ A := by
  obtain ⟨p, -, hj, rfl⟩ := hx
  have hd : chDist n p ≤ max m 1 := chDist_le (by omega)
  exact (mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) A) (chQ_range n ξ ε p).2).trans
    (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hd) hA)

/-- The set of weighted values defining `Q_m` is bounded above, by `max(m, 1)^A`. -/
theorem chQm_set_bddAbove (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ} (hA : 0 ≤ A) (m : ℕ) :
    BddAbove {x | ∃ p ∈ bkPoints, ((n / 2 - m : ℕ) : ℤ) ≤ bkJ p ∧
      x = (chDist n p : ℝ) ^ A * chQ n ξ ε p} :=
  ⟨_, fun _ hx => chQm_set_le n ξ ε hA m hx⟩

end CollatzPosDens
