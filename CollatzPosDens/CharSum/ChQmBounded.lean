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
public import CollatzPosDens.CharSum.ChQBeyond
public import CollatzPosDens.CharSum.ChQmSetBound

/-!
# Lower bounds for `Q_m`

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`, and write `J = ⌊n/2⌋`. For a real
exponent `A ≥ 0` and an integer `m ≥ 0`, the weighted supremum
`Q_m = sup {d_J(p)^A Q(p) : p ∈ 𝒫, j(p) ≥ J ∸ m}` satisfies `1 ≤ Q_m`. The point
`p = (J + 1, 0)` lies in range, has `d_J(p) = 1` and, being beyond the cut-off, `Q(p) = 1`; so
`1` belongs to the defining set, which is bounded above by `max(m, 1)^A`.

## Main results

* `CollatzPosDens.one_le_chQm`: `1 ≤ Q_m` for `A ≥ 0`.
* `CollatzPosDens.chQm_nonneg`: `0 ≤ Q_m`, for every real `A`.

## Implementation notes

The nonnegativity `0 ≤ Q_m` needs no hypothesis on `A`: every element of the defining set is
nonnegative, and the real supremum `sSup` of a set of nonnegative reals is nonnegative whether or
not the set is bounded above. The lower bound `1 ≤ Q_m` uses `A ≥ 0` through the upper bound
`max(m, 1)^A` of the defining set, without which `sSup` could be the junk value `0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **`Q_m` is at least `1`.** For real `A ≥ 0` and every `m ≥ 0`, `1 ≤ Q_m`. -/
@[collatz_pos_dens "lem_ch_Qm_bounded"]
theorem one_le_chQm (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ} (hA : 0 ≤ A) (m : ℕ) :
    1 ≤ chQm n ξ ε A m := by
  have hj : ((n / 2 : ℕ) : ℤ) < bkJ (((n / 2 : ℕ) : ℤ) + 1, 0) := by simp [bkJ]
  have hd : chDist n (((n / 2 : ℕ) : ℤ) + 1, 0) = 1 := by simp [chDist, bkJ]
  have h := le_chQm (chQm_set_bddAbove n ξ ε hA m) (p := (((n / 2 : ℕ) : ℤ) + 1, 0))
    (by simp only [mem_bkPoints, bkJ]; omega) (by simp only [bkJ]; omega)
  rwa [hd, chQ_eq_one_of_lt_bkJ n ξ ε hj, Nat.cast_one, Real.one_rpow, one_mul] at h

/-- **Nonnegativity of `Q_m`.** For every real `A` and every `m ≥ 0`, `0 ≤ Q_m`. -/
theorem chQm_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (A : ℝ) (m : ℕ) :
    0 ≤ chQm n ξ ε A m :=
  Real.sSup_nonneg fun _ ⟨p, _, _, hx⟩ => hx ▸
    mul_nonneg (Real.rpow_nonneg (mod_cast (chDist_pos n p).le) A) (chQ_range n ξ ε p).1

end CollatzPosDens
