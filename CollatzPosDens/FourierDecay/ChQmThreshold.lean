/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChQmLePow

/-!
# A threshold bound on `Q_m`

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. Let `A ≥ 0` be real and `D ≥ 2` an
integer, and suppose that `Q_m ≤ Q_{m-1}` for every integer `m` with `D ≤ m ≤ ⌊n/2⌋`. Then
`Q_m ≤ (D - 1)^A` for every `m ≤ ⌊n/2⌋`. The proof is by induction on `m`: for `m ≤ D - 1` the
bound `Q_m ≤ max(m, 1)^A ≤ (D - 1)^A` applies, and for `m ≥ D` the monotonicity hypothesis
reduces `m` to `m - 1`.

## Main results

* `CollatzPosDens.chQm_le_threshold_pow`: `Q_m ≤ (D - 1)^A` for all `m ≤ ⌊n/2⌋`.

## Implementation notes

The power is the real power `Real.rpow`, matching `CollatzPosDens.chQm`, and `D - 1` is the
real number `(D : ℝ) - 1`. The threshold `ε` is arbitrary.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Threshold bound on `Q_m`.** If `D ≥ 2` and `Q_m ≤ Q_{m-1}` for every `m` with
`D ≤ m ≤ ⌊n/2⌋`, then `Q_m ≤ (D - 1)^A` for every `m ≤ ⌊n/2⌋`. -/
@[collatz_pos_dens "lem_ch_Qm_threshold"]
theorem chQm_le_threshold_pow (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ} (hA : 0 ≤ A)
    {D : ℕ} (hD : 2 ≤ D)
    (hmono : ∀ m, D ≤ m → m ≤ n / 2 → chQm n ξ ε A m ≤ chQm n ξ ε A (m - 1)) :
    ∀ m, m ≤ n / 2 → chQm n ξ ε A m ≤ ((D : ℝ) - 1) ^ A := by
  intro m
  induction m with
  | zero =>
    intro _
    refine (chQm_le_pow n ξ ε hA 0).trans ?_
    have h : ((max 0 1 : ℕ) : ℝ) ≤ (D : ℝ) - 1 := by
      rw [le_sub_iff_add_le]; exact_mod_cast (show max 0 1 + 1 ≤ D by omega)
    gcongr
  | succ k ih =>
    intro hk
    by_cases hkD : k + 1 < D
    · refine (chQm_le_pow n ξ ε hA (k + 1)).trans ?_
      have h : ((max (k + 1) 1 : ℕ) : ℝ) ≤ (D : ℝ) - 1 := by
        rw [le_sub_iff_add_le]; exact_mod_cast (show max (k + 1) 1 + 1 ≤ D by omega)
      gcongr
    · exact (hmono (k + 1) (by omega) hk).trans (ih (by omega))

end CollatzPosDens
