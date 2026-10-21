/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.S04Clog
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.DeficitWindow
public import CollatzPosDens.FirstCrossing.FcLateBound
public import CollatzPosDens.FirstCrossing.FcLateWindow
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.Width

/-!
# The window deficit of the central families

For every scale index `j ∈ ℕ`, the deficit of the central family at the scale `b_j` with cap
`K_j` is bounded by the window deficit bound:
$$1-\mathbf p(\mathcal C(b_j,K_j))\le\mathsf d^{\mathrm w}_j.$$

Write `u = b_j` and `y = y^w_j`. Since `u ≥ 16544`, one has `⌊u/8⌋ ≥ 2068`, `lg u ≥ 15`,
`⌈√(32 u lg u)⌉ ≥ 1000` and `⌊3u/5⌋ - 1 ≥ 9925`, so `1000 ≤ y ≤ wd(u)` and `8 y ≤ u`. The
words of `𝒲(u, r_u, K_j)` with length in `[u - y, u + y]` then form a subfamily of
`𝒞(u, K_j)`, and the deficit bound for a central window applies with half-width `y`.

## Main results

* `CollatzPosDens.thousand_le_min_wd_scale_div_eight`: `1000 ≤ y^w_j` for every `j`.
* `CollatzPosDens.one_sub_geomMass_centralFamily_le_dW`: `1 - 𝐩(𝒞(b_j, K_j)) ≤ d^w_j`.

## Implementation notes

The geometric mass is `ℝ≥0∞`-valued while `d^w_j` is real; the inequality is stated with the
real bound embedded by `ENNReal.ofReal`. Since `d^w_j > 0` this loses nothing.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open scoped ENNReal
open Real

namespace CollatzPosDens

/-- For every `j`, the central window satisfies `1000 ≤ y^w_j`, in its natural-number form
`min (wd b_j) (b_j / 8)`. -/
theorem thousand_le_min_wd_scale_div_eight (j : ℕ) :
    1000 ≤ min (wd (scale j)) (scale j / 8) := by
  have hu := sixteen544_le_scale j
  set u := scale j
  refine le_min (le_wd_iff.2 ⟨?_, by omega⟩) (by omega)
  have hlg : 15 ≤ lg u := by
    by_contra h
    have := lg_le_iff_le_two_pow.1 (show lg u ≤ 14 by omega)
    norm_num at this
    omega
  have hu' : (16544 : ℝ) ≤ u := by exact_mod_cast hu
  have hlg' : (15 : ℝ) ≤ lg u := by exact_mod_cast hlg
  have h1 : (1000 : ℝ) ≤ √(32 * (u : ℝ) * (lg u : ℝ)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  exact_mod_cast h1.trans (Nat.le_ceil _)

/-- **Window deficit of the central families**: for every `j ∈ ℕ`, `1 - 𝐩(𝒞(b_j, K_j)) ≤ d^w_j`. -/
@[collatz_pos_dens "lem_fc_late_window_deficit"]
theorem one_sub_geomMass_centralFamily_le_dW (j : ℕ) :
    1 - geomMass (centralFamily (scale j) (cap j)) ≤ ENNReal.ofReal (dW j) := by
  have hy := thousand_le_min_wd_scale_div_eight j
  set u := scale j with hu_def
  set y := min (wd u) (u / 8) with hy_def
  have hyw : y ≤ wd u := min_le_left _ _
  have hy8 : 8 * y ≤ u := by have : y ≤ u / 8 := min_le_right _ _; omega
  have hsub : {v ∈ firstCrossing u (rb u) (cap j) | u - y ≤ v.length ∧ v.length ≤ u + y} ⊆
      centralFamily u (cap j) := by
    rintro v ⟨hv, h1, h2⟩
    exact mem_centralFamily.2 ⟨hv, by omega, by omega⟩
  refine (tsub_le_tsub_left (geomMass_mono hsub) 1).trans
    ((one_sub_geomMass_deficitWindow_le hy hy8).trans (le_of_eq ?_))
  rw [dW_eq, ← hu_def, ← hy_def, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

end CollatzPosDens
