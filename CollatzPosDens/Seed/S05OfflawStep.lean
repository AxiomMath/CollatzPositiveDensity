/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05OfflawFloor
public import CollatzPosDens.Seed.S05OfflawIndex

/-!
# The step function of an offset-law table

A tuple `g = (g_0, …, g_6198) ∈ ℕ^6199` determines a step function `Ĝ_g : ℝ → ℝ`: it vanishes
for `y < 0`, equals `2^{-62} g_{ι(y)}` on `[0, ξ_6198]`, where `ξ_k` is the offset grid
`offlawGrid k` and `ι` is its grid index `offlawIndex`, and equals the tail floor
`𝖦₀(y) = offlawFloor y` for `y > ξ_6198`. When `g` is nondecreasing and
`2^{-62} g_6198 ≤ 𝖦₀(ξ_6198)`, the step function is nondecreasing on all of `ℝ`.

## Main definitions

* `CollatzPosDens.offlawStep g y`: the step function `Ĝ_g(y)`.

## Main results

* `CollatzPosDens.offlawStep_of_neg`, `CollatzPosDens.offlawStep_of_mem_Icc`,
  `CollatzPosDens.offlawStep_of_gt`: the three branches of the definition.
* `CollatzPosDens.offlawStep_offlawGrid`: `Ĝ_g(ξ_k) = 2^{-62} g_k` for `k ≤ 6198`.
* `CollatzPosDens.offlawStep_nonneg`, `CollatzPosDens.offlawStep_le_one`: `0 ≤ Ĝ_g ≤ 1` when
  every `g_k ≤ 2^62`.
* `CollatzPosDens.offlawStep_monotone`: `Ĝ_g` is nondecreasing when `g` is nondecreasing and
  `2^{-62} g_6198 ≤ 𝖦₀(ξ_6198)`.

## Implementation notes

The tuple is a function `Fin 6199 → ℕ`; the grid index `ι(y) ≤ 6198` is read as an element of
`Fin 6199`. The value `2^{-62} g_k` is written `(g_k : ℝ) / 2^62`.

## References

* [Mazur, *Collatz positive density*], §16.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The grid index `ι(y)` as an element of `Fin 6199`. -/
noncomputable def offlawIndexFin (y : ℝ) : Fin 6199 :=
  ⟨offlawIndex y, Nat.lt_succ_of_le (offlawIndex_le y)⟩

/-- The value of `offlawIndexFin y` is the grid index `offlawIndex y`. -/
@[simp] theorem offlawIndexFin_val (y : ℝ) : (offlawIndexFin y : ℕ) = offlawIndex y := rfl

/-- **Step function of a table** `Ĝ_g : ℝ → ℝ`: `0` for `y < 0`, `2^{-62} g_{ι(y)}` for
`0 ≤ y ≤ ξ_6198`, and `𝖦₀(y)` for `y > ξ_6198`. -/
@[collatz_pos_dens "def_s05_offlaw_step"]
noncomputable def offlawStep (g : Fin 6199 → ℕ) (y : ℝ) : ℝ :=
  if y < 0 then 0
  else if y ≤ ((offlawGrid 6198 : ℚ) : ℝ) then (g (offlawIndexFin y) : ℝ) / 2 ^ 62
  else offlawFloor y

variable (g : Fin 6199 → ℕ)

/-- For `y < 0`, `Ĝ_g(y) = 0`. -/
theorem offlawStep_of_neg {y : ℝ} (hy : y < 0) : offlawStep g y = 0 := by
  simp [offlawStep, hy]

/-- For `0 ≤ y ≤ ξ_6198`, `Ĝ_g(y) = 2^{-62} g_{ι(y)}`. -/
theorem offlawStep_of_mem_Icc {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ ((offlawGrid 6198 : ℚ) : ℝ)) :
    offlawStep g y = (g (offlawIndexFin y) : ℝ) / 2 ^ 62 := by
  simp [offlawStep, not_lt.mpr hy0, hy]

/-- For `y > ξ_6198`, `Ĝ_g(y) = 𝖦₀(y)`. -/
theorem offlawStep_of_gt {y : ℝ} (hy : ((offlawGrid 6198 : ℚ) : ℝ) < y) :
    offlawStep g y = offlawFloor y := by
  have h0 : (0 : ℝ) ≤ ((offlawGrid 6198 : ℚ) : ℝ) := by exact_mod_cast offlawGrid_nonneg 6198
  simp [offlawStep, not_lt.mpr (h0.trans hy.le), not_le.mpr hy]

/-- At a grid point, `Ĝ_g(ξ_k) = 2^{-62} g_k`. -/
theorem offlawStep_offlawGrid (k : Fin 6199) :
    offlawStep g ((offlawGrid k : ℚ) : ℝ) = (g k : ℝ) / 2 ^ 62 := by
  have hk : (k : ℕ) ≤ 6198 := Nat.le_of_lt_succ k.isLt
  rw [offlawStep_of_mem_Icc g (by exact_mod_cast offlawGrid_nonneg k)
    (by exact_mod_cast offlawGrid_monotone hk)]
  congr 3
  exact Fin.ext (offlawIndex_offlawGrid hk)

/-- The step function is nonnegative: `0 ≤ Ĝ_g(y)`. -/
theorem offlawStep_nonneg (y : ℝ) : 0 ≤ offlawStep g y := by
  unfold offlawStep
  split_ifs
  · exact le_rfl
  · positivity
  · exact offlawFloor_nonneg y

/-- If every entry satisfies `g_k ≤ 2^62`, then `Ĝ_g ≤ 1`. -/
theorem offlawStep_le_one (hg : ∀ k, g k ≤ 2 ^ 62) (y : ℝ) : offlawStep g y ≤ 1 := by
  unfold offlawStep
  split_ifs with h0 h1
  · norm_num
  · rw [div_le_one (by positivity)]
    exact_mod_cast hg _
  · exact offlawFloor_le_one (not_lt.mp h0)

/-- If `g` is nondecreasing and `2^{-62} g_6198 ≤ 𝖦₀(ξ_6198)`, then `Ĝ_g` is nondecreasing. -/
theorem offlawStep_monotone (hg : Monotone g)
    (hlast : (g (Fin.last 6198) : ℝ) / 2 ^ 62 ≤ offlawFloor ((offlawGrid 6198 : ℚ) : ℝ)) :
    Monotone (offlawStep g) := by
  have hξ0 : (0 : ℝ) ≤ ((offlawGrid 6198 : ℚ) : ℝ) := by exact_mod_cast offlawGrid_nonneg 6198
  intro y y' hyy'
  rcases lt_or_ge y 0 with hy | hy
  · rw [offlawStep_of_neg g hy]
    exact offlawStep_nonneg g y'
  rcases le_or_gt y' ((offlawGrid 6198 : ℚ) : ℝ) with hy' | hy'
  · rw [offlawStep_of_mem_Icc g hy (hyy'.trans hy'), offlawStep_of_mem_Icc g (hy.trans hyy') hy']
    gcongr
    exact_mod_cast hg (show offlawIndexFin y ≤ offlawIndexFin y' from offlawIndex_mono hyy')
  rw [offlawStep_of_gt g hy']
  rcases le_or_gt y ((offlawGrid 6198 : ℚ) : ℝ) with hyξ | hyξ
  · rw [offlawStep_of_mem_Icc g hy hyξ]
    calc (g (offlawIndexFin y) : ℝ) / 2 ^ 62 ≤ (g (Fin.last 6198) : ℝ) / 2 ^ 62 := by
          gcongr
          exact_mod_cast hg (Fin.le_last _)
      _ ≤ offlawFloor ((offlawGrid 6198 : ℚ) : ℝ) := hlast
      _ ≤ offlawFloor y' := offlawFloor_monotoneOn (Set.mem_Ici.mpr hξ0)
          (Set.mem_Ici.mpr (hξ0.trans hy'.le)) hy'.le
  · rw [offlawStep_of_gt g hyξ]
    exact offlawFloor_monotoneOn (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr (hy.trans hyy')) hyy'

end CollatzPosDens
