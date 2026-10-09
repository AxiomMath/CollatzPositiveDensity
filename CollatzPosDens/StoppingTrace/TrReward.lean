/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.List.GetD

/-!
# The reward of a block

Fix a level `n` and a residue `ξ ∈ G_n`, and call a point *white* when it satisfies
`CollatzPosDens.IsBkWhite n ξ ε_*`, with `ε_* = CollatzPosDens.epsStar`. For a point `x ∈ 𝒫`
and a block `β = (c, e)` with `c = (c₁, …, c_m)`, the *reward* of `β` at `x` is
```
rw(x, β) = [x + bpt(β) is white]
  + κ_* · #{i ∈ {1, …, m} : cᵢ = 3 and x + (i, c₁ + ⋯ + cᵢ) is white}.
```
The first term rewards the block for ending at a white point; the second rewards, with the
smaller weight `κ_* = 4/25`, every intermediate letter `3` of the block that lands on a white
point.

## Main definitions

* `CollatzPosDens.trReward n ξ x β`: the reward `rw(x, β) ∈ ℝ`.

## Main results

* `CollatzPosDens.trReward_nonneg`: rewards are nonnegative.
* `CollatzPosDens.indicator_le_trReward`: `[x + bpt(β) is white] ≤ rw(x, β)`.
* `CollatzPosDens.trReward_nil`: a block with no nonclosing letters has reward
  `[x + bpt(β) is white]`.

## Implementation notes

As for `CollatzPosDens.chBlockPoint`, blocks are modelled as pairs `(c, e) : List ℤ × ℤ` and
points of `𝒫` as elements of `ℤ × ℤ`; the reward is defined for all of them, and the
mathematical definition is recovered by restricting to `x ∈ 𝒫` and `e ∈ {4, 5}`. The letter
`cᵢ` (for `1 ≤ i ≤ m`) is `c.getD (i - 1) 0` and the partial sum `c₁ + ⋯ + cᵢ` is
`(c.take i).sum`. The reward is real-valued, `κ_*` being cast from `ℚ`. The hypothesis that `ξ`
is a unit plays no role in the definition and is omitted.

## References

* [Mazur, *Collatz positive density*], §9.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The reward of a block `β = (c, e)` with `c = (c₁, …, c_m)` at a point `x`: the indicator
that `x + bpt(β)` is white, plus `κ_*` times the number of `i ∈ [1, m]` with `cᵢ = 3` and
`x + (i, c₁ + ⋯ + cᵢ)` white, where white means `IsBkWhite n ξ ε_*`. -/
@[collatz_pos_dens "def_tr_reward"]
noncomputable def trReward (n : ℕ) (ξ : ResidueGroup n) (x : ℤ × ℤ) (β : List ℤ × ℤ) : ℝ :=
  (if IsBkWhite n ξ (epsStar : ℝ) (x + chBlockPoint β) then 1 else 0) +
    (kappaStar : ℝ) *
      (((Finset.Icc 1 β.1.length).filter fun i =>
        β.1.getD (i - 1) 0 = 3 ∧
          IsBkWhite n ξ (epsStar : ℝ) (x + ((i : ℤ), (β.1.take i).sum))).card : ℝ)

variable {n : ℕ} {ξ : ResidueGroup n}

/-- The reward `rw(x, β)` unfolds to the endpoint indicator plus `κ_*` times the number of
intermediate letters `3` landing on a white point. -/
lemma trReward_def (x : ℤ × ℤ) (β : List ℤ × ℤ) :
    trReward n ξ x β =
      (if IsBkWhite n ξ (epsStar : ℝ) (x + chBlockPoint β) then 1 else 0) +
        (kappaStar : ℝ) *
          (((Finset.Icc 1 β.1.length).filter fun i =>
            β.1.getD (i - 1) 0 = 3 ∧
              IsBkWhite n ξ (epsStar : ℝ) (x + ((i : ℤ), (β.1.take i).sum))).card : ℝ) :=
  rfl

/-- The inner reward of a word `c = (c₁, …, c_m)` at `x`: `κ_*` times the number of
`i ∈ [1, m]` with `cᵢ = 3` and `x + (i, c₁ + ⋯ + cᵢ)` white. It is the part of the reward of a
block `(c, e)` that does not depend on the closing letter `e`. -/
noncomputable def trInnerReward (n : ℕ) (ξ : ResidueGroup n) (x : ℤ × ℤ) (c : List ℤ) : ℝ :=
  (kappaStar : ℝ) *
    (((Finset.Icc 1 c.length).filter fun i =>
      c.getD (i - 1) 0 = 3 ∧ IsBkWhite n ξ (epsStar : ℝ) (x + ((i : ℤ), (c.take i).sum))).card : ℝ)

/-- The reward of a block `(c, e)` is the endpoint indicator plus the inner reward of `c`. -/
lemma trReward_eq_add_trInnerReward (x : ℤ × ℤ) (c : List ℤ) (e : ℤ) :
    trReward n ξ x (c, e) =
      (if IsBkWhite n ξ (epsStar : ℝ) (x + chBlockPoint (c, e)) then 1 else 0) +
        trInnerReward n ξ x c :=
  rfl

/-- The inner reward is nonnegative. -/
lemma trInnerReward_nonneg (x : ℤ × ℤ) (c : List ℤ) : 0 ≤ trInnerReward n ξ x c :=
  mul_nonneg (by exact_mod_cast kappaStar_nonneg) (Nat.cast_nonneg _)

open Finset in
/-- The inner reward of the word `(v₀, …, v_{m-1})` is at most `κ_*` times its number of
letters `3`. -/
lemma trInnerReward_ofFn_le (x : ℤ × ℤ) {m : ℕ} (v : Fin m → ℤ) :
    trInnerReward n ξ x (List.ofFn v) ≤ (kappaStar : ℝ) * ((#{i | v i = 3} : ℕ) : ℝ) := by
  rw [trInnerReward]
  gcongr
  · exact_mod_cast kappaStar_nonneg
  calc _ ≤ ((Finset.univ.filter fun i => v i = 3).image fun i : Fin m => (i : ℕ) + 1).card := by
        refine Finset.card_le_card fun i hi => ?_
        simp only [Finset.mem_filter, Finset.mem_Icc, List.length_ofFn] at hi
        obtain ⟨⟨h1, h2⟩, h3, -⟩ := hi
        refine Finset.mem_image.2 ⟨⟨i - 1, by omega⟩, ?_, by simp; omega⟩
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn] at h3
        simpa using h3
    _ ≤ _ := Finset.card_image_le

open Finset in
/-- `(1163/1250)^{t(c)} ≤ e^{-γ_* ι(c)}` for the word `c = (v₀, …, v_{m-1})` with `t(c)` letters
`3`, using `ι(c) ≤ κ_* t(c)` and `1163/1250 ≤ e^{-γ_* κ_*}`. -/
lemma pow_le_exp_neg_trInnerReward (x : ℤ × ℤ) {m : ℕ} (v : Fin m → ℤ) :
    (1163 / 1250 : ℝ) ^ #{i | v i = 3} ≤
      Real.exp (-(gammaStar : ℝ) * trInnerReward n ξ x (List.ofFn v)) := by
  have hκ : (kappaStar : ℝ) = 4 / 25 := by rw [kappaStar_def]; norm_num
  calc (1163 / 1250 : ℝ) ^ #{i | v i = 3} ≤
        Real.exp (-(87 / 200 * (4 / 25))) ^ #{i | v i = 3} := by
        gcongr
        linarith [Real.add_one_le_exp (-(87 / 200 * (4 / 25) : ℝ))]
    _ = Real.exp (-(gammaStar : ℝ) * ((kappaStar : ℝ) * ((#{i | v i = 3} : ℕ) : ℝ))) := by
        rw [← Real.exp_nat_mul, gammaStar_cast, hκ]
        ring_nf
    _ ≤ _ := by
        refine Real.exp_le_exp.2 ?_
        nlinarith [trInnerReward_ofFn_le (n := n) (ξ := ξ) x v,
          (by exact_mod_cast gammaStar_pos : (0 : ℝ) < gammaStar)]

/-- The second term of the reward is nonnegative. -/
lemma trReward_sub_indicator_nonneg (x : ℤ × ℤ) (β : List ℤ × ℤ) :
    0 ≤ trReward n ξ x β -
      (if IsBkWhite n ξ (epsStar : ℝ) (x + chBlockPoint β) then 1 else 0) := by
  obtain ⟨c, e⟩ := β
  rw [trReward_eq_add_trInnerReward, add_sub_cancel_left]
  exact trInnerReward_nonneg x c

/-- A block's reward is at least the indicator that it ends at a white point. -/
lemma indicator_le_trReward (x : ℤ × ℤ) (β : List ℤ × ℤ) :
    (if IsBkWhite n ξ (epsStar : ℝ) (x + chBlockPoint β) then (1 : ℝ) else 0) ≤
      trReward n ξ x β :=
  sub_nonneg.1 (trReward_sub_indicator_nonneg x β)

/-- A block ending at a white point has reward at least `1`. -/
lemma one_le_trReward (x : ℤ × ℤ) (β : List ℤ × ℤ)
    (h : IsBkWhite n ξ (epsStar : ℝ) (x + chBlockPoint β)) : 1 ≤ trReward n ξ x β := by
  simpa only [h, ↓reduceIte] using indicator_le_trReward (n := n) (ξ := ξ) x β

/-- Rewards are nonnegative. -/
lemma trReward_nonneg (x : ℤ × ℤ) (β : List ℤ × ℤ) : 0 ≤ trReward n ξ x β :=
  le_trans (by split_ifs <;> norm_num) (indicator_le_trReward x β)

/-- A block with no nonclosing letters is rewarded only for its endpoint. -/
@[simp]
lemma trReward_nil (x : ℤ × ℤ) (e : ℤ) :
    trReward n ξ x ([], e) =
      if IsBkWhite n ξ (epsStar : ℝ) (x + (1, e)) then 1 else 0 := by
  simp [trReward_def]

end CollatzPosDens
