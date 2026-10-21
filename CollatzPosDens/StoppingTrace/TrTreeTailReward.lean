/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPaidRewardNonneg
public import CollatzPosDens.StoppingTrace.TrCountRaw
public import CollatzPosDens.StoppingTrace.TrEntryWord
public import CollatzPosDens.StoppingTrace.TrExitReward
public import CollatzPosDens.Transfer.S02Gamma
public import CollatzPosDens.Transfer.S02Z

/-!
# The paid factor of a long first letter

Fix a level `n`, a unit `ξ ∈ G_n` and the colour scale `ε_*`. Let `v ∈ 𝒫` be black with gap
`ω = gap(v)`, let `3 ≤ c ≤ 16` with `c > ω`, and let `u` be a list of blocks whose raw word starts
with the letter `c`. Then
```
exp(-γ_* N^*(v, u; |u|)) ≤ 1 - δ^{pk}_{c,c-ω}.
```
Indeed, writing the weighted white count as a sum of paid rewards over the raw letters
(`CollatzPosDens.trCount_eq_sum_chRaw`) and dropping every summand but the first, which is
legitimate since paid rewards are nonnegative, gives `N^*(v, u; |u|) ≥ R_c(v + (1, c))`, as
`σ_1(u) = c`. Write `v + (1, c) = v + (1, ω + (c - ω))` with `1 ≤ c - ω`. Since the exit width
satisfies `1 ≤ f_ω`, the reward at an exit point with `s = ω`, `r = 1` and `o = c - ω` gives
`e^{-z_* R_c(v + (1, c))} ≤ 1 - δ^{pk}_{c,c-ω}`, and `γ_* = z_* ≥ 0`.

## Main results

* `CollatzPosDens.chPaidReward_le_trCount_of_head?_eq`: if the raw word of `u` starts with `c`,
  then `R_c(o + (1, c)) ≤ N^*(o, u; |u|)`.
* `CollatzPosDens.exp_neg_gammaStar_mul_trCount_le_one_sub_trPacketDeficit`:
  `exp(-γ_* N^*(v, u; |u|)) ≤ 1 - δ^{pk}_{c,c-ω}`.

## Implementation notes

The gap is an integer, which is nonnegative; the statement takes a natural number `ω` together
with the equation `gap(v) = ω`, so that `c - ω` is the truncated difference of natural numbers,
which equals the integer difference because `ω < c`. No hypothesis that `u ∈ 𝓔(v)` is an entry
list is imposed: the estimate only reads the first letter of the raw word of `u`, so the
statement holds for every list of blocks `u` whose raw word `raw_M(u)`, `M = j(Bp_{|u|}(u))`, has
first letter `c`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- If the raw word of `u` starts with the letter `c`, then the weighted white count of `u` from
`o` is at least the paid reward of its first letter: `R_c(o + (1, c)) ≤ N^*(o, u; |u|)`. -/
theorem chPaidReward_le_trCount_of_head?_eq {n : ℕ} {ξ : ResidueGroup n} (o : ℤ × ℤ)
    {u : List (List ℤ × ℤ)} {c : ℤ}
    (hu : (chRaw (chBlockPath u u.length).1.toNat u).head? = some c) :
    chPaidReward n ξ (epsStar : ℝ) c (o + (1, c)) ≤ trCount n ξ o u u.length := by
  rw [trCount_eq_sum_chRaw]
  set M := (chBlockPath u u.length).1.toNat
  have hM : 1 ≤ M := by
    rw [chRaw_toNat_chBlockPath_fst] at hu
    simp only [M]
    have : (u.flatMap fun b => b.1 ++ [b.2]) ≠ [] := by
      intro h; rw [h] at hu; simp at hu
    rw [toNat_chBlockPath_fst]
    exact List.length_pos_iff.mpr this
  have hmem : 1 ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨le_rfl, hM⟩
  refine le_of_eq_of_le ?_ (Finset.single_le_sum
    (f := fun i => chPaidReward n ξ (epsStar : ℝ) ((chRaw M u).getD (i - 1) 0)
      (o + ((i : ℤ), trRawSum u i)))
    (fun i _ => zero_le_chPaidReward _ _ _ _ _) hmem)
  obtain ⟨a, l, hl⟩ : ∃ a l, chRaw M u = a :: l := by
    cases h : chRaw M u with
    | nil => rw [h] at hu; simp at hu
    | cons a l => exact ⟨a, l, rfl⟩
  rw [hl, List.head?_cons, Option.some.injEq] at hu
  subst hu
  have hσ : trRawSum u 1 = a := by rw [trRawSum_def, hl]; simp
  simp [hl, hσ]

/-- **The paid factor of a long first letter.** Let `ξ` be a unit, `v ∈ 𝒫` black at the colour
scale `ε_*` with gap `gap(v) = ω`, `3 ≤ c ≤ 16` with `ω < c`, and `u` a list of blocks whose raw
word has first letter `c`. Then `exp(-γ_* N^*(v, u; |u|)) ≤ 1 - δ^{pk}_{c,c-ω}`. -/
@[collatz_pos_dens "lem_tr_tree_tail_reward"]
theorem exp_neg_gammaStar_mul_trCount_le_one_sub_trPacketDeficit {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v)
    {ω : ℕ} (hgap : trGap n ξ (epsStar : ℝ) v = ω) {c : ℕ} (hc₁ : 3 ≤ c) (hc₂ : c ≤ 16)
    (hωc : ω < c) {u : List (List ℤ × ℤ)}
    (hu : (chRaw (chBlockPath u u.length).1.toNat u).head? = some (c : ℤ)) :
    Real.exp (-(gammaStar : ℝ) * trCount n ξ v u u.length) ≤
      1 - (trPacketDeficit c (c - ω) : ℝ) := by
  have hr : 1 ≤ bkExitWidth (trGap n ξ (epsStar : ℝ) v).toNat := one_le_bkExitWidth _
  have hexit := exp_neg_zStar_mul_chPaidReward_le_one_sub_trPacketDeficit hξ hv hb hr hc₁ hc₂
    (by omega : 1 ≤ c - ω)
  have hc : trGap n ξ (epsStar : ℝ) v + ((c - ω : ℕ) : ℤ) = c := by rw [hgap]; omega
  rw [hc] at hexit
  have hγ : (gammaStar : ℝ) = zStar := by rw [gammaStar_cast, zStar_cast]
  have hz : (0 : ℝ) ≤ zStar := by exact_mod_cast zStar_nonneg
  have hle := chPaidReward_le_trCount_of_head?_eq (n := n) (ξ := ξ) v hu
  refine le_trans (Real.exp_le_exp.mpr ?_) hexit
  rw [hγ]
  push_cast at hle ⊢
  nlinarith

end CollatzPosDens
