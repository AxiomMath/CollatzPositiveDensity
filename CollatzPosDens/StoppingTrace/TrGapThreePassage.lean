/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.BlackSet.BkExitWidth
public import CollatzPosDens.CharSum.ChOddDyadicExit
public import CollatzPosDens.CharSum.ChOddDyadicExitStrip
public import CollatzPosDens.CharSum.ChPaidRewardCap
public import CollatzPosDens.CharSum.ChRawFactor
public import CollatzPosDens.StoppingTrace.TrCapFactor
public import CollatzPosDens.StoppingTrace.TrCrossingReward
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrGapOneCells
public import CollatzPosDens.StoppingTrace.TrPassageDeficit
public import CollatzPosDens.Transfer.S02Gamma
public import CollatzPosDens.Transfer.S02Z

/-!
# The passage of length three from a black point of gap three

Let `ξ` be a unit and `v` a black point with `gap(v) = 3`, at the colour scale `ε_*`. Then the
tilted mass of the passage lists of level `3` has a definite deficit:
```
∑_{π ∈ Π_3} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)} ≤ 1 - 37/160.
```

For `c ∈ {4, …, 7}` put `o = c - 3` and `y_c = v + (1, 3 + o) = v + (1, c)`. Since
`gap(v) = 3`, the top edge of the canonical triangle `Δ(v)` lies at height `l_Δ = l(v) + 3`, so
`y_c = (j(v) + 1, l_Δ + o)`. The exit width `f_3 = 1` keeps `y_c` in the strip
`j(y_c) ≤ ⌊n/2⌋`, and the odd dyadic exit lemma writes `ϑ(y_c) = (b + β) / 2^o` with `b` odd
and `|β| ≤ 9 ε_* 2^{-3} < 1/24`. The paid reward cap gives `e^{-z_* R_c(y_c)} ≤ Φ^cap_c(ϑ(y_c))`,
and the bounds on the capped packet factor near the odd dyadic points give
`Φ^cap_c(ϑ(y_c)) < u_c`, where `(u_4, …, u_7) = (9/25, 23/50, 14/25, 4/5)`. On the first raw
crossing event `𝒳_{c,c-3,1}(3)` the white count is at least `R_c(y_c)`, and `γ_* = z_*`, so the
tilt is at most `u_c` there. The deficit bound for passages, with the four triples
`(c, c - 3, 1)`, yields the deficit `∑_c ϖ(c) (1 - u_c) = 37/160`.

## Main results

* `CollatzPosDens.exp_neg_trCount_le_of_mem_trRawThreeWitness_of_trGap_eq_three`: the tilt on a
  first raw crossing event `𝒳_{o+3,o,1}(3)` is at most any `u` bounding the capped packet factor
  `Φ^cap_{o+3}` near the odd dyadic points of level `o`.
* `CollatzPosDens.tsum_trPassage_three_mul_exp_neg_trCount_le`: the deficit bound.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Let `ξ` be a unit, `v ∈ 𝒫` black at the colour scale `ε_*` with `gap(v) = 3`, and
`1 ≤ o ≤ 13`. If `u` satisfies `Φ^cap_{o+3}((m + β) / 2^o) < u` for every odd `m` and every
`|β| ≤ 1/24`, then `e^{-γ_* N^*(v, π; |π|)} ≤ u` for every `π ∈ 𝒳_{o+3,o,1}(3)`. -/
theorem exp_neg_trCount_le_of_mem_trRawThreeWitness_of_trGap_eq_three {n : ℕ}
    {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) v) (hg : trGap n ξ (epsStar : ℝ) v = 3) {o : ℕ}
    (ho₁ : 1 ≤ o) (ho₂ : o ≤ 13) {u : ℝ}
    (hcell : ∀ m : ℤ, Odd m → ∀ β : ℝ, |β| ≤ 1 / 24 →
      trCapFactor ((o : ℤ) + 3) ((m + β) / 2 ^ o) < u)
    {π : List (List ℤ × ℤ)} (hπ : π ∈ trRawThreeWitness 3 ((o : ℤ) + 3) (o : ℤ) 1) :
    Real.exp (-(gammaStar : ℝ) * trCount n ξ v π π.length) ≤ u := by
  obtain ⟨hε₀, hε⟩ := epsStar_mem_bkRange (K := ℝ)
  have hω : bkL v + ((3 : ℕ) : ℤ) = (bkCanonTriangle n ξ (epsStar : ℝ) v hv).l := by
    rw [bkCanonTriangle_l, bkColTop_eq_add_trGap, hg]
    simp
  obtain ⟨b, hbo, β, hβ, hθ⟩ :=
    exists_odd_bkTheta_dyadic_exit hξ hε₀ hε hv hb 3 hω 1 o ho₁
  have hstrip := bkJ_add_le_of_le_bkExitWidth hξ hε₀ hε hv hb hω (r := 1) (by decide)
  set y : ℤ × ℤ := v + (((1 : ℕ) : ℤ), ((3 : ℕ) : ℤ) + (o : ℤ)) with hy
  have hyeq : y = (bkJ v + ((1 : ℕ) : ℤ),
      (bkCanonTriangle n ξ (epsStar : ℝ) v hv).l + (o : ℤ)) := by
    rw [← hω, hy]
    ext <;> simp [bkJ, bkL]; omega
  have hβ' : |β| ≤ 1 / 24 := by
    refine hβ.trans ?_
    rw [epsStar_cast]
    norm_num
  have hcapeq : max (chRawFactor n ξ ((o : ℤ) + 3) y) ((2 : ℝ) ^ (-16 : ℤ)) =
      trCapFactor ((o : ℤ) + 3) ((b + β) / 2 ^ o) := by
    rw [trCapFactor_of_mem (by omega) (by omega), chRawFactor_of_two_le n ξ (by omega), hyeq,
      hθ]
  have hcap := exp_neg_zStar_mul_chPaidReward_le (ξ := ξ) (ε := (epsStar : ℝ))
    (c := (o : ℤ) + 3) (p := y) (by omega) (by omega) (by rw [hyeq]; exact hstrip)
  have hR := chPaidReward_le_trCount_of_mem_trRawThreeWitness ξ v (le_refl 1) hπ
  have hγ : (gammaStar : ℝ) = zStar := by rw [gammaStar_cast, zStar_cast]
  have hz : (0 : ℝ) < zStar := by exact_mod_cast zStar_pos
  calc Real.exp (-(gammaStar : ℝ) * trCount n ξ v π π.length)
      ≤ Real.exp (-(zStar : ℝ) * chPaidReward n ξ (epsStar : ℝ) ((o : ℤ) + 3) y) := by
        rw [hγ, Real.exp_le_exp]
        exact mul_le_mul_of_nonpos_left hR (by linarith)
    _ ≤ max (chRawFactor n ξ ((o : ℤ) + 3) y) ((2 : ℝ) ^ (-16 : ℤ)) := hcap
    _ = trCapFactor ((o : ℤ) + 3) ((b + β) / 2 ^ o) := hcapeq
    _ ≤ u := (hcell b hbo β hβ').le

/-- **The passage from a black point of gap three.** Let `ξ` be a unit and `v ∈ 𝒫` black at the
colour scale `ε_*` with `gap(v) = 3`. Then
`∑_{π ∈ Π_3} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)} ≤ 1 - 37/160`. -/
@[collatz_pos_dens "lem_tr_gap_three_passage"]
theorem tsum_trPassage_three_mul_exp_neg_trCount_le {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v)
    (hg : trGap n ξ (epsStar : ℝ) v = 3) :
    ∑' π : trPassage 3,
        trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) ≤
      1 - 37 / 160 := by
  set I : Finset (ℤ × ℤ × ℕ) := {(4, 1, 1), (5, 2, 1), (6, 3, 1), (7, 4, 1)}
  set u : ℤ × ℤ × ℕ → ℝ := fun t ↦
    if t.1 = 4 then 9 / 25 else if t.1 = 5 then 23 / 50 else if t.1 = 6 then 14 / 25 else 4 / 5
  have hI : ∀ t ∈ I, 1 ≤ t.2.1 ∧ t.2.1 ≤ t.1 ∧ 1 ≤ t.2.2 := by
    intro t ht
    simp only [I, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> simp
  have hcell := chPacketFn_gap_one_cells
  have key : ∀ (o : ℕ) (w : ℝ),
      (((o : ℤ) + 3, o, 1 / 24, w) ∈ ([(4, 1, 1 / 24, 9 / 25), (5, 2, 1 / 24, 23 / 50),
        (6, 3, 1 / 24, 14 / 25), (7, 4, 1 / 24, 4 / 5), (4, 1, 1 / 12, 21 / 50)] :
          List (ℤ × ℕ × ℝ × ℝ))) → 1 ≤ o → o ≤ 13 →
      ∀ π ∈ trRawThreeWitness 3 ((o : ℤ) + 3) (o : ℤ) 1,
        Real.exp (-(gammaStar : ℝ) * trCount n ξ v π π.length) ≤ w := fun o w hmem h₁ h₂ π hπ ↦
    exp_neg_trCount_le_of_mem_trRawThreeWitness_of_trGap_eq_three hξ hv hb hg h₁ h₂
      (hcell _ hmem) hπ
  have hb' : ∀ t ∈ I, ∀ π ∈ trRawThreeWitness 3 t.1 t.2.1 t.2.2,
      Real.exp (-(gammaStar : ℝ) * trCount n ξ v π π.length) ≤ u t := by
    intro t ht π hπ
    simp only [I, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact key 1 (u (4, 1, 1)) (by norm_num [u]) le_rfl (by norm_num) π
        (by norm_num at hπ ⊢; exact hπ)
    · exact key 2 (u (5, 2, 1)) (by norm_num [u]) (by norm_num) (by norm_num) π
        (by norm_num at hπ ⊢; exact hπ)
    · exact key 3 (u (6, 3, 1)) (by norm_num [u]) (by norm_num) (by norm_num) π
        (by norm_num at hπ ⊢; exact hπ)
    · exact key 4 (u (7, 4, 1)) (by norm_num [u]) (by norm_num) (by norm_num) π
        (by norm_num at hπ ⊢; exact hπ)
  refine (tsum_trPassage_mul_exp_neg_trCount_le_one_sub ξ v 3 I u hI hb').trans_eq ?_
  norm_num [I, u, Finset.sum_insert, rawMass_zero, varpi_of_two_le]

end CollatzPosDens
