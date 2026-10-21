/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3FactorReward
public import CollatzPosDens.Case3.C3HIterate
public import CollatzPosDens.Case3.C3PaidLaw
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.CharSum.ChInternalRange
public import CollatzPosDens.CharSum.ChQRange
public import CollatzPosDens.StoppingTrace.TrAtoms
public import CollatzPosDens.StoppingTrace.TrConcat
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrListSplit
public import CollatzPosDens.StoppingTrace.TrPrefixFreeMass
public import CollatzPosDens.StoppingTrace.TrWhiteCount

/-!
# Continuation through the paid passage

Fix `n`, `J = ⌊n/2⌋`, `ξ ∈ G_n`, and let whiteness, the renewal function `Q`, the penalty
`H = Q / w` and the paid passage mass `F̃_e` refer to `(n, ξ, ε_*)`. For a black point `e ∈ 𝒫`
and a horizon `1 ≤ L ≤ J`,
`Q(e) ≤ ∑_{a ∈ 𝒜_n} μ̃_e(a) e^{-z_* N^e_{L-1}(a)} Q(y^e_L(a))`, where `μ̃_e` is the paid fresh law,
`N^e_{L-1}` the weighted white count and `y^e_L` the fresh path.

The paid passage decomposition gives `Q(e) = ∑_{x} F̃_e(x) H(e + x)` over `x ∈ ℤ_{≥1} × ℤ`. For
each `x`, put `o = e + x`; the `L`-step identity expands `H(o)` over `γ ∈ 𝔅^L`. Splitting off the
reward of the last block, `N^*(o, γ; L) = N^*(o, γ; L - 1) + rw(v, γ^L)` with `v = x_{L-1}(o, γ)`,
and `e^{-z_* rw(v, b)} H(v + bpt(b)) = I(v; b) Q(v + bpt(b)) ≤ Q(v + bpt(b))` for a block `b` of
nonzero weight, since `w(v + bpt(b)) I(v; b) = e^{-z_* rw(v, b)}` and `I ≤ 1`. This bounds the term
of `γ` by `bw^⊗(γ) e^{-z_* N^*(o, γ; L-1)} Q(x_L(o, γ))`. These quantities only depend on the
first `L` blocks of a list, and the remaining `J - L` blocks carry total weight `1`, so the sum may
be taken over `𝔅^J` instead. Multiplying by `F̃_e(x)` and summing over `x` gives the claim.

## Main results

* `CollatzPosDens.chQ_le_tsum_trFreshLaw_mul_exp`: the continuation inequality.

## Implementation notes

The paid fresh law is valued in `[0, ∞]`, so the inequality is stated in `[0, ∞]`, with the real
quantity `Q(e)` and the real factors `e^{-z_* N} Q(y)` embedded through `ENNReal.ofReal`; the sum
over the atoms is then an unconditional `tsum` over the subtype `𝒜_n = trAtoms n`. The conditions
`n ≥ 1` and that `ξ` is a unit are not needed. The hypothesis `1 ≤ L` is needed: for `L = 0` the
bound would read `Q(e) ≤ ∑ F̃_e(x) Q(e + x)`, whereas the decomposition only gives
`Q(e) = ∑ F̃_e(x) H(e + x)` with `H ≥ Q`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The term of `γ ∈ 𝔅^L`, `L ≥ 1`, in the `L`-step identity for `H` is bounded by
`bw^⊗(γ) e^{-z_* N^*(o, γ; L-1)} Q(x_L(o, γ))`. -/
private theorem trListWeight_mul_exp_mul_c3H_le (n : ℕ) (ξ : ResidueGroup n) (o : ℤ × ℤ)
    {L : ℕ} (hL : 1 ≤ L) (γ : List (List ℤ × ℤ)) (hγ : γ.length = L)
    (hγB : ∀ x ∈ γ, x.2 ∈ ({4, 5} : Set ℤ)) :
    trListWeight γ * Real.exp (-(zStar : ℝ) * trCount n ξ o γ L) *
        c3H n ξ (epsStar : ℝ) (o + chBlockPath γ L) ≤
      trListWeight γ * (Real.exp (-(zStar : ℝ) * trCount n ξ o γ (L - 1)) *
        chQ n ξ (epsStar : ℝ) (trPath o γ L)) := by
  by_cases hw : trListWeight γ = 0
  · simp [hw]
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  have hm : m < γ.length := by omega
  have hbmem : γ[m] ∈ γ := List.getElem_mem hm
  have hbw : chBlockWeight γ[m] ≠ 0 := fun h ↦
    hw (List.prod_eq_zero (List.mem_map.2 ⟨γ[m], hbmem, h⟩))
  have hc : ∀ a ∈ γ[m].1, a ≠ 4 ∧ a ≠ 5 := fun a ha ↦ by
    by_contra h
    refine hbw (chBlockWeight_eq_zero_of_mem ha ?_)
    rw [not_and_or, not_ne_iff, not_ne_iff] at h
    rcases h with h | h <;> simp [h]
  have he : γ[m].2 = 4 ∨ γ[m].2 = 5 := by simpa using hγB γ[m] hbmem
  have hpath : o + chBlockPath γ (m + 1) = trPath o γ m + chBlockPoint γ[m] := by
    rw [chBlockPath_succ γ hm, ← add_assoc, trPath_eq_add_chBlockPath]
  have hfac := chWhiteFactor_mul_chInternalWeight_eq_exp_trReward n ξ (trPath o γ m) γ[m] hc he
  rw [trCount_succ o γ hm, Nat.add_sub_cancel, trPath_eq_add_chBlockPath o γ (m + 1), hpath,
    mul_add, Real.exp_add, ← hfac, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (trListWeight_nonneg γ)
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [mul_comm (chWhiteFactor _ _ _ _), mul_assoc, chWhiteFactor_mul_c3H]
  exact mul_le_of_le_one_left (chQ_nonneg _ _ _ _) (chInternalWeight_le_one _ _ _ _ _)

/-- From a point `o ∈ 𝒫` and for `1 ≤ L ≤ J`,
`H(o) ≤ ∑_{β ∈ 𝔅^J} bw^⊗(β) e^{-z_* N^*(o, β; L-1)} Q(x_L(o, β))`, in `[0, ∞]`. -/
private theorem ofReal_c3H_le_tsum_trListWeight (n : ℕ) (ξ : ResidueGroup n) {o : ℤ × ℤ}
    (ho : o ∈ bkPoints) {L J : ℕ} (hL : 1 ≤ L) (hLJ : L ≤ J) :
    ENNReal.ofReal (c3H n ξ (epsStar : ℝ) o) ≤
      ∑' β : {β : List (List ℤ × ℤ) //
          β.length = J ∧ ∀ x ∈ β, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
        ENNReal.ofReal (trListWeight β.1) *
          ENNReal.ofReal (Real.exp (-(zStar : ℝ) * trCount n ξ o β.1 (L - 1)) *
            chQ n ξ (epsStar : ℝ) (trPath o β.1 L)) := by
  set Φ : List (List ℤ × ℤ) → ℝ := fun γ ↦
    Real.exp (-(zStar : ℝ) * trCount n ξ o γ (L - 1)) * chQ n ξ (epsStar : ℝ) (trPath o γ L)
    with hΦ
  have hΦapp : ∀ u f : List (List ℤ × ℤ), u.length = L → Φ (u ++ f) = Φ u := by
    intro u f hu
    simp only [hΦ]
    rw [trCount_append_of_le o u f (by omega), trPath_concat o u f hu.ge]
  set T : {β : List (List ℤ × ℤ) // β.length = L ∧ ∀ x ∈ β, x.2 ∈ ({4, 5} : Set ℤ)} → ℝ :=
    fun γ ↦ trListWeight γ.1 * Real.exp (-(zStar : ℝ) * trCount n ξ o γ.1 L) *
      c3H n ξ (epsStar : ℝ) (o + chBlockPath γ.1 L) with hT
  have hT0 : ∀ γ, 0 ≤ T γ := fun γ ↦
    mul_nonneg (mul_nonneg (trListWeight_nonneg _) (Real.exp_pos _).le) (c3H_nonneg _ _ _ _)
  have hH : c3H n ξ (epsStar : ℝ) o = ∑' γ, T γ := c3H_eq_tsum_blockList n ξ L ho
  by_cases hTS : Summable T
  swap
  · rw [hH, tsum_eq_zero_of_not_summable hTS, ENNReal.ofReal_zero]
    exact bot_le
  rw [hH, ENNReal.ofReal_tsum_of_nonneg hT0 hTS]
  refine (ENNReal.tsum_le_tsum fun γ : {β : List (List ℤ × ℤ) //
      β.length = L ∧ ∀ x ∈ β, x.2 ∈ ({4, 5} : Set ℤ)} ↦ (ENNReal.ofReal_le_ofReal
    (trListWeight_mul_exp_mul_c3H_le n ξ o hL γ.1 γ.2.1 γ.2.2)).trans_eq
    (ENNReal.ofReal_mul (trListWeight_nonneg _))).trans (le_of_eq ?_)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hLJ
  have hstep : ∀ β : {β : List (List ℤ × ℤ) //
      β.length = L + b ∧ ∀ x ∈ β, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
      ENNReal.ofReal (Φ β.1) = ENNReal.ofReal (Φ (trSublist β.1 1 L)) := by
    intro β
    rw [trSublist_one]
    conv_lhs => rw [← List.take_append_drop L β.1]
    rw [hΦapp _ _ (by rw [List.length_take, β.2.1]; omega)]
  change _ = ∑' β : {β : List (List ℤ × ℤ) //
      β.length = L + b ∧ ∀ x ∈ β, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
    ENNReal.ofReal (trListWeight β.1) * ENNReal.ofReal (Φ β.1)
  simp_rw [hstep]
  rw [tsum_trListWeight_trSublist {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)} L b
    (fun u _ ↦ ENNReal.ofReal (Φ u))]
  refine tsum_congr fun u ↦ ?_
  simp_rw [mul_right_comm _ _ (ENNReal.ofReal (Φ u.1))]
  rw [ENNReal.tsum_mul_left, tsum_ofReal_trListWeight_length_eq, mul_one]

/-- **Continuation through the paid passage.** Let `e ∈ 𝒫` be black for `(n, ξ, ε_*)` and
`1 ≤ L ≤ J = ⌊n/2⌋`. Then `Q(e) ≤ ∑_{a ∈ 𝒜_n} μ̃_e(a) e^{-z_* N^e_{L-1}(a)} Q(y^e_L(a))`, in
`[0, ∞]`, with `Q` and whiteness taken at the threshold `ε_*`. -/
@[collatz_pos_dens "lem_c3_continuation"]
theorem chQ_le_tsum_trFreshLaw_mul_exp (n : ℕ) (ξ : ResidueGroup n) {e : ℤ × ℤ}
    (he : e ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) e) {L : ℕ} (hL : 1 ≤ L)
    (hLJ : L ≤ n / 2) :
    ENNReal.ofReal (chQ n ξ (epsStar : ℝ) e) ≤
      ∑' a : trAtoms n, c3PaidLaw n ξ e a *
        ENNReal.ofReal (Real.exp (-(zStar : ℝ) * trWhiteCount n ξ e a (L - 1)) *
          chQ n ξ (epsStar : ℝ) (trFreshPath e a L)) := by
  set G : ℤ × ℤ → ℝ≥0∞ := fun o ↦
    ∑' β : {β : List (List ℤ × ℤ) //
        β.length = n / 2 ∧ ∀ x ∈ β, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
      ENNReal.ofReal (trListWeight β.1) *
        ENNReal.ofReal (Real.exp (-(zStar : ℝ) * trCount n ξ o β.1 (L - 1)) *
          chQ n ξ (epsStar : ℝ) (trPath o β.1 L)) with hG
  set g : ℕ × ℤ → ℝ≥0∞ := fun y ↦
    c3PaidPassage n ξ e ((y.1 : ℤ), y.2) * G (e + ((y.1 : ℤ), y.2)) with hg
  rw [ofReal_chQ_eq_tsum_c3PaidPassage n ξ he hb]
  calc _ ≤ ∑' x : {x : ℤ × ℤ // 1 ≤ x.1}, c3PaidPassage n ξ e x * G (e + x) := by
        refine ENNReal.tsum_le_tsum fun x ↦ mul_le_mul_right ?_ _
        refine ofReal_c3H_le_tsum_trListWeight n ξ ?_ hL hLJ
        have h1 := mem_bkPoints.1 he
        have h2 := x.2
        simp only [mem_bkPoints, bkJ, Prod.fst_add] at h1 ⊢
        omega
    _ = ∑' x : {x : ℤ × ℤ // 1 ≤ x.1}, g (x.1.1.toNat, x.1.2) := by
        refine tsum_congr fun x ↦ ?_
        have hx : (((x.1.1.toNat : ℕ) : ℤ), x.1.2) = x.1 :=
          Prod.ext (Int.toNat_of_nonneg (by have := x.2; omega)) rfl
        simp only [hg, hx]
    _ ≤ ∑' y : ℕ × ℤ, g y := by
        refine ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun x : {x : ℤ × ℤ // 1 ≤ x.1} ↦ (x.1.1.toNat, x.1.2)) (fun x x' h ↦ ?_) g
        simp only [Prod.mk.injEq] at h
        refine Subtype.ext (Prod.ext ?_ h.2)
        have := x.2
        have := x'.2
        omega
    _ = _ := by
        rw [← (trAtomsEquiv n).symm.tsum_eq]
        conv_rhs => rw [ENNReal.tsum_prod']
        refine tsum_congr fun y : ℕ × ℤ ↦ ?_
        simp only [hg, hG]
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun β ↦ ?_
        simp only [trAtomsEquiv, Equiv.coe_fn_symm_mk, c3PaidLaw_def, trWhiteCount_def,
          trFreshPath, mul_assoc]
        rfl

end CollatzPosDens
