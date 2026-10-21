/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3HStep
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChQRange
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrListWeight
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The `L`-step identity for `H`

Fix a level `n` and a residue `ξ ∈ G_n`, and let whiteness, the white factor, the renewal
function `Q` and the penalty `H = Q / w` refer to `(n, ξ, ε_*)`. For every `L ∈ ℕ` and `v ∈ 𝒫`,
`H(v) = ∑_{β ∈ 𝔅^L} bw^⊗(β) exp(-z_* N^*(v, β; L)) H(v + Bp_L(β))`.

The proof is by induction on `L`. For `L = 0` the only list is the empty one. For the step, the
one-step identity `CollatzPosDens.c3H_eq_tsum` expands `H(v)` over the first block `b`, the
induction hypothesis expands `H(v + bpt(b))` over the remaining list `β'`, and for `β = b :: β'`
the weight, the count and the block path all split off their first block:
`bw^⊗(β) = bw(b) bw^⊗(β')`, `N^*(v, β; L + 1) = rw(v, b) + N^*(v + bpt(b), β'; L)` and
`Bp_{L+1}(β) = bpt(b) + Bp_L(β')`. Concatenation `𝔅 × 𝔅^L → 𝔅^{L+1}` is a bijection, which
merges the double sum into one.

## Main results

* `CollatzPosDens.c3H_eq_tsum_blockList`: the `L`-step identity for `H`.

## Implementation notes

A list in `𝔅^L` is a `List (List ℤ × ℤ)` of length `L` all of whose blocks have closing letter
in `{4, 5}`, and the sum over `𝔅^L` is a `tsum` over the corresponding subtype. All terms are
nonnegative and `H ≤ e^{z_*}`, so the sums converge; the double sums are rearranged in `[0, ∞]`
and the identity is transported back to `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- `H(v) ≤ e^{z_*}`, since `Q ≤ 1` and `w(v) ≥ e^{-z_*}`. -/
theorem c3H_le_exp_zStar (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (v : ℤ × ℤ) :
    c3H n ξ ε v ≤ Real.exp (zStar : ℝ) := by
  have hz : (0 : ℝ) ≤ zStar := by exact_mod_cast zStar_nonneg
  by_cases h : IsBkWhite n ξ ε v
  · rw [c3H_of_isBkWhite h]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (chQ_le_one _ _ _ _)
  · rw [c3H_of_not_isBkWhite h]
    exact (chQ_le_one _ _ _ _).trans (Real.one_le_exp hz)

private lemma add_chBlockPoint_mem_bkPoints' {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (b : List ℤ × ℤ) : v + chBlockPoint b ∈ bkPoints := by
  simp only [mem_bkPoints, bkJ, Prod.fst_add, chBlockPoint_fst] at hv ⊢
  omega

/-- The summand of the `L`-step identity. -/
private noncomputable def iterTerm (n : ℕ) (ξ : ResidueGroup n) (L : ℕ) (v : ℤ × ℤ)
    (β : List (List ℤ × ℤ)) : ℝ :=
  trListWeight β * Real.exp (-(zStar : ℝ) * trCount n ξ v β L) *
    c3H n ξ (epsStar : ℝ) (v + chBlockPath β L)

private lemma iterTerm_nonneg (n : ℕ) (ξ : ResidueGroup n) (L : ℕ) (v : ℤ × ℤ)
    (β : List (List ℤ × ℤ)) : 0 ≤ iterTerm n ξ L v β :=
  mul_nonneg (mul_nonneg (trListWeight_nonneg β) (Real.exp_pos _).le) (c3H_nonneg _ _ _ _)

private lemma iterTerm_cons (n : ℕ) (ξ : ResidueGroup n) (L : ℕ) (v : ℤ × ℤ)
    (b : List ℤ × ℤ) (β : List (List ℤ × ℤ)) :
    iterTerm n ξ (L + 1) v (b :: β) =
      chBlockWeight b * Real.exp (-(zStar : ℝ) * trReward n ξ v b) *
        iterTerm n ξ L (v + chBlockPoint b) β := by
  simp only [iterTerm, trListWeight_cons, trCount_cons_succ, chBlockPath_cons_succ, add_assoc,
    mul_add, Real.exp_add]
  ring

/-- Concatenation `𝔅 × 𝔅^L → 𝔅^{L+1}`, `(b, β) ↦ b :: β`, is a bijection. -/
private noncomputable def consEquiv (L : ℕ) :
    {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)} ×
        {β : List (List ℤ × ℤ) // β.length = L ∧ ∀ x ∈ β, x.2 ∈ ({4, 5} : Set ℤ)} ≃
      {β : List (List ℤ × ℤ) // β.length = L + 1 ∧ ∀ x ∈ β, x.2 ∈ ({4, 5} : Set ℤ)} :=
  Equiv.ofBijective
    (fun p ↦ ⟨p.1.1 :: p.2.1, by simp [p.2.2.1], List.forall_mem_cons.2 ⟨p.1.2, p.2.2.2⟩⟩)
    ⟨fun p q h ↦ by
      have h' := congrArg Subtype.val h
      simp only [List.cons.injEq] at h'
      exact Prod.ext (Subtype.ext h'.1) (Subtype.ext h'.2),
    fun ⟨β, hl, hm⟩ ↦ by
      match β, hl, hm with
      | b :: β', hl, hm =>
        rw [List.forall_mem_cons] at hm
        exact ⟨(⟨b, hm.1⟩, ⟨β', by simpa using hl, hm.2⟩), rfl⟩⟩

private lemma ofReal_c3H_eq_tsum (n : ℕ) (ξ : ResidueGroup n) (L : ℕ) {v : ℤ × ℤ}
    (hv : v ∈ bkPoints) :
    ENNReal.ofReal (c3H n ξ (epsStar : ℝ) v) =
      ∑' β : {β : List (List ℤ × ℤ) // β.length = L ∧ ∀ x ∈ β, x.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (iterTerm n ξ L v β) := by
  induction L generalizing v with
  | zero =>
    rw [tsum_eq_single ⟨[], rfl, by simp⟩ fun ⟨β, hl, _⟩ h ↦
      (h (Subtype.ext (List.length_eq_zero_iff.1 hl))).elim]
    simp [iterTerm]
  | succ L ih =>
    set B := {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}
    set a : B → ℝ := fun b ↦ chBlockWeight b * Real.exp (-(zStar : ℝ) * trReward n ξ v b)
    have ha0 : ∀ b, 0 ≤ a b := fun b ↦ mul_nonneg (chBlockWeight_nonneg _) (Real.exp_pos _).le
    have hz : (0 : ℝ) ≤ zStar := by exact_mod_cast zStar_nonneg
    have hsum : Summable fun b : B ↦ a b * c3H n ξ (epsStar : ℝ) (v + chBlockPoint b) := by
      refine (hasSum_prod_chBlockWeight_single.summable.mul_right
        (Real.exp (zStar : ℝ))).of_nonneg_of_le
        (fun b ↦ mul_nonneg (ha0 b) (c3H_nonneg _ _ _ _)) fun b ↦ ?_
      refine mul_le_mul ?_ (c3H_le_exp_zStar _ _ _ _) (c3H_nonneg _ _ _ _)
        (chBlockWeight_nonneg _)
      refine mul_le_of_le_one_right (chBlockWeight_nonneg _) (Real.exp_le_one_iff.2 ?_)
      rw [neg_mul]
      exact neg_nonpos.2 (mul_nonneg hz (trReward_nonneg _ _))
    rw [c3H_eq_tsum n ξ hv, ENNReal.ofReal_tsum_of_nonneg
      (fun b ↦ mul_nonneg (ha0 b) (c3H_nonneg _ _ _ _)) hsum]
    rw [← (consEquiv L).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun b ↦ ?_
    rw [ENNReal.ofReal_mul (ha0 b), ih (add_chBlockPoint_mem_bkPoints' hv b),
      ← ENNReal.tsum_mul_left]
    refine tsum_congr fun β ↦ ?_
    change _ = ENNReal.ofReal (iterTerm n ξ (L + 1) v (b.1 :: β.1))
    rw [iterTerm_cons, ENNReal.ofReal_mul (ha0 b)]

/-- **`L`-step identity for `H`.** For every `L ∈ ℕ` and `v ∈ 𝒫`,
`H(v) = ∑_{β ∈ 𝔅^L} bw^⊗(β) exp(-z_* N^*(v, β; L)) H(v + Bp_L(β))`, all at the threshold `ε_*`. -/
@[collatz_pos_dens "lem_c3_H_iterate"]
theorem c3H_eq_tsum_blockList (n : ℕ) (ξ : ResidueGroup n) (L : ℕ) {v : ℤ × ℤ}
    (hv : v ∈ bkPoints) :
    c3H n ξ (epsStar : ℝ) v =
      ∑' β : {β : List (List ℤ × ℤ) // β.length = L ∧ ∀ x ∈ β, x.2 ∈ ({4, 5} : Set ℤ)},
        trListWeight β * Real.exp (-(zStar : ℝ) * trCount n ξ v β L) *
          c3H n ξ (epsStar : ℝ) (v + chBlockPath β L) := by
  rw [← ENNReal.toReal_ofReal (c3H_nonneg n ξ _ v), ofReal_c3H_eq_tsum n ξ L hv,
    ENNReal.tsum_toReal_eq fun _ ↦ ENNReal.ofReal_ne_top]
  exact tsum_congr fun β ↦ ENNReal.toReal_ofReal (iterTerm_nonneg n ξ L v β)

end CollatzPosDens
