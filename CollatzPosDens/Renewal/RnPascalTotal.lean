/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal

/-!
# Total mass of the Pascal weights

The Pascal weights `ϖ(b) = (b - 1) 2^{-b}` (`b ≥ 2`), `ϖ(b) = 0` (`b ≤ 1`) are nonnegative, and the
series `∑_{b ∈ ℤ} ϖ(b)` converges with sum `1`. Since `ϖ` vanishes for `b ≤ 1`, the series is
`∑_{n ≥ 0} ϖ(n + 2) = ∑_{k ≥ 1} k 2^{-k-1} = 1`.

## Main results

* `CollatzPosDens.hasSum_varpi`: `∑_{b ∈ ℤ} ϖ(b) = 1`, as an unconditionally convergent series.
* `CollatzPosDens.summable_varpi`, `CollatzPosDens.tsum_varpi`: the two halves of it.
* `CollatzPosDens.hasSum_varpiLast`, `CollatzPosDens.hasSum_varpiIn`: the closing letters `{4, 5}`
  carry mass `5/16`, the others `11/16`.
* `CollatzPosDens.hasSum_pi_fin_prod_of_nonneg`: a nonnegative family with sum `a` has
  product family on `β^n` with sum `a^n`.
* `CollatzPosDens.tsum_pi_fin_prod_ennreal`, `CollatzPosDens.tsum_pi_fin_prod_ennreal_const`: the
  same product rule for `[0, ∞]`-valued series, where no summability is needed.
* `CollatzPosDens.ofReal_tsum_le_tsum_ofReal`: `ofReal (∑ f) ≤ ∑ ofReal f` for `f ≥ 0`.

## Implementation notes

Unconditional convergence (`HasSum`) over `ℤ` is the strongest form of the statement; for a
series of nonnegative terms it is equivalent to convergence in any ordering. Nonnegativity of the
terms is `CollatzPosDens.varpi_nonneg`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The Pascal weights sum to `1` over `ℤ`. -/
@[collatz_pos_dens "lem_rn_pascal_total"]
theorem hasSum_varpi : HasSum varpi 1 := by
  have hg : Function.Injective (fun n : ℕ ↦ (n : ℤ) + 2) := fun a b h ↦ by
    simpa using h
  refine (hg.hasSum_iff fun b hb ↦ ?_).mp hasSum_varpi_add_two
  refine varpi_of_le_one ?_
  by_contra h
  exact hb ⟨(b - 2).toNat, by simp only; omega⟩

/-- The Pascal weights are summable over `ℤ`. -/
theorem summable_varpi : Summable varpi := hasSum_varpi.summable

/-- `∑_{b ∈ ℤ} ϖ(b) = 1`. -/
theorem tsum_varpi : ∑' b, varpi b = 1 := hasSum_varpi.tsum_eq

/-- The closing letters `{4, 5}` carry Pascal mass `ϖ(4) + ϖ(5) = 5/16`. -/
theorem hasSum_varpiLast : HasSum varpiLast (5 / 16) := by
  have h : HasSum varpiLast (∑ b ∈ ({4, 5} : Finset ℤ), varpiLast b) :=
    hasSum_sum_of_ne_finset_zero fun b hb ↦ varpiLast_of_notMem (by simpa using hb)
  convert h using 1
  rw [Finset.sum_pair (by norm_num), varpiLast_of_mem (by simp), varpiLast_of_mem (by simp),
    varpi_four, varpi_five]
  norm_num

/-- The nonclosing letters carry Pascal mass `1 - 5/16 = 11/16`. -/
theorem hasSum_varpiIn : HasSum varpiIn (11 / 16) := by
  have h := hasSum_varpi.sub hasSum_varpiLast
  norm_num at h
  convert h using 1
  funext b
  rw [← varpiLast_add_varpiIn b]
  ring

/-- If `v` is nonnegative with sum `a`, then `b ↦ ∏_i v(b_i)` on `β^n` has sum `a^n`. -/
theorem hasSum_pi_fin_prod_of_nonneg {β : Type*} {v : β → ℝ} {a : ℝ} (hv : HasSum v a)
    (h0 : 0 ≤ v) (n : ℕ) : HasSum (fun b : Fin n → β ↦ ∏ i, v (b i)) (a ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    generalize hg : (fun b : Fin n → β ↦ ∏ i, v (b i)) = g at ih
    have hg0 : 0 ≤ g := hg ▸ fun b ↦ Finset.prod_nonneg fun i _ ↦ h0 (b i)
    have hmul := HasSum.mul hv ih (Summable.mul_of_nonneg hv.summable ih.summable h0 hg0)
    have key : (fun x : β × (Fin n → β) ↦ v x.1 * g x.2) =
        (fun b : Fin (n + 1) → β ↦ ∏ i, v (b i)) ∘ Fin.consEquiv (fun _ ↦ β) := by
      subst hg
      funext x
      simp [Fin.consEquiv, Fin.prod_univ_succ]
    rw [key, ← pow_succ'] at hmul
    exact (Equiv.hasSum_iff _).mp hmul

open scoped ENNReal

/-- A product of `[0, ∞]`-valued series over `Fin K`: `∑_x ∏_i f_i(x_i) = ∏_i ∑_a f_i(a)`. -/
theorem tsum_pi_fin_prod_ennreal :
    ∀ {K : ℕ} {α : Fin K → Type*} (f : ∀ i, α i → ℝ≥0∞),
      ∑' x : (∀ i, α i), ∏ i, f i (x i) = ∏ i, ∑' a, f i a
  | 0, α, f => by simp
  | K + 1, α, f => by
    rw [← (Fin.consEquiv α).tsum_eq, Fin.prod_univ_succ]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a ↦ ?_
    dsimp only
    rw [ENNReal.tsum_mul_left, tsum_pi_fin_prod_ennreal]

/-- `∑_{h : Fin N → α} ∏_i f(h_i) = (∑_a f(a))^N` in `[0, ∞]`. -/
theorem tsum_pi_fin_prod_ennreal_const {α : Type*} (f : α → ℝ≥0∞) (N : ℕ) :
    ∑' h : Fin N → α, ∏ i, f (h i) = (∑' a, f a) ^ N := by
  simpa using tsum_pi_fin_prod_ennreal fun _ : Fin N ↦ f

/-- `ofReal` of a sum of nonnegative reals is at most the sum of the `ofReal`s. -/
theorem ofReal_tsum_le_tsum_ofReal {α : Type*} {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (∑' a, f a) ≤ ∑' a, ENNReal.ofReal (f a) := by
  by_cases h : Summable f
  · rw [ENNReal.ofReal_tsum_of_nonneg hf h]
  · simp [tsum_eq_zero_of_not_summable h]

end CollatzPosDens
