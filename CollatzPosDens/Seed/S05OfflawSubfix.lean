/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05OfflawCert
public import CollatzPosDens.Seed.S05OfflawStep
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# An offset-law certificate is a sub-fixed point

Let `g` be an offset-law certificate (`CollatzPosDens.IsOfflawCert`) and `Ĝ = Ĝ_g` its step
function (`CollatzPosDens.offlawStep`). For a real `x`, write
$$(T\widehat{\mathsf G})(x) =
  \sum_{a \ge 1} 2^{-a}\, \widehat{\mathsf G}\Bigl(\frac{2^a x - 1}{3}\Bigr)$$
for the one-letter recursion of the offset law applied to `Ĝ`. Then for every `x ≥ 0`,
$$\widehat{\mathsf G}(x) \le \max\bigl(\mathsf G_0(x),\ (T\widehat{\mathsf G})(x)\bigr),$$
where `𝖦₀` is the tail floor `CollatzPosDens.offlawFloor`.

The proof: the conditions `IsOfflawCert.monotone` and `IsOfflawCert.le_floor_last` make `Ĝ`
nondecreasing with values in `[0, 1]`, so the series converges and `TĜ` is nondecreasing. Each
integer contribution satisfies `c_g(k,a) ≤ 2^62 2^{-a} Ĝ((2^a ξ_k - 1)/3)`, so the condition
`IsOfflawCert.le_max` gives the inequality at every grid point `ξ_k`; monotonicity of `𝖦₀` and of
`TĜ` carries it from `ξ_{ix(x)}` to `x`.

## Main results

* `CollatzPosDens.IsOfflawCert.le_two_pow`: every entry of a certificate is at most `2^62`.
* `CollatzPosDens.IsOfflawCert.monotone_offlawStep`: the step function of a certificate is
  nondecreasing.
* `CollatzPosDens.IsOfflawCert.summable_offlawStep`: the series `(TĜ)(x)` converges.
* `CollatzPosDens.IsOfflawCert.offlawStep_le_max`: the sub-fixed-point inequality
  `Ĝ(x) ≤ max(𝖦₀(x), (TĜ)(x))` for `x ≥ 0`.

## Implementation notes

The series is a real `tsum` over `ℕ+`, with `2^{-a}` written `2⁻¹ ^ a`, as in the recursion
`CollatzPosDens.offlawCdf_succ`; its summability is
`CollatzPosDens.IsOfflawCert.summable_offlawStep`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §16.6.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

namespace IsOfflawCert

variable {g : Fin 6199 → ℕ}

/-- The last entry of a certificate is at most `2^62 𝖦₀(ξ_6198)`. -/
theorem le_two_pow_mul_offlawFloor (hg : IsOfflawCert g) :
    (g (Fin.last 6198) : ℝ) ≤ 2 ^ 62 * offlawFloor ((offlawGrid 6198 : ℚ) : ℝ) :=
  (Nat.cast_le.2 hg.le_floor_last).trans
    (Nat.floor_le (mul_nonneg (by positivity) (offlawFloor_nonneg _)))

/-- Every entry of a certificate is at most `2^62`. -/
theorem le_two_pow (hg : IsOfflawCert g) (k : Fin 6199) : g k ≤ 2 ^ 62 := by
  have h0 : (0 : ℝ) ≤ ((offlawGrid 6198 : ℚ) : ℝ) := by exact_mod_cast offlawGrid_nonneg 6198
  have h1 : (g k : ℝ) ≤ 2 ^ 62 :=
    calc (g k : ℝ) ≤ g (Fin.last 6198) := by exact_mod_cast hg.monotone (Fin.le_last k)
      _ ≤ 2 ^ 62 * offlawFloor ((offlawGrid 6198 : ℚ) : ℝ) := hg.le_two_pow_mul_offlawFloor
      _ ≤ 2 ^ 62 * 1 := by gcongr; exact offlawFloor_le_one h0
      _ = 2 ^ 62 := mul_one _
  exact_mod_cast h1

/-- The step function of a certificate is nondecreasing. -/
theorem monotone_offlawStep (hg : IsOfflawCert g) : Monotone (offlawStep g) :=
  offlawStep_monotone g hg.monotone <| by
    rw [div_le_iff₀ (by positivity), mul_comm]
    exact hg.le_two_pow_mul_offlawFloor

/-- The step function of a certificate is at most `1`. -/
theorem offlawStep_le_one (hg : IsOfflawCert g) (y : ℝ) : offlawStep g y ≤ 1 :=
  CollatzPosDens.offlawStep_le_one g hg.le_two_pow y

/-- The terms `2^{-a} Ĝ((2^a x - 1)/3)` of the recursion, indexed by `a ∈ ℕ`. -/
private theorem summable_nat (hg : IsOfflawCert g) (x : ℝ) :
    Summable fun a : ℕ => (2⁻¹ : ℝ) ^ a * offlawStep g ((2 ^ a * x - 1) / 3) :=
  Summable.of_nonneg_of_le (fun a => mul_nonneg (by positivity) (offlawStep_nonneg g _))
    (fun a => mul_le_of_le_one_right (by positivity) (hg.offlawStep_le_one _))
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

/-- The series `(TĜ)(x) = ∑_{a ≥ 1} 2^{-a} Ĝ((2^a x - 1)/3)` converges. -/
theorem summable_offlawStep (hg : IsOfflawCert g) (x : ℝ) :
    Summable fun a : ℕ+ => (2⁻¹ : ℝ) ^ (a : ℕ) * offlawStep g ((2 ^ (a : ℕ) * x - 1) / 3) :=
  (hg.summable_nat x).comp_injective PNat.coe_injective

/-- The series `(TĜ)(x)` is nondecreasing in `x`. -/
private theorem monotone_tsum (hg : IsOfflawCert g) :
    Monotone fun x : ℝ =>
      ∑' a : ℕ+, (2⁻¹ : ℝ) ^ (a : ℕ) * offlawStep g ((2 ^ (a : ℕ) * x - 1) / 3) := by
  intro x x' hxx'
  refine (hg.summable_offlawStep x).tsum_le_tsum (fun a => ?_) (hg.summable_offlawStep x')
  gcongr
  exact hg.monotone_offlawStep (by gcongr)

/-- Each integer contribution is at most `2^62 2^{-a} Ĝ((2^a ξ_k - 1)/3)`. -/
private theorem offlawContrib_le (k a : ℕ) :
    (offlawContrib g k a : ℝ) ≤
      2 ^ 62 * ((2⁻¹ : ℝ) ^ a * offlawStep g ((2 ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3)) := by
  set y : ℝ := (2 ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3 with hy
  rcases lt_or_ge y 0 with h0 | h0
  · rw [offlawContrib_of_neg g h0]
    simp only [Nat.cast_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (offlawStep_nonneg g _))
  rcases lt_or_ge ((offlawGrid 6198 : ℚ) : ℝ) y with h1 | h1
  · rw [offlawContrib_of_lt g h1, offlawStep_of_gt g h1, inv_pow]
    refine (Nat.floor_le (by positivity)).trans ?_
    have := Nat.floor_le (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ 62) (offlawFloor_nonneg y))
    calc ((2 : ℝ) ^ a)⁻¹ * ⌊(2 : ℝ) ^ 62 * offlawFloor y⌋₊
        ≤ ((2 : ℝ) ^ a)⁻¹ * (2 ^ 62 * offlawFloor y) := by gcongr
      _ = _ := by ring
  · rw [offlawContrib_of_nonneg_of_le g h0 h1, offlawStep_of_mem_Icc g h0 h1, inv_pow]
    refine (Nat.floor_le (by positivity)).trans (le_of_eq ?_)
    rw [offlawIndexFin]
    field_simp
    rfl

/-- The sub-fixed-point inequality at a grid point: `2^{-62} g_k ≤ max(𝖦₀(ξ_k), (TĜ)(ξ_k))`. -/
private theorem le_max_offlawGrid (hg : IsOfflawCert g) (k : Fin 6199) :
    (g k : ℝ) / 2 ^ 62 ≤ max (offlawFloor ((offlawGrid k : ℚ) : ℝ))
      (∑' a : ℕ+, (2⁻¹ : ℝ) ^ (a : ℕ) *
        offlawStep g ((2 ^ (a : ℕ) * ((offlawGrid k : ℚ) : ℝ) - 1) / 3)) := by
  set ξ : ℝ := ((offlawGrid k : ℚ) : ℝ)
  set F : ℕ → ℝ := fun a => (2⁻¹ : ℝ) ^ a * offlawStep g ((2 ^ a * ξ - 1) / 3) with hF
  have hFnn : ∀ a, 0 ≤ F a := fun a => mul_nonneg (by positivity) (offlawStep_nonneg g _)
  have hpart : ∑ a ∈ Icc 1 60, F a ≤ ∑' a : ℕ+, F a := by
    rw [tsum_pnat_eq_tsum_succ (f := F)]
    have hs : Summable fun n : ℕ => F (n + 1) :=
      (summable_nat_add_iff 1).2 (hg.summable_nat ξ)
    calc ∑ a ∈ Icc 1 60, F a = ∑ n ∈ range 60, F (n + 1) := by
          rw [Finset.range_eq_Ico, Finset.sum_Ico_add' F 0 60 1]
          rfl
      _ ≤ ∑' n : ℕ, F (n + 1) := hs.sum_le_tsum _ fun n _ => hFnn _
  have hsum : ((∑ a ∈ Icc 1 60, offlawContrib g k a : ℕ) : ℝ) ≤ 2 ^ 62 * ∑' a : ℕ+, F a := by
    push_cast
    calc ∑ a ∈ Icc 1 60, (offlawContrib g k a : ℝ) ≤ ∑ a ∈ Icc 1 60, 2 ^ 62 * F a :=
          sum_le_sum fun a _ => offlawContrib_le k a
      _ = 2 ^ 62 * ∑ a ∈ Icc 1 60, F a := (mul_sum _ _ _).symm
      _ ≤ 2 ^ 62 * ∑' a : ℕ+, F a := by gcongr
  have hfl : (⌊(2 : ℝ) ^ 62 * offlawFloor ξ⌋₊ : ℝ) ≤ 2 ^ 62 * offlawFloor ξ :=
    Nat.floor_le (mul_nonneg (by positivity) (offlawFloor_nonneg _))
  have hk : (g k : ℝ) ≤ 2 ^ 62 * max (offlawFloor ξ) (∑' a : ℕ+, F a) := by
    rw [mul_max_of_nonneg _ _ (by positivity)]
    calc (g k : ℝ) ≤ ((max ⌊(2 : ℝ) ^ 62 * offlawFloor ξ⌋₊
          (∑ a ∈ Icc 1 60, offlawContrib g k a) : ℕ) : ℝ) := by exact_mod_cast hg.le_max k
      _ ≤ _ := by
          rw [Nat.cast_max]
          exact max_le_max hfl hsum
  rw [div_le_iff₀ (by positivity), mul_comm]
  exact hk

/-- **A certificate is a sub-fixed point**: if `g` is an offset-law certificate, then for every
real `x ≥ 0`, `Ĝ_g(x) ≤ max(𝖦₀(x), ∑_{a ≥ 1} 2^{-a} Ĝ_g((2^a x - 1)/3))`. -/
@[collatz_pos_dens "lem_s05_offlaw_subfix"]
theorem offlawStep_le_max (hg : IsOfflawCert g) {x : ℝ} (hx : 0 ≤ x) :
    offlawStep g x ≤ max (offlawFloor x)
      (∑' a : ℕ+, (2⁻¹ : ℝ) ^ (a : ℕ) * offlawStep g ((2 ^ (a : ℕ) * x - 1) / 3)) := by
  rcases lt_or_ge ((offlawGrid 6198 : ℚ) : ℝ) x with h1 | h1
  · rw [offlawStep_of_gt g h1]
    exact le_max_left _ _
  set k : Fin 6199 := offlawIndexFin x
  have hξ0 : (0 : ℝ) ≤ ((offlawGrid k : ℚ) : ℝ) := by exact_mod_cast offlawGrid_nonneg k
  have hξx : ((offlawGrid k : ℚ) : ℝ) ≤ x := offlawGrid_offlawIndex_le hx
  rw [offlawStep_of_mem_Icc g hx h1]
  refine (hg.le_max_offlawGrid k).trans (max_le_max ?_ (hg.monotone_tsum hξx))
  exact offlawFloor_monotoneOn (Set.mem_Ici.2 hξ0) (Set.mem_Ici.2 hx) hξx

end IsOfflawCert

end CollatzPosDens
