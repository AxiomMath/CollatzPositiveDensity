/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHoldList
public import CollatzPosDens.Renewal.RnJointPgf
public import CollatzPosDens.Renewal.RnPascalTotal
public import Mathlib.Data.Fin.Tuple.Take

/-!
# Splitting off the tail of a tilted hold-list sum

Let `X ≥ 0` and `y > 0` be real, let `u ≤ N`, and let `E` be a set of hold lists of length `u`.
Summing the tilted weight `η^{⊗N}(h) X^{j(h_1 + ⋯ + h_N)} y^{l(h_1 + ⋯ + h_N)}` over the hold lists
`h ∈ 𝒫^N` whose first `u` entries form a list in `E` gives, in `[0, ∞]`,
`𝖦(X, y)^{N - u} ∑_{g ∈ E} η^{⊗u}(g) X^{j(g_1 + ⋯ + g_u)} y^{l(g_1 + ⋯ + g_u)}`.

Indeed, writing `h = gk` as the concatenation of its first `u` entries `g` and its last `N - u`
entries `k`, the tilted weight of `h` is the product of the tilted weight of `g` and the one-step
tilted weights `η(k_i) X^{j(k_i)} y^{l(k_i)}`; by Tonelli the sum over `k ∈ 𝒫^{N - u}` factorises
as the `(N - u)`-th power of the one-step sum, which is `𝖦(X, y)`.

## Main results

* `CollatzPosDens.tsum_holdListLaw_tilt_take`: the tail of the tilted sum over hold lists with
  prescribed prefix splits off as `𝖦(X, y)^{N - u}`.
* `CollatzPosDens.tsum_holdListLaw_tilt_append`: the same identity with `N = u + m` and the list
  written as a concatenation.

## Implementation notes

As in the definition of the hold-list weight, a point is a pair `(j, l) : ℕ × ℤ`, and
`𝒫 = ℤ_{≥1} × ℤ` is the set of pairs with `1 ≤ j`; `𝒫^N` is the set of `h : Fin N → ℕ × ℤ` with
`1 ≤ j(h_i)` for every `i`. The prefix `(h_1, …, h_u)` is `Fin.take u _ h`. The set `E` is any set
of tuples `Fin u → ℕ × ℤ`, not necessarily contained in `𝒫^u`, and the sum on the right runs
over `E ∩ 𝒫^u`. All sums are taken in `ℝ≥0∞`, each term embedded by `ENNReal.ofReal`, so
`𝖦(X, y) = ∞` is allowed with the convention `0 · ∞ = 0`. Only `0 ≤ X` is assumed; the hypothesis
`y > 0` is needed for `y^{a + b} = y^a y^b` with integer exponents.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The one-step tilted weight `η(p) X^{j(p)} y^{l(p)}` of a point `p ∈ 𝒫`, as an element of
`[0, ∞]`, and `0` off `𝒫`. -/
private noncomputable def tiltWeight (X y : ℝ) (p : ℕ × ℤ) : ℝ≥0∞ :=
  if 1 ≤ p.1 then ENNReal.ofReal (holdLaw p.1 p.2 * X ^ p.1 * y ^ p.2) else 0

private lemma tsum_tiltWeight (X y : ℝ) : ∑' p, tiltWeight X y p = holdJointPgf X y := by
  rw [holdJointPgf_eq_tsum_natPoints]
  refine (tsum_subtype {p : ℕ × ℤ | 1 ≤ p.1}
    (fun p ↦ ENNReal.ofReal (holdLaw p.1 p.2 * X ^ p.1 * y ^ p.2))).trans ?_ |>.symm
  refine tsum_congr fun p ↦ ?_
  simp [tiltWeight, Set.indicator]

private lemma zpow_finset_sum {ι : Type*} (s : Finset ι) {y : ℝ} (hy : y ≠ 0) (f : ι → ℤ) :
    y ^ (∑ i ∈ s, f i) = ∏ i ∈ s, y ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hy, ih]

/-- The tilted weight of a hold list in `𝒫^N` is the product of the one-step tilted weights, and
the product vanishes off `𝒫^N`. -/
private lemma prod_tiltWeight {N : ℕ} {X y : ℝ} (hX : 0 ≤ X) (hy : 0 < y)
    (h : Fin N → ℕ × ℤ) :
    ∏ i, tiltWeight X y (h i) =
      if ∀ i, 1 ≤ (h i).1 then
        ENNReal.ofReal (holdListLaw h * X ^ (∑ i, (h i).1) * y ^ (∑ i, (h i).2))
      else 0 := by
  split_ifs with hh
  · rw [holdListLaw_def, ← Finset.prod_pow_eq_pow_sum, zpow_finset_sum _ hy.ne',
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ENNReal.ofReal_prod_of_nonneg fun i _ ↦ holdJointPgf_term_nonneg hX hy.le _ _]
    exact Finset.prod_congr rfl fun i _ ↦ by simp [tiltWeight, hh i]
  · obtain ⟨i, hi⟩ := not_forall.mp hh
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [tiltWeight, hi])

private lemma tsum_subtype_eq_tsum_prod_tiltWeight {N : ℕ} {X y : ℝ} (hX : 0 ≤ X) (hy : 0 < y)
    (P : (Fin N → ℕ × ℤ) → Prop) :
    ∑' h : {h : Fin N → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ P h},
      ENNReal.ofReal (holdListLaw h.1 * X ^ (∑ i, (h.1 i).1) * y ^ (∑ i, (h.1 i).2)) =
      ∑' h : Fin N → ℕ × ℤ, {h | P h}.indicator (fun h ↦ ∏ i, tiltWeight X y (h i)) h := by
  refine (tsum_subtype {h : Fin N → ℕ × ℤ | (∀ i, 1 ≤ (h i).1) ∧ P h}
    (fun h ↦ ENNReal.ofReal (holdListLaw h * X ^ (∑ i, (h i).1) * y ^ (∑ i, (h i).2)))).trans ?_
  refine tsum_congr fun h ↦ ?_
  simp only [Set.indicator, Set.mem_ofPred_eq, prod_tiltWeight hX hy]
  by_cases h1 : ∀ i, 1 ≤ (h i).1 <;> by_cases h2 : P h <;> simp [h1, h2]

/-- **Splitting off the tail of a tilted hold-list sum**, with `N = u + m` and the hold list
written as the concatenation `gk` of `g ∈ 𝒫^u` and `k ∈ 𝒫^m`. -/
theorem tsum_holdListLaw_tilt_append {u m : ℕ} {X y : ℝ} (hX : 0 ≤ X) (hy : 0 < y)
    (E : Set (Fin u → ℕ × ℤ)) :
    ∑' h : {h : Fin (u + m) → ℕ × ℤ //
        (∀ i, 1 ≤ (h i).1) ∧ Fin.take u (Nat.le_add_right u m) h ∈ E},
      ENNReal.ofReal (holdListLaw h.1 * X ^ (∑ i, (h.1 i).1) * y ^ (∑ i, (h.1 i).2)) =
      holdJointPgf X y ^ m *
        ∑' g : {g : Fin u → ℕ × ℤ // (∀ i, 1 ≤ (g i).1) ∧ g ∈ E},
          ENNReal.ofReal (holdListLaw g.1 * X ^ (∑ i, (g.1 i).1) * y ^ (∑ i, (g.1 i).2)) := by
  rw [tsum_subtype_eq_tsum_prod_tiltWeight hX hy, tsum_subtype_eq_tsum_prod_tiltWeight hX hy,
    ← tsum_tiltWeight, ← tsum_pi_fin_prod_ennreal_const, ← (Fin.appendEquiv u m).tsum_eq,
    ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
  refine tsum_congr fun g ↦ ?_
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun k ↦ ?_
  have htake : Fin.take u (Nat.le_add_right u m) (Fin.append g k) = g := by
    funext i
    simp [Fin.take]
  rw [show Fin.appendEquiv u m (g, k) = Fin.append g k from funext fun _ ↦ rfl]
  simp only [Set.indicator, Set.mem_ofPred_eq, htake, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right]
  split_ifs <;> simp_all [mul_comm]

/-- **Splitting off the tail of a tilted hold-list sum.** Let `X ≥ 0` and `y > 0` be real, let
`u ≤ N`, and let `E` be a set of tuples of length `u`. Then, in `[0, ∞]`,
`∑_{h ∈ 𝒫^N, (h_1, …, h_u) ∈ E} η^{⊗N}(h) X^{j(h_1 + ⋯ + h_N)} y^{l(h_1 + ⋯ + h_N)}
  = 𝖦(X, y)^{N - u} ∑_{g ∈ E ∩ 𝒫^u} η^{⊗u}(g) X^{j(g_1 + ⋯ + g_u)} y^{l(g_1 + ⋯ + g_u)}`. -/
@[collatz_pos_dens "lem_rn_list_tilt_split"]
theorem tsum_holdListLaw_tilt_take {u N : ℕ} (huN : u ≤ N) {X y : ℝ} (hX : 0 ≤ X) (hy : 0 < y)
    (E : Set (Fin u → ℕ × ℤ)) :
    ∑' h : {h : Fin N → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ Fin.take u huN h ∈ E},
      ENNReal.ofReal (holdListLaw h.1 * X ^ (∑ i, (h.1 i).1) * y ^ (∑ i, (h.1 i).2)) =
      holdJointPgf X y ^ (N - u) *
        ∑' g : {g : Fin u → ℕ × ℤ // (∀ i, 1 ≤ (g i).1) ∧ g ∈ E},
          ENNReal.ofReal (holdListLaw g.1 * X ^ (∑ i, (g.1 i).1) * y ^ (∑ i, (g.1 i).2)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le huN
  rw [Nat.add_sub_cancel_left]
  exact tsum_holdListLaw_tilt_append hX hy E

end CollatzPosDens
