/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.StoppingTrace.TrLipConst
public import CollatzPosDens.StoppingTrace.TrTreePolicy
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# The Lipschitz constant of a tree cost

Let `cut : ℕ → ℕ` and let `W` be a bounded policy. For `r, h ∈ ℕ` the number `L^{cut,W}_{r,h}` is
defined, for all `r` at once, by downward recursion on `h`:
`L^{cut,W}_{r,h} = 9^r 2^{-h} ∑_{c=3}^{cut(h)} ϖ(c) ℓ_c 2^{-c}
  + ∑_{c : (r,h,c) ∈ W} ϖ(c) L^{cut,W}_{r+1,h+c}`,
where `ϖ` is the Pascal law `CollatzPosDens.varpi` and `ℓ_c` the Lipschitz constant
`CollatzPosDens.trLipConst` of the capped packet factor. The recursion is well founded because
every `(r, h, c) ∈ W` has `c ≥ 2` and `h + c` bounded.

## Main definitions

* `CollatzPosDens.policyBound`: a bound `K` on `h + c` over the triples of a bounded policy.
* `CollatzPosDens.trTreeLip`: the constant `L^{cut,W}_{r,h}`.

## Main results

* `CollatzPosDens.trTreeLip_eq_finsum`: the defining recursion, with the second sum taken over
  the set `{c | (r, h, c) ∈ W}`.
* `CollatzPosDens.trTreeLip_eq_sum`: the defining recursion, with the second sum taken over any
  finite set containing every `c` with `(r, h, c) ∈ W`.
* `CollatzPosDens.trTreeLip_of_forall_notMem`: a node without children carries only its own term.
* `CollatzPosDens.trTreeLip_nonneg`: `0 ≤ L^{cut,W}_{r,h}`.

## Implementation notes

The continuation lengths `c` of a policy are natural numbers, cast to `ℤ` in `ϖ(c)`; the
first sum runs over the integer interval `[3, cut(h)]`. The recursion is by well-founded
recursion on `K + 1 - h`, where `K = CollatzPosDens.policyBound W`; the second sum is
restricted to the `c ≤ K` with `1 ≤ c` and `h + c ≤ K`, which for a bounded policy is no
restriction. For a set `W` that is not a bounded policy the value is unspecified.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Classical in
/-- A bound `K` such that every triple `(r, h, c)` of the bounded policy `W` satisfies
`h + c ≤ K` (and `0` if `W` is not a bounded policy). -/
noncomputable def policyBound (W : Set (ℕ × ℕ × ℕ)) : ℕ :=
  if hW : IsBoundedPolicy W then Classical.choose hW else 0

/-- Every triple `(r, h, c)` of a bounded policy satisfies `2 ≤ c` and
`h + c ≤ policyBound W`. -/
theorem IsBoundedPolicy.le_policyBound {W : Set (ℕ × ℕ × ℕ)} (hW : IsBoundedPolicy W)
    {p : ℕ × ℕ × ℕ} (hp : p ∈ W) : 2 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ policyBound W := by
  simp only [policyBound, hW, dite_true]
  exact Classical.choose_spec hW p hp

open Classical in
/-- The Lipschitz constant of a tree cost:
`L^{cut,W}_{r,h} = 9^r 2^{-h} ∑_{c=3}^{cut(h)} ϖ(c) ℓ_c 2^{-c}
  + ∑_{c : (r,h,c) ∈ W} ϖ(c) L^{cut,W}_{r+1,h+c}`, by downward recursion on `h`. -/
@[collatz_pos_dens "def_tr_tree_lip"]
noncomputable def trTreeLip (cut : ℕ → ℕ) (W : Set (ℕ × ℕ × ℕ)) (r h : ℕ) : ℝ :=
  (9 : ℝ) ^ r * (2 : ℝ) ^ (-(h : ℤ)) *
      ∑ c ∈ Finset.Icc (3 : ℤ) (cut h), varpi c * (trLipConst c : ℝ) * (2 : ℝ) ^ (-c) +
    ∑ c ∈ ((Finset.range (policyBound W + 1)).filter fun c =>
        (r, h, c) ∈ W ∧ 1 ≤ c ∧ h + c ≤ policyBound W).attach,
      varpi (c.1 : ℤ) * trTreeLip cut W (r + 1) (h + c.1)
termination_by policyBound W + 1 - h
decreasing_by
  have := (Finset.mem_filter.mp c.2).2
  omega

/-- The defining recursion of `trTreeLip`, with the second sum over any finite set `s` of
continuation lengths containing every `c` with `(r, h, c) ∈ W`. -/
theorem trTreeLip_eq_sum {cut : ℕ → ℕ} {W : Set (ℕ × ℕ × ℕ)} (hW : IsBoundedPolicy W)
    [DecidablePred (· ∈ W)] (r h : ℕ) {s : Finset ℕ} (hs : ∀ c, (r, h, c) ∈ W → c ∈ s) :
    trTreeLip cut W r h =
      (9 : ℝ) ^ r * (2 : ℝ) ^ (-(h : ℤ)) *
          ∑ c ∈ Finset.Icc (3 : ℤ) (cut h), varpi c * (trLipConst c : ℝ) * (2 : ℝ) ^ (-c) +
        ∑ c ∈ s.filter (fun c => (r, h, c) ∈ W),
          varpi (c : ℤ) * trTreeLip cut W (r + 1) (h + c) := by
  classical
  rw [trTreeLip]
  congr 1
  rw [Finset.sum_attach (f := fun c : ℕ => varpi (c : ℤ) * trTreeLip cut W (r + 1) (h + c))]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext c
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, hc, -⟩
    exact ⟨hs c hc, hc⟩
  · rintro ⟨-, hc⟩
    have := hW.le_policyBound hc
    simp only at this
    exact ⟨by omega, hc, by omega, this.2⟩

/-- The defining recursion of `trTreeLip`, with the second sum over the set of continuation
lengths `{c | (r, h, c) ∈ W}`. -/
theorem trTreeLip_eq_finsum {cut : ℕ → ℕ} {W : Set (ℕ × ℕ × ℕ)} (hW : IsBoundedPolicy W)
    (r h : ℕ) :
    trTreeLip cut W r h =
      (9 : ℝ) ^ r * (2 : ℝ) ^ (-(h : ℤ)) *
          ∑ c ∈ Finset.Icc (3 : ℤ) (cut h), varpi c * (trLipConst c : ℝ) * (2 : ℝ) ^ (-c) +
        ∑ᶠ c ∈ {c : ℕ | (r, h, c) ∈ W}, varpi (c : ℤ) * trTreeLip cut W (r + 1) (h + c) := by
  classical
  have hs : ∀ c, (r, h, c) ∈ W → c ∈ Finset.range (policyBound W + 1) := fun c hc => by
    have := (hW.le_policyBound hc).2
    simp only at this
    exact Finset.mem_range.mpr (by omega)
  have hfin : {c : ℕ | (r, h, c) ∈ W}.Finite :=
    (Finset.range (policyBound W + 1)).finite_toSet.subset fun c hc => hs c hc
  rw [trTreeLip_eq_sum hW r h hs, finsum_mem_eq_finite_toFinset_sum _ hfin]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext c
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨hs c h, h⟩⟩

/-- A node `(r, h)` without children in `W` carries only its own term. -/
theorem trTreeLip_of_forall_notMem {cut : ℕ → ℕ} {W : Set (ℕ × ℕ × ℕ)}
    (hW : IsBoundedPolicy W) {r h : ℕ} (hrh : ∀ c, (r, h, c) ∉ W) :
    trTreeLip cut W r h =
      (9 : ℝ) ^ r * (2 : ℝ) ^ (-(h : ℤ)) *
        ∑ c ∈ Finset.Icc (3 : ℤ) (cut h), varpi c * (trLipConst c : ℝ) * (2 : ℝ) ^ (-c) := by
  classical
  rw [trTreeLip_eq_sum hW r h (s := ∅) fun c hc => (hrh c hc).elim]
  simp

/-- The Lipschitz constant of a tree cost is nonnegative. -/
theorem trTreeLip_nonneg (cut : ℕ → ℕ) (W : Set (ℕ × ℕ × ℕ)) (r h : ℕ) :
    0 ≤ trTreeLip cut W r h := by
  classical
  suffices ∀ n r h, policyBound W + 1 - h = n → 0 ≤ trTreeLip cut W r h from this _ r h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r h hn
    rw [trTreeLip]
    refine add_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun c _ => ?_))
      (Finset.sum_nonneg fun c _ => mul_nonneg (varpi_nonneg _) ?_)
    · have := trLipConst_nonneg c
      have : (0 : ℝ) ≤ (trLipConst c : ℝ) := by exact_mod_cast this
      have := varpi_nonneg c
      positivity
    · have := (Finset.mem_filter.mp c.2).2
      exact ih _ (by omega) _ _ rfl

end CollatzPosDens
