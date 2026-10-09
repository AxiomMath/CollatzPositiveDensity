/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHoldList
public import CollatzPosDens.Renewal.RnHoldMass

/-!
# Marginals of hold lists

For `a, b ∈ ℕ` and `u ∈ 𝒫^a`, summing the hold-list weight `η^{⊗(a+b)}` of the concatenation
`uv` over all continuations `v ∈ 𝒫^b` recovers `η^{⊗a}(u)`:
`∑_{v ∈ 𝒫^b} η^{⊗(a+b)}(uv) = η^{⊗a}(u)`. Indeed `η^{⊗(a+b)}(uv) = η^{⊗a}(u) ∏_i η(v_i)`, and
the sum of `∏_i η(v_i)` over `𝒫^b` factorises as `(∑_{p ∈ 𝒫} η(p))^b = 1`, since `η` is a
probability distribution on `𝒫`.

## Main results

* `CollatzPosDens.hasSum_holdListLaw_append`: the series `v ↦ η^{⊗(a+b)}(uv)` over
  `v ∈ 𝒫^b` has sum `η^{⊗a}(u)`.
* `CollatzPosDens.tsum_holdListLaw_append`: `∑_{v ∈ 𝒫^b} η^{⊗(a+b)}(uv) = η^{⊗a}(u)`.
* `CollatzPosDens.hasSum_holdListLaw`, `CollatzPosDens.tsum_holdListLaw`: the case
  `a = 0`, i.e. `η^{⊗b}` has total mass `1` on `𝒫^b`.
* `CollatzPosDens.tsum_ofReal_holdListLaw`: the same total mass `1`, as a sum in `[0, ∞]`.

## Implementation notes

As in `holdListLaw`, a point is a pair `(j, l) : ℕ × ℤ` and `𝒫 = ℤ_{≥1} × ℤ` is the set of pairs
with `1 ≤ j`; accordingly `𝒫^b` is the set of `v : Fin b → ℕ × ℤ` with `1 ≤ j(v_i)` for every
`i`. The restriction matters: `η(0, l)` is the indicator of `l = 0`, not zero. The prefix `u` is
allowed to be any tuple `Fin a → ℕ × ℤ`, not only one in `𝒫^a`, and the concatenation `uv` is
`Fin.append u v`. For `a = 0` the prefix is the empty tuple, of weight `1` (`holdListLaw_zero`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- `η` has total mass `1` on `𝒫`, written as the pairs `(j, l) : ℕ × ℤ` with `1 ≤ j`. -/
private lemma hasSum_holdLaw_subtype :
    HasSum (fun p : {p : ℕ × ℤ // 1 ≤ p.1} ↦ holdLaw p.1.1 p.1.2) 1 := by
  rw [← natPointsEquiv.hasSum_iff]
  exact hasSum_holdLaw_bkPoints_succ

/-- **Marginal of a hold list.** For any prefix `u : Fin a → ℕ × ℤ` and `b ∈ ℕ`, the series
`v ↦ η^{⊗(a+b)}(uv)` over `v ∈ 𝒫^b` has sum `η^{⊗a}(u)`. -/
@[collatz_pos_dens "lem_rn_list_marginal"]
theorem hasSum_holdListLaw_append {a : ℕ} (u : Fin a → ℕ × ℤ) (b : ℕ) :
    HasSum (fun v : {v : Fin b → ℕ × ℤ // ∀ i, 1 ≤ (v i).1} ↦ holdListLaw (Fin.append u v.1))
      (holdListLaw u) := by
  have h := (hasSum_pi_fin_prod_of_nonneg hasSum_holdLaw_subtype
    (fun p ↦ holdLaw_nonneg _ _) b).mul_left (holdListLaw u)
  simp only [one_pow, mul_one] at h
  rw [← (Equiv.subtypePiEquivPi (α := Fin b) (p := fun _ (p : ℕ × ℤ) ↦ 1 ≤ p.1)).symm.hasSum_iff]
  convert h using 2 with w
  rw [Function.comp_apply, holdListLaw_append]
  simp [Equiv.subtypePiEquivPi, holdListLaw_def]

/-- **Marginal of a hold list.** For any prefix `u : Fin a → ℕ × ℤ` and `b ∈ ℕ`,
`∑_{v ∈ 𝒫^b} η^{⊗(a+b)}(uv) = η^{⊗a}(u)`. -/
@[collatz_pos_dens "lem_rn_list_marginal"]
theorem tsum_holdListLaw_append {a : ℕ} (u : Fin a → ℕ × ℤ) (b : ℕ) :
    ∑' v : {v : Fin b → ℕ × ℤ // ∀ i, 1 ≤ (v i).1}, holdListLaw (Fin.append u v.1) =
      holdListLaw u :=
  (hasSum_holdListLaw_append u b).tsum_eq

/-- The hold-list weight `η^{⊗b}` has total mass `1` on `𝒫^b`. -/
theorem hasSum_holdListLaw (b : ℕ) :
    HasSum (fun v : {v : Fin b → ℕ × ℤ // ∀ i, 1 ≤ (v i).1} ↦ holdListLaw v.1) 1 := by
  convert hasSum_holdListLaw_append (Fin.elim0 : Fin 0 → ℕ × ℤ) b using 1
  · funext v
    rw [holdListLaw_append, holdListLaw_zero, one_mul]
  · simp

/-- The hold-list weight `η^{⊗b}` has total mass `1` on `𝒫^b`: `∑_{v ∈ 𝒫^b} η^{⊗b}(v) = 1`. -/
theorem tsum_holdListLaw (b : ℕ) :
    ∑' v : {v : Fin b → ℕ × ℤ // ∀ i, 1 ≤ (v i).1}, holdListLaw v.1 = 1 :=
  (hasSum_holdListLaw b).tsum_eq

/-- The hold-list weight `η^{⊗b}` has total mass `1` on `𝒫^b`, as a sum in `[0, ∞]`. -/
theorem tsum_ofReal_holdListLaw (b : ℕ) :
    ∑' v : {v : Fin b → ℕ × ℤ // ∀ i, 1 ≤ (v i).1}, ENNReal.ofReal (holdListLaw v.1) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ holdListLaw_nonneg _)
    (hasSum_holdListLaw b).summable, tsum_holdListLaw, ENNReal.ofReal_one]

end CollatzPosDens
