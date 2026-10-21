/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05JointLaw
public import CollatzPosDens.Seed.S05OfflawRecursion

/-!
# The one-letter recursion of the joint offset law

Splitting off the first letter of a word, `u = (a) v` with `a ≥ 1`, gives
`off(u) = 2^{-a} (1 + 3 off(v))` and `A(u) = a + A(v)`, so `off(u) ≤ x` if and only if
`off(v) ≤ (2^a x - 1)/3`. For `q ≥ 1` the prefix residue satisfies `pr_q(u) = r` if and only if
`3 ∣ 2^a r̃ - 1` and `pr_{q-1}(v) = dn_a(r)`. Summing the geometric weights first over `v` gives,
for all integers `D ≥ q ≥ 1`, every `r ∈ G_q` and every real `x`,
$$\mathsf F^{\mathrm{jt}}_{D,q}(r,x) = \sum_{a \ge 1,\ 3 \mid 2^a \tilde r - 1} 2^{-a}\,
  \mathsf F^{\mathrm{jt}}_{D-1,q-1}\Bigl(\mathrm{dn}_a(r), \frac{2^a x - 1}{3}\Bigr)$$
in `[0, ∞]`.

## Main results

* `CollatzPosDens.jointLaw_eq_tsum`: the one-letter recursion of the joint offset law.

## Implementation notes

The sum over the letters `a ≥ 1` with `3 ∣ 2^a r̃ - 1` is a `tsum` over `ℕ+` in `ℝ≥0∞` whose
terms vanish when the divisibility (in `ℤ`) fails. The recursion holds under `1 ≤ q` and
`1 ≤ D` alone, both of which follow from `D ≥ q ≥ 1`.

## References

* [Mazur, *Collatz positive density*], §16.6.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- **One-letter recursion of the joint offset law**: for `q ≥ 1`, `D ≥ 1` (in particular for
`D ≥ q ≥ 1`), every `r ∈ G_q` and every real `x`,
`𝖥^{jt}_{D,q}(r, x) = ∑_{a ≥ 1, 3 ∣ 2^a r̃ - 1} 2^{-a} 𝖥^{jt}_{D-1,q-1}(dn_a(r), (2^a x - 1)/3)`,
an identity in `[0, ∞]`. -/
@[collatz_pos_dens "lem_s05_joint_recursion"]
theorem jointLaw_eq_tsum {D q : ℕ} (hq : 1 ≤ q) (hD : 1 ≤ D) (r : ResidueGroup q) (x : ℝ) :
    jointLaw D q r x =
      ∑' a : ℕ+, if (3 : ℤ) ∣ 2 ^ (a : ℕ) * (r.val : ℤ) - 1 then
        (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * jointLaw (D - 1) (q - 1) (childResidue a r)
          ((2 ^ (a : ℕ) * x - 1) / 3)
      else 0 := by
  set S : Set Word := {u : Word | u.length = D ∧ (off u : ℝ) ≤ x ∧ prefixResidue q u = r}
    with hS
  set f : Word → ℝ≥0∞ := S.indicator Word.massWeight with hf
  have hinj : Function.Injective (fun p : ℕ+ × Word => p.1 :: p.2) := by
    rintro ⟨a, v⟩ ⟨b, w⟩ h
    simp only [List.cons.injEq] at h
    rw [h.1, h.2]
  have hsupp : Function.support f ⊆ Set.range (fun p : ℕ+ × Word => p.1 :: p.2) := by
    intro u hu
    have hu' : u ∈ S := by
      by_contra hn
      exact hu (Set.indicator_of_notMem hn _)
    match u, hu' with
    | [], h => exact absurd h.1 (by simp only [List.length_nil]; omega)
    | a :: v, _ => exact ⟨(a, v), rfl⟩
  rw [jointLaw_def, geomMass_eq_tsum_indicator, ← hinj.tsum_eq hsupp]
  rw [ENNReal.tsum_prod (f := fun a v => f (a :: v))]
  refine tsum_congr fun a => ?_
  have hlen : ∀ v : Word, (a :: v).length = D ↔ v.length = D - 1 := fun v => by
    simp only [List.length_cons]
    omega
  by_cases hc : (3 : ℤ) ∣ 2 ^ (a : ℕ) * (r.val : ℤ) - 1
  · simp only [hc, ↓reduceIte]
    rw [jointLaw_def, geomMass_eq_tsum_indicator, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun v => ?_
    simp only [hf, hS, Set.indicator_apply, Set.mem_ofPred_eq, hlen, off_cons_le_iff,
      prefixResidue_cons_eq_iff hq, hc, true_and, Word.massWeight, Word.valSum_cons, pow_add]
    split_ifs <;> simp
  · simp only [hc, ↓reduceIte]
    refine ENNReal.tsum_eq_zero.2 fun v => ?_
    simp only [hf, hS, Set.indicator_apply, Set.mem_ofPred_eq, prefixResidue_cons_eq_iff hq, hc,
      false_and, and_false, ↓reduceIte]

end CollatzPosDens
