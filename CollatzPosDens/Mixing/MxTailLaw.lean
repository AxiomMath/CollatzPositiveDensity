/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.RefLaw
public import CollatzPosDens.Transfer.FxRefLawTotal

/-!
# The tail law

For `n, k, l ∈ ℕ` with `k < n` and `x ∈ G_n = ℤ/3^nℤ`, the *tail law* is the pushforward of the
reference law `μ_{n-k-1}` under the affine map `z ↦ [3^{k+1} 2^{-l}]_n z̃` from `G_{n-k-1}` to
`G_n`, where `z̃` is the least nonnegative representative of `z`:
$$\mathrm{Tl}_{n,k,l}(x) = \sum_{z \in G_{n-k-1},\ [3^{k+1}2^{-l}]_n\,\tilde z = x}
  \mu_{n-k-1}(z).$$

## Main definitions

* `CollatzPosDens.tailLawCoeff n k l`: the residue `[3^{k+1} 2^{-l}]_n ∈ G_n`.
* `CollatzPosDens.tailLaw n k l`: the weights `Tl_{n,k,l} : G_n → [0, ∞]`.

## Main results

* `CollatzPosDens.tailLawCoeff_eq`: `[3^{k+1} 2^{-l}]_n = 3^{k+1} · (2⁻¹)^l` in `G_n`.
* `CollatzPosDens.tailLaw_eq_sum_ite`: the defining sum, written over all of `G_{n-k-1}`.
* `CollatzPosDens.sum_tailLaw`: the tail law has the same total mass as `μ_{n-k-1}`.
* `CollatzPosDens.sum_tailLaw_eq_one`: the tail law has total mass `1`.

## Implementation notes

The weights take values in `ℝ≥0∞`, like the reference law. The definition makes sense for all
`n, k, l`, so the hypothesis `k < n` of the source is not imposed; it belongs to the lemmas that
use it. The coefficient `[3^{k+1} 2^{-l}]_n` is the reduction `dyadicRed n` of the dyadic rational
`3^{k+1} / 2^l`.

## References

* [Mazur, *Collatz positive density*], §13.1.
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

/-- The residue `[3^{k+1} 2^{-l}]_n ∈ G_n`, the reduction modulo `3^n` of the dyadic rational
`3^{k+1} / 2^l`. -/
noncomputable def tailLawCoeff (n k l : ℕ) : ResidueGroup n :=
  dyadicRed n ⟨((3 ^ (k + 1) : ℤ) : ℚ) / 2 ^ l, intCast_div_two_pow_mem _ l⟩

/-- The coefficient computed in `G_n`: `[3^{k+1} 2^{-l}]_n = 3^{k+1} · (2⁻¹)^l`. -/
theorem tailLawCoeff_eq (n k l : ℕ) : tailLawCoeff n k l = 3 ^ (k + 1) * 2⁻¹ ^ l := by
  rw [tailLawCoeff, dyadicRed_div_two_pow]
  push_cast
  rfl

/-- The tail law `Tl_{n,k,l}(x) = ∑_{z ∈ G_{n-k-1}, [3^{k+1} 2^{-l}]_n z̃ = x} μ_{n-k-1}(z)`, where
`z̃` is the least nonnegative representative of `z`. -/
@[collatz_pos_dens "def_mx_tail_law"]
noncomputable def tailLaw (n k l : ℕ) (x : ResidueGroup n) : ℝ≥0∞ :=
  ∑ z ∈ Finset.univ.filter
      (fun z : ResidueGroup (n - k - 1) => tailLawCoeff n k l * (z.val : ResidueGroup n) = x),
    refLaw (n - k - 1) z

/-- Unfolding lemma for `tailLaw`, with the coefficient written as `3^{k+1} · (2⁻¹)^l`. -/
theorem tailLaw_def (n k l : ℕ) (x : ResidueGroup n) :
    tailLaw n k l x = ∑ z ∈ Finset.univ.filter (fun z : ResidueGroup (n - k - 1) =>
        3 ^ (k + 1) * 2⁻¹ ^ l * (z.val : ResidueGroup n) = x), refLaw (n - k - 1) z := by
  simp only [tailLaw, tailLawCoeff_eq]

/-- The tail law as a sum over all of `G_{n-k-1}` with an indicator of the fibre. -/
theorem tailLaw_eq_sum_ite (n k l : ℕ) (x : ResidueGroup n) :
    tailLaw n k l x = ∑ z : ResidueGroup (n - k - 1),
      if tailLawCoeff n k l * (z.val : ResidueGroup n) = x then refLaw (n - k - 1) z else 0 := by
  rw [tailLaw, Finset.sum_filter]

/-- The tail law is a pushforward of `μ_{n-k-1}`, so its total mass is that of `μ_{n-k-1}`. -/
theorem sum_tailLaw (n k l : ℕ) : ∑ x, tailLaw n k l x = ∑ z, refLaw (n - k - 1) z := by
  simp only [tailLaw]
  exact Finset.sum_fiberwise Finset.univ
    (fun z : ResidueGroup (n - k - 1) => tailLawCoeff n k l * (z.val : ResidueGroup n)) _

/-- The tail law is a probability distribution: `∑_x Tl_{n,k,l}(x) = 1`. -/
theorem sum_tailLaw_eq_one (n k l : ℕ) : ∑ x, tailLaw n k l x = 1 :=
  (sum_tailLaw n k l).trans (sum_refLaw _)

/-- Each value of the tail law is finite. -/
theorem tailLaw_ne_top (n k l : ℕ) (x : ResidueGroup n) : tailLaw n k l x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top <|
    sum_tailLaw_eq_one n k l ▸ Finset.single_le_sum_of_canonicallyOrdered (Finset.mem_univ x)

end CollatzPosDens
