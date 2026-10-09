/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Lb
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.Recipe.NValue
public import CollatzPosDens.Seed.Pullback
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.Transfer.LiftedTransfer
public import CollatzPosDens.Transfer.Reduction
public import CollatzPosDens.Transfer.TransferNonunit

/-!
# The pulled-back density vanishes on nonunits

The pulled-back reference density `Ψ` on `G_{q_*}` vanishes at every `y ∈ G_{q_*}` with
`3 ∣ y`.

Indeed `N_* ≥ 1`, and every word of a central family `𝒞(b, K)` has length `> ℓ_b ≥ 0`, so
each concatenated word `ŵ(t) = w_0 ⋯ w_{N_*-1}` of a selected tuple `t ∈ 𝔗_{N_*}` is nonempty.
A lifted transfer along a nonempty word is a transfer evaluated at a reduction of `y`, which is
again a nonunit, so each summand of `Ψ` vanishes at `y` by the vanishing of transfers on
nonunits.

## Main results

* `CollatzPosDens.pullbackDensity_length_concatWord_pos`: for `N ≥ 1` and `t ∈ 𝔗_N`,
  the concatenated word `ŵ(t)` is nonempty.
* `CollatzPosDens.pullbackDensityOf_eq_zero_of_three_dvd`: for `N ≥ 1` and any level `q`,
  `pullbackDensityOf N q y = 0` whenever `3 ∣ y`.
* `CollatzPosDens.pullbackDensity_eq_zero_of_three_dvd`: `Ψ(y) = 0` whenever `3 ∣ y`.

## Implementation notes

A residue `y ∈ G_q` is divisible by `3` when `3` divides its least nonnegative representative
`y.val`. Since `3 ∣ 3^q` for `q ≥ 1`, this does not depend on the choice of representative, and
it says exactly that `y` is not a unit in the sense of `CollatzPosDens.IsResidueUnit`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For `N ≥ 1`, the concatenated word `ŵ(t)` of a selected central tuple `t ∈ 𝔗_N` is
nonempty. -/
theorem pullbackDensity_length_concatWord_pos {N : ℕ} (hN : 0 < N) {t : Fin N → Word}
    (ht : t ∈ selectedTuples N) : 0 < (concatWord t).length := by
  have h0 : t ⟨0, hN⟩ ≠ [] := ne_nil_of_mem_firstCrossing
    (centralFamily_subset_firstCrossing _ _ (selectedTuples_mem_centralFamily ht ⟨0, hN⟩))
  rw [List.length_pos_iff, concatWord_def, Ne, List.flatten_eq_nil_iff]
  exact fun h => h0 (h _ (List.mem_ofFn.2 ⟨_, rfl⟩))

/-- For `N ≥ 1` and any level `q`, the sum `pullbackDensityOf N q` vanishes at every
`y ∈ G_q` with `3 ∣ y`. -/
theorem pullbackDensityOf_eq_zero_of_three_dvd {N q : ℕ} (hN : 0 < N) {y : ResidueGroup q}
    (hy : 3 ∣ y.val) : pullbackDensityOf N q y = 0 := by
  rw [pullbackDensityOf_apply]
  refine sum_eq_zero fun t ht => ?_
  split_ifs with h
  · have hlen := pullbackDensity_length_concatWord_pos hN
      ((selectedTuples_finite N).mem_toFinset.1 ht)
    rw [liftedTransfer_apply]
    refine transfer_eq_zero_of_not_isResidueUnit hlen _ ?_
    rw [IsResidueUnit, not_not, val_residueReduction]
    refine (Nat.dvd_mod_iff ?_).2 hy
    exact dvd_pow_self 3 (by omega)
  · rfl

/-- **The pulled-back density vanishes on nonunits.** `Ψ(y) = 0` for every `y ∈ G_{q_*}`
with `3 ∣ y`. -/
@[collatz_pos_dens "lem_pullback_nonunit"]
theorem pullbackDensity_eq_zero_of_three_dvd {y : ResidueGroup conductor}
    (hy : 3 ∣ y.val) : pullbackDensity y = 0 :=
  pullbackDensityOf_eq_zero_of_three_dvd (by rw [generationThreshold_eq]; norm_num) hy

end CollatzPosDens
