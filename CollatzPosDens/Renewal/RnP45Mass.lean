/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnFpRaw
public import CollatzPosDens.Renewal.RnP45
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Renewal.RnFpRawLem

/-!
# The closing exit mass is a first-passage mass

For every `s ∈ ℕ`,
`∑_{r=1}^{⌊(5s+16)/16⌋} ∑_{O=1}^{4} F_s(r, s + O) = p₄₅(s)`,
where `F_s` is the first-passage law and `p₄₅` the closing exit mass.

For `r ≥ 1` and a target `ℓ ≤ s + 4`, every word `c ∈ ℤ^r` with letters at least `2`, last letter
in `{4, 5}` and letter sum `ℓ` has all its proper prefix sums at most `ℓ - c_r ≤ s`, so the prefix
condition of the raw first-passage words `𝒟_s(r, ℓ)` holds automatically. Splitting by the last
letter then gives `∑_{c ∈ 𝒟_s(r, ℓ)} ∏ ϖ(c_i) = ϖ(4) 𝖱(r - 1, ℓ - 4) + ϖ(5) 𝖱(r - 1, ℓ - 5)`, and
the raw-word form of the first-passage law turns this into the claim.

## Main results

* `CollatzPosDens.sum_firstPassageWords_eq_of_le`: for `ℓ ≤ s + 4`,
  `∑_{c ∈ 𝒟_s(r + 1, ℓ)} ∏ ϖ(c_i) = ∑_{e=4}^{5} ϖ(e) 𝖱(r, ℓ - e)`.
* `CollatzPosDens.sum_firstPassageLaw_eq_p45`: the identity
  `∑_{r=1}^{⌊(5s+16)/16⌋} ∑_{O=1}^{4} F_s(r, s + O) = p₄₅(s)`.

## Implementation notes

The first-passage law takes an integer level and a point of `ℤ × ℤ`; the level `s` and the length
`r` are cast from `ℕ`. The overshoot `O` ranges over `Icc (1 : ℤ) 4`, matching the definition of
`p₄₅`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For a target `ℓ ≤ s + 4`, the prefix condition of `𝒟_s(r + 1, ℓ)` is automatic, and splitting
by the last letter gives `∑_{c ∈ 𝒟_s(r + 1, ℓ)} ∏ ϖ(c_i) = ∑_{e=4}^{5} ϖ(e) 𝖱(r, ℓ - e)`. -/
theorem sum_firstPassageWords_eq_of_le (s r : ℕ) (ℓ : ℤ) (hℓ : ℓ ≤ s + 4) :
    ∑ c ∈ firstPassageWords s (r + 1) ℓ, ∏ i, varpi (c i) =
      ∑ e ∈ Icc (4 : ℤ) 5, varpi e * rawMass r (ℓ - e) := by
  simp only [rawMass, mul_sum]
  rw [sum_sigma']
  refine sum_nbij' (fun c ↦ ⟨c (Fin.last r), Fin.init c⟩) (fun x ↦ Fin.snoc x.2 x.1)
    ?_ ?_ ?_ ?_ ?_
  · intro c hc
    have hlast := firstPassageWords_last_mem hc
    rw [mem_firstPassageWords, Fin.sum_univ_castSucc] at hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hlast
    simp only [mem_sigma, mem_Icc, mem_rawWords]
    refine ⟨by omega, fun i ↦ hc.1 _, ?_⟩
    simp only [Fin.init]; linarith [hc.2.2.1]
  · rintro ⟨e, d⟩ hx
    simp only [mem_sigma, mem_Icc, mem_rawWords] at hx
    obtain ⟨⟨he4, he5⟩, hd2, hds⟩ := hx
    dsimp only
    rw [mem_firstPassageWords]
    have h2 : ∀ i, 2 ≤ (Fin.snoc d e : Fin (r + 1) → ℤ) i := by
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp; omega
      · simpa using hd2 j
    have hsum : ∑ i, (Fin.snoc d e : Fin (r + 1) → ℤ) i = ℓ := by
      rw [Fin.sum_univ_castSucc]; simp [hds]
    refine ⟨h2, fun i hi ↦ ?_, hsum, fun i hi _ ↦ ?_⟩
    · have : i = Fin.last r := Fin.ext (by simp; omega)
      subst this
      simp only [Fin.snoc_last, Set.mem_insert_iff, Set.mem_singleton_iff]; omega
    · have hsub : Iic i ⊆ univ.erase (Fin.last r) := fun j hj ↦ by
        simp only [mem_Iic] at hj
        simp only [mem_erase, mem_univ, and_true, ne_eq]
        intro h; subst h
        have := Fin.le_iff_val_le_val.1 hj
        simp at this; omega
      have hle := sum_le_sum_of_subset_of_nonneg hsub
        (f := (Fin.snoc d e : Fin (r + 1) → ℤ)) fun j _ _ ↦ by linarith [h2 j]
      have hsplit := add_sum_erase univ (Fin.snoc d e : Fin (r + 1) → ℤ) (mem_univ (Fin.last r))
      rw [hsum, Fin.snoc_last] at hsplit
      omega
  · intro c _
    simp
  · rintro ⟨e, d⟩ _
    simp
  · intro c _
    simp [Fin.prod_univ_castSucc, Fin.init, mul_comm]

/-- **The closing exit mass is a first-passage mass.** For every `s ∈ ℕ`,
`∑_{r=1}^{⌊(5s+16)/16⌋} ∑_{O=1}^{4} F_s(r, s + O) = p₄₅(s)`. -/
@[collatz_pos_dens "lem_rn_p45_mass"]
theorem sum_firstPassageLaw_eq_p45 (s : ℕ) :
    ∑ r ∈ Icc 1 ((5 * s + 16) / 16), ∑ O ∈ Icc (1 : ℤ) 4,
      firstPassageLaw s ((r : ℤ), (s : ℤ) + O) = p45 s := by
  calc _ = ∑ r ∈ Icc 1 ((5 * s + 16) / 16), ∑ O ∈ Icc (1 : ℤ) 4, ∑ e ∈ Icc (4 : ℤ) 5,
        varpi e * rawMass (r - 1) ((s : ℤ) + O - e) := by
        refine sum_congr rfl fun r hr ↦ sum_congr rfl fun O hO ↦ ?_
        simp only [mem_Icc] at hO hr
        obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        rw [firstPassageLaw_eq_sum_firstPassageWords s (k + 1) (by omega) _ (by omega),
          sum_firstPassageWords_eq_of_le s k _ (by omega)]
        simp
    _ = p45 s := by
        rw [p45]
        simp_rw [mul_sum]
        rw [sum_congr rfl fun r _ ↦ sum_comm, sum_comm]
        exact sum_congr rfl fun e _ ↦ sum_comm

end CollatzPosDens
