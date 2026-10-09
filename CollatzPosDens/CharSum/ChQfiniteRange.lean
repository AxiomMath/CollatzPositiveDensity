/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQfinite
public import CollatzPosDens.CharSum.ChInternalWeight
public import CollatzPosDens.CharSum.ChRaw3Factor
public import CollatzPosDens.CharSum.ChWhiteFactor
public import CollatzPosDens.Transfer.Kappa
public import CollatzPosDens.Transfer.Z
public import CollatzPosDens.CharSum.ChBlockListMass

/-!
# The range of the finite-horizon white products

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For every horizon `K ∈ ℕ` and every
point `p`, the series defining the finite-horizon white product `Q^{(K)}(p)` converges and
`0 ≤ Q^{(K)}(p) ≤ 1`. Indeed, the white factor `w` and the raw-three factor `w₃` take values in
`(0, 1]`, hence so does the internal weight `I`, and every product of `w`- and `I`-factors lies
in `(0, 1]`. The weights `∏_k bw(βᵏ)` are nonnegative and sum to `1` over `𝔅^K`, so the
defining series is dominated termwise by a convergent series of sum `1`, and `Q^{(K)}(p)` is an
average of numbers in `[0, 1]`.

## Main results

* `CollatzPosDens.chQFinite_le_one`: `Q^{(K)}(p) ≤ 1`.
* `CollatzPosDens.chQFinite_mem_Icc`: `Q^{(K)}(p) ∈ [0, 1]`.
* `CollatzPosDens.chQFinite_range`: the defining series converges and
  `0 ≤ Q^{(K)}(p) ≤ 1`.

## Implementation notes

The base point `p` ranges over all of `ℤ × ℤ`, and the threshold `ε` is an arbitrary real
number; no restriction on `p` is needed. The convergence of the defining series is stated for
its summand written out exactly as in `CollatzPosDens.chQFinite`; it is definitionally
`CollatzPosDens.chQFiniteTerm`.

## References

* [Mazur, *Collatz positive density*], §7.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The finite-horizon white product is at most `1`: `Q^{(K)}(p) ≤ 1`. -/
theorem chQFinite_le_one (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ) (p : ℤ × ℤ) :
    chQFinite n ξ ε K p ≤ 1 := by
  have hη := hasSum_prod_chBlockWeight K
  rw [chQFinite_eq_tsum, ← hη.tsum_eq]
  exact Summable.tsum_le_tsum (chQFiniteTerm_le n ξ ε K p)
    (summable_chQFiniteTerm n ξ ε K p) hη.summable

/-- The finite-horizon white product lies in `[0, 1]`. -/
theorem chQFinite_mem_Icc (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ) (p : ℤ × ℤ) :
    chQFinite n ξ ε K p ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨chQFinite_nonneg n ξ ε K p, chQFinite_le_one n ξ ε K p⟩

/-- **Range of the finite-horizon products.** For every `K ∈ ℕ` and every point `p`, the series
defining `Q^{(K)}(p)` converges and `0 ≤ Q^{(K)}(p) ≤ 1`. -/
@[collatz_pos_dens "lem_ch_Qfinite_range"]
theorem chQFinite_range (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ) (p : ℤ × ℤ) :
    Summable (fun β : Fin K → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)} ↦
      (∏ k, chBlockWeight (β k)) *
        (∏ i ∈ Finset.range (K + 1),
          chWhiteFactor n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) i)) *
        ∏ k : Fin K,
          chInternalWeight n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) k) (β k)) ∧
      0 ≤ chQFinite n ξ ε K p ∧ chQFinite n ξ ε K p ≤ 1 :=
  ⟨summable_chQFiniteTerm n ξ ε K p, chQFinite_nonneg n ξ ε K p, chQFinite_le_one n ξ ε K p⟩

end CollatzPosDens
