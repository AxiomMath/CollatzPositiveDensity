/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.StoppingTrace.TrAtoms
public import CollatzPosDens.StoppingTrace.TrListWeight

/-!
# The fresh law after a first passage

For `n ≥ 1`, an entry point `e ∈ 𝒫` and a level `g ∈ ℕ`, the *fresh law* is the weight
`μ_{e,g}((r, ℓ), β) = F_g(r, ℓ) · bw^⊗(β)` on the fresh atoms `a = ((r, ℓ), β) ∈ 𝒜_n`: a first
passage over level `g` landing at the displacement `(r, ℓ)`, followed by the `⌊n/2⌋` blocks of
`β`, weighted independently by the block weight. It does not depend on `e`.

## Main definitions

* `CollatzPosDens.trFreshLaw`: the fresh law `μ_{e,g}`.

## Main results

* `CollatzPosDens.trFreshLaw_mk`: `μ_{e,g}((r, ℓ), β) = F_g(r, ℓ) · bw^⊗(β)`.
* `CollatzPosDens.trFreshLaw_nonneg`: `μ_{e,g} ≥ 0`, so it takes values in `[0, ∞)`.
* `CollatzPosDens.trFreshLaw_indep_entry`: `μ_{e,g}` does not depend on `e`.
* `CollatzPosDens.summable_trFreshLaw_of_tsum_ofReal_ne_top`: `μ_{e,g}` is summable on a set
  of atoms on which its sum in `[0, ∞]` is finite.

## Implementation notes

The fresh atoms `𝒜_n = trAtoms n` form a subset of `(ℕ × ℤ) × List (List ℤ × ℤ)`, cut out by the
length `⌊n/2⌋` of the block list and the condition that every closing letter lies in `{4, 5}`. The
fresh law is defined by the same formula on the whole ambient type; its restriction to `𝒜_n` is
`μ_{e,g}`, and sums over `𝒜_n` range over the subtype `trAtoms n`.
The law is real-valued, like `F_g` and `bw^⊗`; that it lands in `[0, ∞)` is `trFreshLaw_nonneg`.
The level `g ∈ ℕ` is read in `ℤ` for `F_g`, whose level ranges over `ℤ`. The entry point `e` is a
point of `ℤ × ℤ` and an explicit argument on which the law does not depend; the hypotheses `n ≥ 1`
and `e ∈ 𝒫` play no role in the definition and are dropped.

## References

* [Mazur, *Collatz positive density*], §9.8.
-/

@[expose] public section

namespace CollatzPosDens

/-- The fresh law `μ_{e,g}((r, ℓ), β) = F_g(r, ℓ) · bw^⊗(β)` on the fresh atoms `𝒜_n`
(defined by the same formula on all of `(ℕ × ℤ) × List (List ℤ × ℤ)`). It does not depend on the
entry point `e`. -/
@[collatz_pos_dens "def_tr_fresh_law"]
noncomputable def trFreshLaw (_n : ℕ) (_e : ℤ × ℤ) (g : ℕ)
    (a : (ℕ × ℤ) × List (List ℤ × ℤ)) : ℝ :=
  firstPassageLaw g ((a.1.1 : ℤ), a.1.2) * trListWeight a.2

/-- The fresh law at an atom `a` is the first-passage law at its displacement times the block
weight of its block list. -/
lemma trFreshLaw_def (n : ℕ) (e : ℤ × ℤ) (g : ℕ) (a : (ℕ × ℤ) × List (List ℤ × ℤ)) :
    trFreshLaw n e g a = firstPassageLaw g ((a.1.1 : ℤ), a.1.2) * trListWeight a.2 :=
  rfl

/-- The fresh law at an atom written `((r, ℓ), β)`. -/
@[simp]
lemma trFreshLaw_mk (n : ℕ) (e : ℤ × ℤ) (g r : ℕ) (ℓ : ℤ) (β : List (List ℤ × ℤ)) :
    trFreshLaw n e g ((r, ℓ), β) = firstPassageLaw g ((r : ℤ), ℓ) * trListWeight β :=
  rfl

/-- The fresh law is nonnegative. -/
lemma trFreshLaw_nonneg (n : ℕ) (e : ℤ × ℤ) (g : ℕ) (a : (ℕ × ℤ) × List (List ℤ × ℤ)) :
    0 ≤ trFreshLaw n e g a :=
  mul_nonneg (firstPassageLaw_nonneg _ _) (trListWeight_nonneg _)

/-- The fresh law does not depend on the entry point. -/
lemma trFreshLaw_indep_entry (n : ℕ) (e e' : ℤ × ℤ) (g : ℕ) :
    trFreshLaw n e g = trFreshLaw n e' g :=
  rfl

/-- The fresh law does not depend on `n`: only its domain `𝒜_n` does. -/
lemma trFreshLaw_indep_n (n n' : ℕ) (e : ℤ × ℤ) (g : ℕ) :
    trFreshLaw n e g = trFreshLaw n' e g :=
  rfl

/-- The fresh law with an empty block list is the first-passage law. -/
lemma trFreshLaw_nil (n : ℕ) (e : ℤ × ℤ) (g r : ℕ) (ℓ : ℤ) :
    trFreshLaw n e g ((r, ℓ), []) = firstPassageLaw g ((r : ℤ), ℓ) := by
  simp

/-- The fresh law is summable on any set of atoms on which its sum in `[0, ∞]` is finite. -/
theorem summable_trFreshLaw_of_tsum_ofReal_ne_top {n : ℕ} {e : ℤ × ℤ} {g : ℕ}
    {S : Set ((ℕ × ℤ) × List (List ℤ × ℤ))}
    (h : ∑' a : S, ENNReal.ofReal (trFreshLaw n e g a) ≠ ⊤) :
    Summable fun a : S ↦ trFreshLaw n e g a :=
  (ENNReal.summable_toReal h).congr fun _ ↦ ENNReal.toReal_ofReal (trFreshLaw_nonneg _ _ _ _)

end CollatzPosDens
