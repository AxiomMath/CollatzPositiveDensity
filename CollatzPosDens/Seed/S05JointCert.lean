/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05JointContrib

/-!
# Joint certificates

Let `g = (g_0, …, g_6198)` be an offset-law table. A family `𝖸 = (𝖸_q)_{1 ≤ q ≤ 8}` of tables
`𝖸_q : G_q × {0, …, 6198} → ℕ` is a *joint certificate over `g`* if every entry is bounded by
the sum of its joint contributions over the letters `1 ≤ a ≤ 60`:
$$\mathsf Y_q(r, k) \le \sum_{a=1}^{60} c^{\mathrm{jt}}_{g,\mathsf Y}(q, r, k, a)
  \qquad (1 \le q \le 8,\ 0 \le k \le 6198,\ r \in G_q).$$

## Main definitions

* `CollatzPosDens.IsJointCert g 𝖸`: `𝖸` is a joint certificate over `g`.

## Main results

* `CollatzPosDens.isJointCert_iff_of_ne_zero`: the condition need only be checked at the
  nonzero entries of `𝖸`, since a zero entry satisfies it trivially.

## Implementation notes

The family `𝖸` is a function of every level `q ∈ ℕ`, as for `CollatzPosDens.jointContrib`;
the condition constrains only the levels `1 ≤ q ≤ 8`, and the grid index ranges over
`Fin 6199`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- **Joint certificate over `g`**: a family `𝖸 = (𝖸_q)` of tables
`𝖸_q : G_q × {0, …, 6198} → ℕ` with `𝖸_q(r, k) ≤ ∑_{a=1}^{60} c^{jt}_{g,𝖸}(q, r, k, a)` for all
`1 ≤ q ≤ 8`, `0 ≤ k ≤ 6198` and `r ∈ G_q`. -/
@[collatz_pos_dens "def_s05_joint_cert"]
def IsJointCert (g : Fin 6199 → ℕ) (Y : (q : ℕ) → ResidueGroup q → Fin 6199 → ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → q ≤ 8 → ∀ k : Fin 6199, ∀ r : ResidueGroup q,
    Y q r k ≤ ∑ a ∈ Icc 1 60, jointContrib g Y q r k a

/-- `IsJointCert g 𝖸` holds iff `𝖸_q(r, k) ≤ ∑_{a=1}^{60} c^{jt}_{g,𝖸}(q, r, k, a)` for all
`1 ≤ q ≤ 8`, `0 ≤ k ≤ 6198` and `r ∈ G_q`. -/
theorem isJointCert_def (g : Fin 6199 → ℕ) (Y : (q : ℕ) → ResidueGroup q → Fin 6199 → ℕ) :
    IsJointCert g Y ↔ ∀ q : ℕ, 1 ≤ q → q ≤ 8 → ∀ k : Fin 6199, ∀ r : ResidueGroup q,
      Y q r k ≤ ∑ a ∈ Icc 1 60, jointContrib g Y q r k a :=
  Iff.rfl

/-- The joint-certificate condition need only be checked at the nonzero entries of `𝖸`. -/
theorem isJointCert_iff_of_ne_zero (g : Fin 6199 → ℕ)
    (Y : (q : ℕ) → ResidueGroup q → Fin 6199 → ℕ) :
    IsJointCert g Y ↔ ∀ q : ℕ, 1 ≤ q → q ≤ 8 → ∀ k : Fin 6199, ∀ r : ResidueGroup q,
      Y q r k ≠ 0 → Y q r k ≤ ∑ a ∈ Icc 1 60, jointContrib g Y q r k a := by
  refine ⟨fun h q h1 h8 k r _ => h q h1 h8 k r, fun h q h1 h8 k r => ?_⟩
  by_cases h0 : Y q r k = 0
  · exact h0 ▸ Nat.zero_le _
  · exact h q h1 h8 k r h0

end CollatzPosDens
