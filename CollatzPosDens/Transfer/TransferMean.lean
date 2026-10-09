/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Transfer

/-!
# The mean of a transfer

For every word `w`, every `t ∈ ℕ` and every `g : G_t → ℝ`, the transfer `𝒯_w g` has mean
`⟨𝒯_w g⟩_{t+|w|} = 2^{-A(w)} ⟨g⟩_t`. Each `z ∈ G_t` lies in exactly one fiber of the residue map
`φ_w`, so the total mass of `𝒯_w g` is `ω(w)` times that of `g`; dividing by `3^{t+|w|}` and using
`ω(w) = 3^{|w|} 2^{-A(w)}` gives the claim.

## Main results

* `CollatzPosDens.residueAvg_transfer`: `⟨𝒯_w g⟩_{t+|w|} = 2^{-A(w)} ⟨g⟩_t`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The mean of a transfer satisfies `⟨𝒯_w g⟩_{t+|w|} = 2^{-A(w)} ⟨g⟩_t`. -/
@[collatz_pos_dens "lem_transfer_mean"]
theorem residueAvg_transfer (w : Word) {t : ℕ} (g : ResidueGroup t → ℝ) :
    residueAvg (t + w.length) (transfer w g) =
      (2 : ℝ) ^ (-(w.valSum : ℤ)) * residueAvg t g := by
  rw [residueAvg_def, residueAvg_def, sum_transfer, Word.weight, zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp

end CollatzPosDens
