/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02OmegaFar
public import CollatzPosDens.Transfer.S02ROmega
public import CollatzPosDens.Transfer.S02VLower

/-!
# A lower bound for the far-gap threshold `Ω_far`

At every Fourier parameter index `ι ∈ {o, b}` the far-gap threshold `Ω_far(ι) = R_Ω(ι)^2`
dominates each of `2^34`, `512 V_*(ι)` and `12500000`.

## Main results

* `CollatzPosDens.max_le_omegaFar`: `max (2^34, 512 V_*(ι), 12500000) ≤ Ω_far(ι)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The far-gap threshold dominates `2^34`, `512 V_*(ι)` and `12500000`:
`max (2^34, 512 V_*(ι), 12500000) ≤ Ω_far(ι)` for every index `ι`. -/
@[collatz_pos_dens "lem_s02_Omega_lower"]
theorem max_le_omegaFar (ι : FIndex) :
    max (max (2 ^ 34) (512 * Vstar ι)) 12500000 ≤ omegaFar ι := by
  have hV := two_pow_18_le_Vstar ι
  have hR := Vstar_le_ROmega ι
  rw [omegaFar_def, sq]
  generalize Vstar ι = V at hV hR ⊢
  generalize ROmega ι = R at hR ⊢
  have h512 : 512 ≤ R := le_trans (by norm_num) (hV.trans hR)
  have hVR : 512 * V ≤ R * R := Nat.mul_le_mul h512 hR
  have h34 : 2 ^ 34 ≤ R * R :=
    le_trans (by norm_num) (Nat.mul_le_mul (hV.trans hR) (hV.trans hR))
  exact max_le (max_le h34 hVR) (le_trans (by norm_num) h34)

end CollatzPosDens
