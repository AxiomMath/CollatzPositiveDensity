/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02Bi
public import CollatzPosDens.Transfer.S02GammaPk
public import CollatzPosDens.Transfer.S02Hpack
public import CollatzPosDens.Transfer.S02ROmega
public import CollatzPosDens.Transfer.S02Qpack
public import CollatzPosDens.Transfer.S02Eta
public import CollatzPosDens.Transfer.S02RhoPk
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Positivity

/-!
# The weighted square-root allowance `𝓔_sq(ι)`

For a Fourier index `ι ∈ 𝔍 = {o, b}`, the weighted square-root allowance is the rational number
$$\mathcal E_{\mathrm{sq}}(\iota) := \frac{\frac{49}{120}\sum_{i=0}^{r_*(\iota)-1}\eta_i(\iota)
  \bigl[4\mathsf q_{\mathrm{pack}}(\mathsf B_i(\iota)+H_{\mathrm{pk}}(\iota))
    +\Gamma_{\mathrm{pk}}\bigr]
  \bigl(1+\rho_i(\iota)\bigr)+1}{R_\Omega(\iota)},$$
where `η_i(ι)` are the event coefficients, `q_pack` the packing ratio, `B_i(ι)` the packing widths,
`H_pk(ι)` the packing expansion length, `Γ_pk` the packing constant, `ρ_i(ι)` the thin-block
packing ratios, `r_*(ι)` the number of schedule intervals and `R_Ω(ι)` the far-gap scale. It
collects, over the `r_*(ι)` active packing steps, the square-root error terms of the thin-block
conditional packing, each weighted by the event coefficient of its stage, normalised by the
far-gap scale. It is positive; its value at the bootstrap index is `𝓔_sq(b) = 0.0172681394628…`.

## Main definitions

* `CollatzPosDens.Esq`: the weighted square-root allowance `𝓔_sq(ι) ∈ ℚ`.

## Main results

* `CollatzPosDens.Esq_def`: the defining formula of `𝓔_sq(ι)`.
* `CollatzPosDens.Esq_pos`: `0 < 𝓔_sq(ι)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The weighted square-root allowance
`𝓔_sq(ι) := ((49/120) ∑_{i < r_*(ι)} η_i(ι) [4 q_pack (B_i(ι) + H_pk(ι)) + Γ_pk] (1 + ρ_i(ι)) + 1)
/ R_Ω(ι)`. -/
@[collatz_pos_dens "def_s02_weighted_sqrt"]
noncomputable def Esq (ι : FIndex) : ℚ :=
  (49 / 120 * ∑ i ∈ Finset.range (rStar ι), eventCoeff ι i *
      (4 * qPack * (packWidth ι i + (Hpack ι : ℚ)) + Gammapk) * (1 + thinPackRatio ι i) + 1) /
    (ROmega ι : ℚ)

/-- The defining formula of the weighted square-root allowance. -/
theorem Esq_def (ι : FIndex) : Esq ι =
    (49 / 120 * ∑ i ∈ Finset.range (rStar ι), eventCoeff ι i *
      (4 * qPack * (packWidth ι i + (Hpack ι : ℚ)) + Gammapk) * (1 + thinPackRatio ι i) + 1) /
      (ROmega ι : ℚ) := by
  unfold Esq
  rfl

/-- The weighted square-root allowance is positive. -/
theorem Esq_pos (ι : FIndex) : 0 < Esq ι := by
  rw [Esq_def]
  have hR : (0 : ℚ) < ROmega ι := by exact_mod_cast ROmega_pos ι
  have hS : 0 ≤ ∑ i ∈ Finset.range (rStar ι), eventCoeff ι i *
      (4 * qPack * (packWidth ι i + (Hpack ι : ℚ)) + Gammapk) * (1 + thinPackRatio ι i) :=
    Finset.sum_nonneg fun i _ => by
      have := eventCoeff_nonneg ι i; have := qPack_pos; have := (packWidth_pos ι i).le
      have := Gammapk_pos; have := thinPackRatio_nonneg ι i
      positivity
  positivity

end CollatzPosDens
