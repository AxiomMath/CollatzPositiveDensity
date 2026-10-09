/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChDist
public import CollatzPosDens.CharSum.ChQmDominate
public import CollatzPosDens.CharSum.ChQmNonempty

/-!
# A boundary estimate suffices for monotonicity of `Q_m`

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`, and write `J = ⌊n/2⌋`. For a real
`A ≥ 0` and an integer `m ≥ 1`, passing from `Q_{m-1}` to `Q_m` only adds the points `p ∈ 𝒫` on
the layer `j(p) + m = J`, where `d_J(p) = m`. Hence if `Q(p) ≤ m^{-A} Q_{m-1}` on that layer,
then `Q_m ≤ Q_{m-1}`: points with `j(p) + m - 1 ≥ J` are dominated by `Q_{m-1}`, and on the layer
`d_J(p)^A Q(p) = m^A Q(p) ≤ Q_{m-1}`.

## Main results

* `CollatzPosDens.chQm_le_chQm_pred`: `Q_m ≤ Q_{m-1}` under the boundary hypothesis.

## Implementation notes

Powers are real powers `Real.rpow`, matching `CollatzPosDens.chQm`. The threshold `ε` is an
arbitrary real parameter.

## References

* [Mazur, *Collatz positive density*], §7.5.
-/

@[expose] public section

namespace CollatzPosDens

/-- **A boundary estimate suffices.** For real `A ≥ 0` and an integer `m ≥ 1`, if
`Q(p) ≤ m^{-A} Q_{m-1}` for every `p ∈ 𝒫` with `j(p) + m = ⌊n/2⌋`, then `Q_m ≤ Q_{m-1}`. -/
@[collatz_pos_dens "lem_ch_boundary_suffices"]
theorem chQm_le_chQm_pred (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ} (hA : 0 ≤ A)
    {m : ℕ} (hm : 1 ≤ m)
    (h : ∀ p ∈ bkPoints, bkJ p + m = ((n / 2 : ℕ) : ℤ) →
      chQ n ξ ε p ≤ (m : ℝ) ^ (-A) * chQm n ξ ε A (m - 1)) :
    chQm n ξ ε A m ≤ chQm n ξ ε A (m - 1) := by
  refine csSup_le (chQm_set_nonempty n ξ ε A m) fun _ ⟨p, hp, hj, hx⟩ => hx ▸ ?_
  have hp1 : 1 ≤ bkJ p := hp
  by_cases hcase : ((n / 2 : ℕ) : ℤ) ≤ bkJ p + (m - 1 : ℕ)
  · exact chQm_dominate n ξ ε hA (m - 1) hp (by omega)
  · have hJ : bkJ p + m = ((n / 2 : ℕ) : ℤ) := by omega
    have hd : chDist n p = m := by
      have := chDist_eq_of_lt (n := n) (p := p) (by omega); omega
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    rw [hd, ← le_inv_mul_iff₀ (by positivity), ← Real.rpow_neg hmpos.le]
    exact h p hp hJ

end CollatzPosDens
