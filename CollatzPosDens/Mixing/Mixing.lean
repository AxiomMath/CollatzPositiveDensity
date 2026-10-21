/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Transfer.MxProfile
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.S02Reduction
public import CollatzPosDens.Mixing.MxOscForm
public import CollatzPosDens.Transfer.S02Findex
public import CollatzPosDens.Mixing.MxBootChain
public import CollatzPosDens.Mixing.MxExactProfileLe

/-!
# The mixing lemma

For every Fourier index `ι ∈ {o, b}` and integers `n₀ ≤ m ≤ q`, where `n₀` is the mixing gate
level `mxGateLevel`, the reference density `ρ_q` is close on average to the pulled-back coarser
density `ρ_m ∘ π_{q,m}`:
$$\langle |\rho_q - \rho_m \circ \pi_{q,m}| \rangle_q \le \mathfrak M_ι(m),$$
where `𝔐_ι = mxProfile ι` is the propagation mixing profile.

## Main results

* `CollatzPosDens.residueAvg_abs_refDensity_sub_le_of_two_pow_le`: the mixing bound above.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every Fourier index `ι` and integers `n₀ ≤ m ≤ q`, where `n₀` is the mixing gate level,
`⟨|ρ_q - ρ_m ∘ π_{q,m}|⟩_q ≤ 𝔐_ι(m)`, where `𝔐_ι` is the propagation mixing profile. -/
@[collatz_pos_dens "lem_mixing"]
theorem residueAvg_abs_refDensity_sub_le_of_two_pow_le (ι : FIndex) {m q : ℕ}
    (hm : mxGateLevel ≤ m) (h : m ≤ q) :
    residueAvg q (fun y => |refDensity q y - refDensity m (residueReduction h y)|) ≤
      mxProfile ι m := by
  rw [residueAvg_abs_refDensity_sub h]
  exact (oscillation_refLaw_le_mxExactProfile ι hm h).trans
    (mxExactProfile_le_mxProfile ι (by exact_mod_cast hm))

end CollatzPosDens
