/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17Values
public import CollatzPosDens.Transfer.S02GammaPk
public import CollatzPosDens.Transfer.S02Hpack
public import CollatzPosDens.Transfer.S02Qpack
public import Mathlib.Tactic.Linarith

/-!
# The same-class affine envelope

For every Fourier index `ι ∈ 𝔍`, every phase class `s ∈ {1, 3, 5, 7}` and every
`N ≥ H_pk(ι) + 1`, the affine function `N ↦ (4 - Sʰ_s) N + Dʰ_s` built from the aggregate deficit
`Sʰ_s` and the aggregate range `Dʰ_s` lies below the packing envelope `N ↦ 4 q_pack N + Γ_pk`.

Writing `a_s = Sʰ_s - 4 + 4 q_pack` and `N_ι = H_pk(ι) + 1` (so `N_o = 36`, `N_b = 34`), the exact
values of `Sʰ_s` and `Dʰ_s` give `a_s = 22412959847/53687091200000000` for `s ∈ {1, 7}` and
`a_s = 20700711010826399/107374182400000000` for `s ∈ {3, 5}`, and the four margins
`Γ_pk - (Dʰ_s - N_ι a_s)` are
`8156081731579/107374182400000000` (`ι = o`, `s ∈ {1, 7}`),
`68195995933285883/10737418240000000` (`ι = o`, `s ∈ {3, 5}`),
`8066429892191/107374182400000000` (`ι = b`, `s ∈ {1, 7}`) and
`40034908581950377/6710886400000000` (`ι = b`, `s ∈ {3, 5}`). All are positive, so
`(4 - Sʰ_s) N + Dʰ_s = 4 q_pack N + (Dʰ_s - N_ι a_s) - a_s (N - N_ι) ≤ 4 q_pack N + Γ_pk`.

## Main results

* `CollatzPosDens.c3H17_affine_envelope`: the affine envelope, for `N` in any linearly ordered
  field.

## Implementation notes

The inequality is stated for `N` in an arbitrary linearly ordered field rather than only for
real `N`; the real case is an instance.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Same-class affine envelope.** For every Fourier index `ι`, every `s ∈ {1, 3, 5, 7}` and
every `N ≥ H_pk(ι) + 1`,
`(4 - Sʰ_s) N + Dʰ_s ≤ 4 q_pack N + Γ_pk`. -/
@[collatz_pos_dens "lem_c3_affine_envelope"]
theorem c3H17_affine_envelope {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ι : FIndex) {s : ℤ} (hs : s ∈ ({1, 3, 5, 7} : Finset ℤ)) {N : K}
    (hN : (Hpack ι : K) + 1 ≤ N) :
    (4 - (c3H17S s : K)) * N + (c3H17Delta s : K) ≤ 4 * (qPack : K) * N + (Gammapk : K) := by
  have hv := c3H17S_c3H17Delta_eq hs
  have hN' : (34 : K) ≤ N := by
    cases ι
    · rw [Hpack_cast_o] at hN; linarith
    · rw [Hpack_cast_b] at hN; linarith
  rw [qPack_cast, Gammapk_cast]
  by_cases h17 : s ∈ ({1, 7} : Finset ℤ)
  · rw [ite_eq_left h17, Prod.mk.injEq] at hv
    rw [hv.1, hv.2]
    push_cast
    linarith
  · rw [ite_eq_right h17, Prod.mk.injEq] at hv
    rw [hv.1, hv.2]
    push_cast
    linarith

end CollatzPosDens
