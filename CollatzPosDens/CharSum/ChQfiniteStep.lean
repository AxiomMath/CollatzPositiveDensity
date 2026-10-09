/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQfinite
public import CollatzPosDens.CharSum.ChBlockPoint

/-!
# The step recursion for the finite-horizon white products

For every horizon `K ∈ ℕ` and base point `p`, the finite-horizon white product satisfies
`Q^{(K+1)}(p) = w(p) ∑_{β ∈ 𝔅} bw(β) I(p; β) Q^{(K)}(p + bpt(β))`. Indeed, writing a list
`γ ∈ 𝔅^{K+1}` as `(β) γ'` with `β ∈ 𝔅` and `γ' ∈ 𝔅^K`, the block path of `γ` is
`Bp_0(γ) = 0` and `Bp_i(γ) = bpt(β) + Bp_{i-1}(γ')`, so the term of `Q^{(K+1)}(p)` at `γ`
factors as `w(p) bw(β) I(p; β)` times the term of `Q^{(K)}(p + bpt(β))` at `γ'`; summing
over `γ'` and then over `β` gives the identity.

## Main results

* `CollatzPosDens.chQFinite_succ`:
  `Q^{(K+1)}(p) = w(p) ∑_{β ∈ 𝔅} bw(β) I(p; β) Q^{(K)}(p + bpt(β))`.

## Implementation notes

As in `CollatzPosDens.chQFinite`, the alphabet `𝔅` is the subtype of pairs
`List ℤ × ℤ` whose closing letter lies in `{4, 5}`, and the sum over `𝔅` is a `tsum`. The
identity holds for every base point `p ∈ ℤ × ℤ`, not only for points of the parameter set `𝒫`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Step recursion for the finite-horizon white products.**
`Q^{(K+1)}(p) = w(p) ∑_{β ∈ 𝔅} bw(β) I(p; β) Q^{(K)}(p + bpt(β))`. -/
@[collatz_pos_dens "lem_ch_Qfinite_step"]
theorem chQFinite_succ (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ) (p : ℤ × ℤ) :
    chQFinite n ξ ε (K + 1) p =
      chWhiteFactor n ξ ε p *
        ∑' β : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
          chBlockWeight β * chInternalWeight n ξ ε p β *
            chQFinite n ξ ε K (p + chBlockPoint β) := by
  set e := Fin.consEquiv fun _ : Fin (K + 1) ↦ {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}
  have hFe : ∀ x, chQFiniteTerm n ξ ε (K + 1) p (e x) =
      chWhiteFactor n ξ ε p * (chBlockWeight x.1 * chInternalWeight n ξ ε p x.1 *
        chQFiniteTerm n ξ ε K (p + chBlockPoint x.1) x.2) := by
    rintro ⟨a, γ⟩
    simp only [chQFiniteTerm]
    rw [Finset.prod_range_succ' _ (K + 1)]
    simp only [e, Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.prod_univ_succ, chBlockPath_cons_succ, chBlockPath_zero, Fin.val_zero, Fin.val_succ,
      add_zero, add_assoc]
    ring
  calc chQFinite n ξ ε (K + 1) p
      = ∑' x, chQFiniteTerm n ξ ε (K + 1) p (e x) :=
        (e.tsum_eq (chQFiniteTerm n ξ ε (K + 1) p)).symm
    _ = ∑' a, ∑' γ, chQFiniteTerm n ξ ε (K + 1) p (e (a, γ)) :=
        ((e.summable_iff (f := chQFiniteTerm n ξ ε (K + 1) p)).mpr
          (summable_chQFiniteTerm n ξ ε (K + 1) p)).tsum_prod
    _ = _ := by simp only [hFe, tsum_mul_left, chQFinite_eq_tsum]

end CollatzPosDens
