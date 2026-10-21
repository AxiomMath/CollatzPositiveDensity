/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.S02Theta
public import CollatzPosDens.Transfer.S02RhoUnit
public import CollatzPosDens.StoppingTrace.TrEntryWord
public import CollatzPosDens.StoppingTrace.TrKernel
public import CollatzPosDens.StoppingTrace.TrKernelOne
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# Powers of the entry kernel

Fix a level `n` and a unit `ξ ∈ G_n`, and call a point black when it is black for the level
`n`, the residue `ξ` and the threshold `ε_*`. For every black point `v ∈ 𝒫` and every `k ∈ ℕ`,
the `k`-th power of the entry kernel satisfies `m_k(v) ≤ θ^en_k = (1 - d_entry)^k = (77/100)^k`.

The proof is by induction on `k`, for all black points at once. Since `m_0 = 1 = θ^en_0` the
base case is trivial. If `m_k ≤ θ^en_k` at every black point, then, since the endpoints
`x_{|u|}(v, u)` of the entry lists `u ∈ 𝓔(v)` are black points and all terms are nonnegative,
the recursion for `m_{k+1}(v)` and `θ^en_k ≥ 0` give `m_{k+1}(v) ≤ θ^en_k m_1(v)`, and the
one-step bound `m_1(v) ≤ 1 - d_entry` gives `m_{k+1}(v) ≤ θ^en_k (1 - d_entry) = θ^en_{k+1}`.

## Main results

* `CollatzPosDens.trKernel_two_le_rhoStar`: `m_k(v) ≤ θ^en_k` for every black point `v` and
  every `k`.

## Implementation notes

The value `m_k(v)` lies in `[0, ∞]`, and the bound is stated there against
`ENNReal.ofReal θ^en_k`; since `θ^en_k > 0` this is the real inequality, and it asserts in
particular that `m_k(v)` is finite. Black points are points of `𝒫` and the residue `ξ` is a
unit; these standing assumptions are the hypotheses `v ∈ bkPoints` and `IsResidueUnit ξ`.

## References

* [Mazur, *Collatz positive density*], §9.10.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

variable {n : ℕ} {ξ : ResidueGroup n}

/-- **Powers of the entry kernel.** Let `ξ ∈ G_n` be a unit. For every
black point `v ∈ 𝒫` and every `k ∈ ℕ`, `m_k(v) ≤ θ^en_k`. -/
@[collatz_pos_dens "lem_tr_kernel_two"]
theorem trKernel_two_le_rhoStar (hξ : IsResidueUnit ξ) (k : ℕ) {v : ℤ × ℤ}
    (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v) :
    trKernel n ξ k v ≤ ENNReal.ofReal (thetaEn k : ℝ) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    have hθ : (0 : ℝ) ≤ thetaEn k := by exact_mod_cast (thetaEn_pos_and_le_one k).1.le
    calc trKernel n ξ (k + 1) v
        ≤ ∑' u : trEntryWords n ξ (epsStar : ℝ) v,
            ENNReal.ofReal (trListWeight u.1) *
              ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u.1 u.1.length)) *
                ENNReal.ofReal (thetaEn k : ℝ) :=
          trKernel_succ_le_of_le k v (fun _ ↦ ENNReal.ofReal (thetaEn k : ℝ)) fun u hu ↦
            ih (trPath_mem_bkPoints hv u u.length) (trEntryWords_bkBlack hu)
      _ = ENNReal.ofReal (thetaEn k : ℝ) * trKernel n ξ 1 v := by
          rw [trKernel_succ, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun u ↦ ?_
          rw [trKernel_zero, mul_one, mul_comm]
      _ ≤ ENNReal.ofReal (thetaEn k : ℝ) * ENNReal.ofReal (1 - (dEntry : ℝ)) := by
          gcongr
          exact trKernel_one_le hξ hv hb
      _ = ENNReal.ofReal (thetaEn (k + 1) : ℝ) := by
          rw [← ENNReal.ofReal_mul hθ, thetaEn_succ]
          push_cast
          ring_nf

end CollatzPosDens
