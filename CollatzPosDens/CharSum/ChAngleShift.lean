/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.BlackSet.BkResidueShift

/-!
# Shifting the angle along the `l`-direction

For a point `p ∈ 𝒫` and `k ∈ ℕ`, put `q = p - (0, k)`. The angle residues satisfy
`r(q) = 2^k r(p)` in `G_n = ℤ/3^nℤ`, and `3^n ϑ(q)`, `3^n ϑ(p)` are integer representatives of
`r(q)`, `r(p)`. Hence `ϑ_{n,ξ}(q) - 2^k ϑ_{n,ξ}(p)` is an integer.

## Main results

* `CollatzPosDens.bkTheta_sub_shift_mem_int`: `ϑ_{n,ξ}(p - (0,k)) - 2^k ϑ_{n,ξ}(p) ∈ ℤ`.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Angle shift.** For `p ∈ 𝒫` and `k ∈ ℕ`, `ϑ_{n,ξ}(p - (0,k)) - 2^k ϑ_{n,ξ}(p)` is an
integer. -/
@[collatz_pos_dens "lem_ch_angle_shift"]
theorem bkTheta_sub_shift_mem_int (n : ℕ) (ξ : ResidueGroup n) {p : ℤ × ℤ}
    (hp : p ∈ bkPoints) (k : ℕ) :
    ∃ m : ℤ, bkTheta n ξ (p - (0, (k : ℤ))) - 2 ^ k * bkTheta n ξ p = m := by
  have hq : p - (0, (k : ℤ)) ∈ bkPoints := by simpa [mem_bkPoints] using hp
  have hres := bkThetaResidue_shift n ξ hp hq (by simp) (by simp)
  simp only [bkJ, bkL, Prod.fst_sub, Prod.snd_sub, sub_zero, sub_self, Int.toNat_zero, pow_zero,
    one_mul, sub_sub_cancel, Int.toNat_natCast] at hres
  set rq := bkThetaResidue n ξ (p - (0, (k : ℤ)))
  set rp := bkThetaResidue n ξ p
  have hcong : ((rq.valMinAbs : ℤ) : ZMod (3 ^ n)) =
      ((2 ^ k * rp.valMinAbs : ℤ) : ZMod (3 ^ n)) := by
    push_cast
    simpa using hres
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hcong.symm
  refine ⟨m, ?_⟩
  have hN : ((3 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
  rw [bkTheta_def, bkTheta_def, sfr_def, sfr_def]
  field_simp
  have : ((rq.valMinAbs - 2 ^ k * rp.valMinAbs : ℤ) : ℝ) = ((3 ^ n : ℕ) : ℤ) * m := by
    exact_mod_cast hm
  push_cast at this ⊢
  linarith

end CollatzPosDens
