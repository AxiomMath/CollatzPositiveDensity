/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FcFirstDeficit
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.S05JointBelow
public import CollatzPosDens.Seed.S05JointCertExists
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Transfer.PrefixExtension

/-!
# Mass of the selected first block in the cylinder

At generation `0`, the words `v` of the central family `𝒞 = 𝒞(b_0, K_0)` with `|v| ≥ 8`,
offset at most `3/4` and prefix residue `pr_8(v) = [6275]_8` carry geometric mass
$$\mathbf p\bigl(\{v\in\mathcal C : |v| \ge 8,\ \mathrm{off}(v)\le\tfrac34,\
  \mathrm{pr}_8(v) = [6275]_8\}\bigr) > \frac{617014680840434}{2^{62}}-\frac1{20000000}.$$

Write `𝒞'` for this set and `h = h_{b_0}`. The family `𝒞` lies in the first-crossing family
`𝒲(b_0, r_{b_0}, K_0)`, which is finite and prefix-disjoint, with all lengths in `(ℓ_{b_0}, h]`,
and `ℓ_{b_0} = 6618` since `b_0 = 16544`. A word of length `h` with a prefix `v ∈ 𝒞 ∖ 𝒞'`
has offset `> 3/4` or prefix residue `≠ [6275]_8`, because `off(vz) ≥ off(v)` and
`pr_8(vz) = pr_8(v)` for `|v| ≥ 8`. By prefix extension, `𝐩(𝒞 ∖ 𝒞')` is therefore at most
`1 - 𝖥^{jt}_{h,8}([6275]_8, 3/4)`. The joint certificate of `exists_isOfflawCert_isJointCert`
gives `𝖥^{jt}_{h,8}([6275]_8, ξ_384) ≥ 617014680840434/2^62`, with `ξ_384 = 3/4`, and
`one_sub_geomMass_centralFamily_scale_zero_lt` gives `𝐩(𝒞) > 1 - 1/20000000`.

## Main results

* `CollatzPosDens.sub_lt_geomMass_setOf_mem_centralFamily_off_le`: the mass bound above.

## Implementation notes

The geometric mass is `ℝ≥0∞`-valued; the bound is written
`617014680840434 / 2^62 - 20000000⁻¹` in `ℝ≥0∞`, where the subtraction is exact since
`20000000⁻¹ ≤ 617014680840434 / 2^62`. The residue `[6275]_8 ∈ G_8` is the dyadic reduction of
the integer `6275`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- `617014680840434 / 2^62` in `ℝ≥0∞` has real part `617014680840434 / 2^62`. -/
private theorem firstBlock_toReal_cert :
    ((617014680840434 : ℝ≥0∞) / 2 ^ 62).toReal = 617014680840434 / 2 ^ 62 := by
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_ofNat]

/-- At generation `0`, `𝐩({v ∈ 𝒞(b_0, K_0) : |v| ≥ 8, off(v) ≤ 3/4, pr_8(v) = [6275]_8})`
exceeds `617014680840434/2^62 - 1/20000000`. -/
@[collatz_pos_dens "lem_s05_first_block_mass"]
theorem sub_lt_geomMass_setOf_mem_centralFamily_off_le :
    (617014680840434 / 2 ^ 62 : ℝ≥0∞) - 20000000⁻¹ <
      geomMass {v ∈ centralFamily (scale 0) (cap 0) |
        8 ≤ v.length ∧ off v ≤ 3 / 4 ∧
          prefixResidue 8 v = dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩} := by
  set r : ResidueGroup 8 := dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩ with hr_def
  set C := centralFamily (scale 0) (cap 0) with hC_def
  set h := hb (scale 0) with hh_def
  set P : Word → Prop := fun v => 8 ≤ v.length ∧ off v ≤ 3 / 4 ∧ prefixResidue 8 v = r
    with hP_def
  set C' := {v ∈ C | P v}
  set B := {v ∈ C | ¬ P v}
  set A := {u : Word | u.length = h ∧ (off u : ℝ) ≤ 3 / 4 ∧ prefixResidue 8 u = r}
  set Ac := {u : Word | u.length = h ∧ ¬ ((off u : ℝ) ≤ 3 / 4 ∧ prefixResidue 8 u = r)}
  have h34 {q : ℚ} : (q : ℝ) ≤ 3 / 4 ↔ q ≤ 3 / 4 := by
    rw [show (3 / 4 : ℝ) = ((3 / 4 : ℚ) : ℝ) by norm_num, Rat.cast_le]
  have hsub : C ⊆ firstCrossing (scale 0) (rb (scale 0)) (cap 0) :=
    centralFamily_subset_firstCrossing _ _
  have hCfin : C.Finite := (firstCrossing_finite _ _ _).subset hsub
  have hCtop : geomMass C ≠ ⊤ := by
    rw [← hCfin.coe_toFinset]; exact geomMass_coe_finset_ne_top _
  have hlb : lb (scale 0) = 6618 := by rw [scale_zero, lb_eq]
  have hlen8 : ∀ v ∈ C, 8 ≤ v.length := fun v hv => by
    have := lb_lt_length_of_mem_firstCrossing (hsub hv)
    omega
  have hCB : geomMass C = geomMass C' + geomMass B := by
    have hCeq : C = C' ∪ B := by
      ext v
      constructor
      · intro hv
        by_cases hp : P v
        · exact Or.inl ⟨hv, hp⟩
        · exact Or.inr ⟨hv, hp⟩
      · rintro (⟨hv, -⟩ | ⟨hv, -⟩) <;> exact hv
    have hdisj : Disjoint C' B := by
      rw [Set.disjoint_left]
      rintro v ⟨-, hv⟩ ⟨-, hv'⟩
      exact hv' hv
    exact (congrArg geomMass hCeq).trans (geomMass_union hdisj)
  have hB : geomMass B ≤ geomMass Ac := by
    rw [geomMass_eq_geomMass_setOf_prefix_mem (h := h)
      (fun a ha b hb' hab => isPrefixFree_firstCrossing _ _ _ a (hsub ha.1) b (hsub hb'.1) hab)
      fun v hv => length_le_hb_of_mem_firstCrossing (hsub hv.1)]
    refine geomMass_mono ?_
    rintro u ⟨hu, v, ⟨hvC, hvP⟩, z, rfl⟩
    refine ⟨hu, fun ⟨hoff, hres⟩ => hvP ⟨hlen8 v hvC, ?_, ?_⟩⟩
    · refine (h34.1 hoff).trans' ?_
      rw [off_append]
      exact le_add_of_nonneg_right (mul_nonneg (Word.weight_pos v).le (off_nonneg z))
    · rw [← hres, prefixResidue_def, prefixResidue_def,
        List.take_append_of_le_length (hlen8 v hvC)]
  have hU : geomMass A + geomMass Ac = 1 := by
    have hUeq : A ∪ Ac = {u : Word | u.length = h} := by
      ext u
      constructor
      · rintro (⟨hu, -⟩ | ⟨hu, -⟩) <;> exact hu
      · intro hu
        by_cases hp : (off u : ℝ) ≤ 3 / 4 ∧ prefixResidue 8 u = r
        · exact Or.inl ⟨hu, hp⟩
        · exact Or.inr ⟨hu, hp⟩
    have hdisj : Disjoint A Ac := by
      rw [Set.disjoint_left]
      rintro u ⟨-, hu⟩ ⟨-, hu'⟩
      exact hu' hu
    rw [← geomMass_union hdisj, hUeq, geomMass_setOf_length_eq h]
  have hA : (617014680840434 / 2 ^ 62 : ℝ≥0∞) ≤ geomMass A := by
    obtain ⟨g, Y, hg, hY, hY8⟩ := exists_isOfflawCert_isJointCert
    have h8 : 8 ≤ h := by rw [hh_def, scale_zero, hb_eq]; norm_num
    have hbd := hY.div_le_jointLaw hg (by norm_num) le_rfl h8 384 r
    have hgrid : ((offlawGrid ((384 : Fin 6199) : ℕ) : ℚ) : ℝ) = 3 / 4 := by
      rw [show ((384 : Fin 6199) : ℕ) = 384 from rfl, offlawGrid_384]
      norm_num
    rw [hgrid, jointLaw_def] at hbd
    refine le_trans ?_ hbd
    gcongr
    exact_mod_cast hY8
  have hD := one_sub_geomMass_centralFamily_scale_zero_lt
  rw [← hC_def] at hD
  have hinv : (20000000⁻¹ : ℝ≥0∞) ≠ ⊤ := ENNReal.inv_ne_top.2 (by norm_num)
  have hcert : (617014680840434 / 2 ^ 62 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have hAtop : geomMass A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hU ▸ le_self_add)
  have hActop : geomMass Ac ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hU ▸ le_add_self)
  have hC'top : geomMass C' ≠ ⊤ := ne_top_of_le_ne_top hCtop (hCB ▸ le_self_add)
  have hBtop : geomMass B ≠ ⊤ := ne_top_of_le_ne_top hCtop (hCB ▸ le_add_self)
  have hCBr : (geomMass C).toReal = (geomMass C').toReal + (geomMass B).toReal := by
    rw [hCB, ENNReal.toReal_add hC'top hBtop]
  have hBr : (geomMass B).toReal ≤ (geomMass Ac).toReal :=
    (ENNReal.toReal_le_toReal hBtop hActop).2 hB
  have hUr : (geomMass A).toReal + (geomMass Ac).toReal = 1 := by
    rw [← ENNReal.toReal_add hAtop hActop, hU, ENNReal.toReal_one]
  have hAr : (617014680840434 / 2 ^ 62 : ℝ) ≤ (geomMass A).toReal := by
    rw [← firstBlock_toReal_cert]
    exact (ENNReal.toReal_le_toReal hcert hAtop).2 hA
  have hDr : 1 < (geomMass C).toReal + 1 / 20000000 := by
    have h1 := ENNReal.lt_add_of_sub_lt_left (Or.inl ENNReal.one_ne_top) hD
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top
      (ENNReal.add_ne_top.2 ⟨hCtop, hinv⟩)).2 h1
    rwa [ENNReal.toReal_add hCtop hinv, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
      ENNReal.toReal_one, ← one_div] at this
  refine ENNReal.sub_lt_of_lt_add ?_ ?_
  · rw [← ENNReal.toReal_le_toReal hinv hcert, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
      firstBlock_toReal_cert]
    norm_num
  rw [← ENNReal.toReal_lt_toReal hcert (ENNReal.add_ne_top.2 ⟨hC'top, hinv⟩),
    ENNReal.toReal_add hC'top hinv, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    firstBlock_toReal_cert]
  linarith

end CollatzPosDens
