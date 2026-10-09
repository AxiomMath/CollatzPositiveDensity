/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.AffineIdentity
public import CollatzPosDens.Maps.OffsetBound
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.OffsetSmall
public import CollatzPosDens.FirstCrossing.WeightLower
public import CollatzPosDens.FirstCrossing.WeightUpper
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.Terminal.ShiftWindow
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.Terminal.UnweightedMass

/-!
# The source window

Let `M` be a good seed, `n ≥ 0`, and let `X` be admissible for generation `n`. Then every
source `x = src(w, R_h)` of a counted pair `(h, w)` of `Υ_{n,X}(M)` satisfies `X ≤ x < 32 X`,
that is `𝒮_{n,X}(M) ⊆ [X, 32 X)`.

With `R = R_h`, `b = b_n` and `u = u_h`, one has `R ≥ 16^b`, `R = ω(w) x + off(w)` and
`0 < off(w) < 2^b ≤ R / 2`, so `R / 2 ≤ ω(w) x ≤ R`. The weight bounds
`2^{-2+r_b-u} (3/4)^b ≤ ω(w) ≤ 2^{1+r_b-u} (3/4)^b` together with
`2^{u-r_b} (4/3)^b R = 4 · 2^u L_b(R)` give `2^u L_b(R) ≤ x ≤ 16 · 2^u L_b(R)`, and the shift
window `X ≤ 2^u L_b(R) < 2X` concludes.

## Main results

* `CollatzPosDens.sources_subset_Ico_of_odd`: the window, for an odd integer seed
  `M ≥ 16^{b₀}`.
* `CollatzPosDens.GoodSeed.sources_subset_Ico`: the window, for a good seed `M`.

## Implementation notes

Of the good-seed conditions, the argument uses only that `M` is odd with `M ≥ 16^{b₀}`; the
general statement is recorded under these hypotheses. The source set is a set of integers and
the window is stated for its image in `ℝ`.

## References

* [Mazur, *Collatz positive density*], §18.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {X : ℝ}

/-- The scale identity `4 · 2^{r_b - u} (3/4)^b · 2^u L_b(R) = R`. -/
private theorem four_mul_mul_lowerScale (b u : ℕ) (R : ℝ) :
    4 * ((2 : ℝ) ^ (rb b - (u : ℤ)) * (3 / 4) ^ b) * (2 ^ u * lowerScale b R) = R := by
  rw [lowerScale_def, zpow_sub₀ two_ne_zero, zpow_natCast, div_pow]
  have : (0 : ℝ) < 2 ^ rb b := zpow_pos two_pos _
  field_simp

/-- **Source window**, for an odd integer seed `M ≥ 16^{b₀}`: if `X` is admissible for
generation `n`, then `𝒮_{n,X}(M) ⊆ [X, 32 X)`. -/
theorem sources_subset_Ico_of_odd {M : ℤ} (hodd : Odd M) (hM : 16 ^ scale 0 ≤ M)
    (hX : IsAdmissibleScale M n X) :
    ((↑) : ℤ → ℝ) '' sources n X M ⊆ Set.Ico X (32 * X) := by
  rintro _ ⟨z, ⟨⟨h, w⟩, hp, hz⟩, rfl⟩
  obtain ⟨hh, hw, -, -⟩ := mem_unweightedMassPairs.1 hp
  dsimp only at hz
  set b := scale n with hb
  set u := historyShift n X M h with hu
  set R := historyEndpoint (M : ℚ) h with hRdef
  have h16 : ((16 : ℝ) ^ b) ≤ (R : ℝ) :=
    historyEndpointAt_large_sixteen_pow_le_endpoint hodd hM hh
  have hR := two_mul_two_pow_le_sixteen_pow (K := ℝ) (scale_pos n)
  have hoff0 : (0 : ℝ) < off w := by
    exact_mod_cast off_pos (List.length_pos_iff.2 (ne_nil_of_mem_firstCrossing hw))
  have hoff1 : (off w : ℝ) < 2 ^ b := by
    exact_mod_cast off_lt_two_pow_of_mem_firstCrossing hw
  have haff : (R : ℝ) = (w.weight : ℝ) * z + off w := by
    have := eq_weight_mul_src_add_off w R
    rw [hz] at this
    exact_mod_cast this
  have hωu : (w.weight : ℝ) ≤ (2 : ℝ) ^ (1 + rb b - (u : ℤ)) * (3 / 4) ^ b := by
    have := Rat.cast_le (K := ℝ) |>.2 (weight_le_of_mem_firstCrossing hw)
    push_cast at this
    exact this
  have hωl : (2 : ℝ) ^ (-((1 : ℕ) : ℤ) - 1 + rb b - (u : ℤ)) * (3 / 4) ^ b ≤ w.weight := by
    have := Rat.cast_le (K := ℝ) |>.2 (le_weight_of_mem_firstCrossing hw)
    push_cast at this ⊢
    exact this
  have hωpos : (0 : ℝ) < w.weight := by exact_mod_cast Word.weight_pos w
  obtain ⟨hT1, hT2⟩ := hX.shift_window hh
  set T := (2 : ℝ) ^ u * lowerScale b R with hT
  have hTpos : 0 < T := by linarith [hX.pos]
  set c : ℝ := (2 : ℝ) ^ (rb b - (u : ℤ)) * (3 / 4) ^ b with hc
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have hcu : (2 : ℝ) ^ (1 + rb b - (u : ℤ)) * (3 / 4) ^ b = 2 * c := by
    rw [hc, show 1 + rb b - (u : ℤ) = 1 + (rb b - u) by ring, zpow_add₀ h2, zpow_one]
    ring
  have hcl : (2 : ℝ) ^ (-((1 : ℕ) : ℤ) - 1 + rb b - (u : ℤ)) * (3 / 4) ^ b = c / 4 := by
    rw [hc, show -((1 : ℕ) : ℤ) - 1 + rb b - (u : ℤ) = -2 + (rb b - u) by push_cast; ring,
      zpow_add₀ h2]
    norm_num
    ring
  have hcT : 4 * c * T = R := four_mul_mul_lowerScale b u R
  rw [hcu] at hωu
  rw [hcl] at hωl
  refine ⟨?_, ?_⟩
  · have : (w.weight : ℝ) * T ≤ w.weight * z := by nlinarith
    exact hT1.trans (le_of_mul_le_mul_left this hωpos)
  · have : (w.weight : ℝ) * z ≤ w.weight * (16 * T) := by nlinarith
    linarith [le_of_mul_le_mul_left this hωpos]

/-- **Source window.** Let `M` be a good seed and let `X` be admissible for generation `n`.
Then `𝒮_{n,X}(M) ⊆ [X, 32 X)`. -/
@[collatz_pos_dens "lem_source_window"]
theorem GoodSeed.sources_subset_Ico {M : ℕ} (hM : GoodSeed M)
    (hX : IsAdmissibleScale M n X) :
    ((↑) : ℤ → ℝ) '' sources n X M ⊆ Set.Ico X (32 * X) := by
  simpa only [Int.cast_natCast] using sources_subset_Ico_of_odd (M := (M : ℤ))
    (by exact_mod_cast hM.odd) (by exact_mod_cast hM.lower.le) hX

end CollatzPosDens
