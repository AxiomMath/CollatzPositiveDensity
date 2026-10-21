/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkAlphaBounds
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkDrift
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.Case3.C3AlphaUpper
public import CollatzPosDens.Case3.C3AnchorSep
public import CollatzPosDens.Case3.C3Cols
public import CollatzPosDens.Case3.C3FilteredPacking
public import CollatzPosDens.Case3.C3GoodMarginal
public import CollatzPosDens.Case3.C3PackConst
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.Transfer.S02AdaptiveAnchor
public import CollatzPosDens.Transfer.S02GammaPk
public import CollatzPosDens.Transfer.S02Hpack
public import CollatzPosDens.Transfer.S02Qpack
public import CollatzPosDens.Transfer.S02Wtot
public import CollatzPosDens.Transfer.S02Xd
public import CollatzPosDens.Transfer.S02Xl
public import CollatzPosDens.Transfer.S02Xo

/-!
# Filtered mass of the anchor columns

Let `ι ∈ 𝔍` be a Fourier index, `ξ` a unit, `e ∈ 𝒫` black (for `ε_*`) with gap
`ω = gap(e) ≥ 2^{34}`, `Δ₀` a triangle, `v ∈ ℕ` and `s > 0` real. Put `A = b_an s - W(ι, v) - 1`,
`B⁺ = 2 X_d(ι, v) + (8/25) W(ι, v) + 1` and `C = (127/40)(2 X_d(ι, v) + 1) + W(ι, v)`, and assume
`B⁺ + H_pk(ι) ≤ (5/16) A`. Then
$$\sum_{r\in\mathcal U_{e,\Delta_0,v,s}(\iota)}\sum_{\ell\in\mathbb Z}
  F^{\mathrm{gd}}_{e,\iota}(r,\ell)
  \le\frac{q_{\mathrm{pack}}C
      +\frac{127}{40}(H_{\mathrm{pk}}(\iota)q_{\mathrm{pack}}+\Gamma_{\mathrm{pk}}/4)}{A}
    +\frac{49}{120}\cdot
      \frac{\bigl(4q_{\mathrm{pack}}(B^++H_{\mathrm{pk}}(\iota))+\Gamma_{\mathrm{pk}}\bigr)
        \bigl(1+\frac{127}{40}(B^++H_{\mathrm{pk}}(\iota))/A\bigr)}{\sqrt\omega}.$$

Fix `ι` and write `X_o, X_l, X_d, W, H_pk` for `X_o(ι), X_l(ι, v), X_d(ι, v), W(ι, v), H_pk(ι)`.
Let `I` be the set of integers `i` with `-X_d - X_l/4 < i < λ X_o + λ₀ X_l + X_d`. This open
interval has length `2 X_d + λ W` (as `λ = 1/4 + λ₀` and `W = X_o + X_l`), so `I` is a block of
`t < B := 2 X_d + λ W + 1` consecutive integers starting at some `i₀`, and the anchor columns lie
in `{z + i : z ∈ Z, 0 ≤ i < t}` with `Z = Anc(Δ₀, s, W) - j(e) + i₀`. The points of `Z` are
`λ A`-separated by `CollatzPosDens.sub_gt_of_mem_bkAnchors`, and `5/16 ≤ λ < 8/25` gives
`B + H_pk ≤ B⁺ + H_pk ≤ (5/16) A ≤ λ A`. The conditional packing
`CollatzPosDens.BkBlack.tsum_tsum_c3GoodMarginal_le` of the filtered marginal then bounds the sum
by `(q_pack (B + H_pk) + Γ_pk/4)/(λ A)
+ 49/120 · (4 q_pack (B + H_pk) + Γ_pk)(1 + (B + H_pk)/(λ A))/√ω`,
and `1/λ < 127/40` with `0 ≤ B + H_pk ≤ B⁺ + H_pk` concludes.

## Main results

* `CollatzPosDens.BkBlack.tsum_tsum_c3GoodMarginal_c3AnchorCols_le`: the mass bound, as a sum
  in `[0, ∞]`.

## Implementation notes

The family is `𝔗 = 𝔗_{n,ξ,ε_*}` for a unit `ξ`. The hypotheses `Δ₀ ∈ 𝔗` and `e ∈ Δ₀` are not
needed for the bound and are dropped, and `A > 0` is not assumed since it follows from
`B⁺ + H_pk ≤ (5/16) A`. The quantities `A`, `B⁺`, `C` are written out in the statement. As in
`CollatzPosDens.BkBlack.tsum_tsum_c3GoodMarginal_le`, the gap is a natural number `ω` with
`(ω : ℤ) = gap(e)`, and the sum is taken in `[0, ∞]`, which needs no summability assumption.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- **Filtered mass of the anchor columns**. Let `ι` be a Fourier index, `ξ` a unit, `e ∈ 𝒫`
black (for `ε_*`) with gap `ω = gap(e) ≥ 2^{34}`, `Δ₀` a triangle, `v ∈ ℕ` and `s > 0`. Write
`A = b_an s - W(ι, v) - 1`, `B⁺ = 2 X_d(ι, v) + (8/25) W(ι, v) + 1`,
`C = (127/40)(2 X_d(ι, v) + 1) + W(ι, v)` and assume `B⁺ + H_pk(ι) ≤ (5/16) A`. Then, as a sum
in `[0, ∞]`, `∑_{r ∈ 𝒰_{e,Δ₀,v,s}(ι)} ∑_ℓ F^gd_{e,ι}(r, ℓ) ≤
(q_pack C + (127/40)(H_pk(ι) q_pack + Γ_pk/4)) / A
+ 49/120 · (4 q_pack (B⁺ + H_pk(ι)) + Γ_pk) (1 + (127/40)(B⁺ + H_pk(ι)) / A) / √ω`, where the
anchor columns are relative to `𝔗 = 𝔗_{n,ξ,ε_*}`. -/
@[collatz_pos_dens "lem_c3_outside_mass"]
theorem BkBlack.tsum_tsum_c3GoodMarginal_c3AnchorCols_le (ι : FIndex) {n : ℕ}
    {ξ : ResidueGroup n}
    {e : ℤ × ℤ} (hb : BkBlack n ξ (epsStar : ℝ) e) (hξ : IsResidueUnit ξ) (he : e ∈ bkPoints)
    {ω : ℕ} (hω : (ω : ℤ) = trGap n ξ (epsStar : ℝ) e) (hω34 : 2 ^ 34 ≤ ω)
    (Δ₀ : BkTriangle) (v : ℕ) {s : ℝ} (hs : 0 < s)
    (hBA : 2 * (Xd ι v : ℝ) + 8 / 25 * totalAllowance ι v + 1 + Hpack ι ≤
      5 / 16 * ((bAn : ℝ) * s - totalAllowance ι v - 1)) :
    ∑' r : c3AnchorCols ι (bkFamily n ξ epsStar) e Δ₀ v s, ∑' ℓ : ℤ,
        c3GoodMarginal ι n ξ e ((r : ℤ), ℓ) ≤
      ENNReal.ofReal
        (((qPack : ℝ) * (127 / 40 * (2 * (Xd ι v : ℝ) + 1) + totalAllowance ι v) +
            127 / 40 * (Hpack ι * (qPack : ℝ) + (Gammapk : ℝ) / 4)) /
            ((bAn : ℝ) * s - totalAllowance ι v - 1) +
          49 / 120 * ((4 * (qPack : ℝ) * (2 * (Xd ι v : ℝ) + 8 / 25 * totalAllowance ι v + 1 +
            Hpack ι) + Gammapk) * (1 + 127 / 40 * (2 * (Xd ι v : ℝ) +
              8 / 25 * totalAllowance ι v + 1 + Hpack ι) /
                ((bAn : ℝ) * s - totalAllowance ι v - 1)) / √ω)) := by
  set A : ℝ := (bAn : ℝ) * s - totalAllowance ι v - 1 with hAdef
  set W : ℝ := (totalAllowance ι v : ℝ) with hW
  set X : ℝ := (Xd ι v : ℝ) with hX
  set lo : ℝ := -(Xd ι v : ℝ) - (Xl ι v : ℝ) / 4 with hlo
  set hi : ℝ := alpha * overshootAllowance ι + drift * Xl ι v + Xd ι v with hhi
  have hα := alpha_pos
  have hα1 := five_div_sixteen_le_alpha
  have hα2 := alpha_lt_eight_div_twentyfive
  have hX0 : 0 ≤ X := by rw [hX]; exact_mod_cast (Xd_pos ι v).le
  have hW0 : 0 ≤ W := by rw [hW]; exact_mod_cast (totalAllowance_pos ι v).le
  have hH : (0 : ℝ) ≤ Hpack ι := Nat.cast_nonneg _
  have hq : (0 : ℝ) < qPack := by exact_mod_cast qPack_pos
  have hΓ : (0 : ℝ) < Gammapk := by exact_mod_cast Gammapk_pos
  have hA : 0 < A := by nlinarith
  set i₀ : ℤ := ⌊lo⌋ + 1 with hi₀
  set t : ℕ := (⌈hi⌉ - ⌊lo⌋ - 1).toNat with htdef
  have hlen : hi - lo = 2 * X + alpha * W := by
    simp only [hhi, hlo, hX, hW, totalAllowance_def, drift_def]
    push_cast
    ring
  set B : ℝ := 2 * X + alpha * W + 1 with hBdef
  have htB : (t : ℝ) < B := by
    have h0 := zero_mem_c3AnchorCols_window (ι := ι) (v := v)
    have h1 : ⌊lo⌋ < ⌈hi⌉ := by
      have := Int.floor_le lo
      have := Int.le_ceil hi
      have : (⌊lo⌋ : ℝ) < ⌈hi⌉ := by linarith [h0.1, h0.2]
      exact_mod_cast this
    have hnn : 0 ≤ ⌈hi⌉ - ⌊lo⌋ - 1 := by omega
    rw [htdef, ← Int.cast_natCast, Int.toNat_of_nonneg hnn]
    push_cast
    have := Int.ceil_lt_add_one hi
    have := Int.sub_one_lt_floor lo
    linarith
  set Z : Set ℤ := (fun z ↦ z - bkJ e + i₀) ''
    bkAnchors (bkFamily n ξ epsStar) Δ₀ s (totalAllowance ι v) with hZdef
  have hcover : c3AnchorCols ι (bkFamily n ξ epsStar) e Δ₀ v s ⊆
      {r : ℤ | ∃ z ∈ Z, ∃ i : ℕ, i < t ∧ r = z + i} := by
    rintro r ⟨z, hz, i, h₁, h₂, rfl⟩
    have hi1 : ⌊lo⌋ < i := Int.floor_lt.2 h₁
    have hi2 : i < ⌈hi⌉ := Int.lt_ceil.2 h₂
    refine ⟨z - bkJ e + i₀, ⟨z, hz, rfl⟩, (i - i₀).toNat, ?_, ?_⟩
    · omega
    · rw [Int.toNat_of_nonneg (by omega)]
      ring
  have hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → alpha * A ≤ |(z : ℝ) - z'| := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hne
    have hne' : y ≠ y' := fun h ↦ hne (by rw [h])
    rw [show ((y - bkJ e + i₀ : ℤ) : ℝ) - ((y' - bkJ e + i₀ : ℤ) : ℝ) = (y : ℝ) - y' by
      push_cast; ring]
    have hd0 : 0 < alpha * A := mul_pos hα hA
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · have := sub_gt_of_mem_bkAnchors hξ hs hA hy hy' hlt
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      exact this.le
    · have := sub_gt_of_mem_bkAnchors hξ hs hA hy' hy hlt
      rw [abs_of_pos (by linarith)]
      exact this.le
  have hBB : B ≤ 2 * X + 8 / 25 * W + 1 := by
    have := mul_le_mul_of_nonneg_right hα2.le hW0
    rw [hBdef]; linarith
  have hBd : B + Hpack ι ≤ alpha * A := by
    have := mul_le_mul_of_nonneg_right hα1 hA.le
    linarith
  have hpack := hb.tsum_tsum_c3GoodMarginal_le ι hξ he hω hω34 t htB hBd hsep
  calc ∑' r : c3AnchorCols ι (bkFamily n ξ epsStar) e Δ₀ v s, ∑' ℓ : ℤ,
        c3GoodMarginal ι n ξ e ((r : ℤ), ℓ)
      ≤ ∑' r : {r : ℤ | ∃ z ∈ Z, ∃ i : ℕ, i < t ∧ r = z + i}, ∑' ℓ : ℤ,
        c3GoodMarginal ι n ξ e ((r : ℤ), ℓ) :=
        ENNReal.tsum_mono_subtype (fun r : ℤ ↦ ∑' ℓ : ℤ, c3GoodMarginal ι n ξ e (r, ℓ)) hcover
    _ ≤ _ := hpack
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (add_le_add ?_ ?_)
        · -- `(q (B + H) + Γ/4) / (λ A) ≤ (q C + (127/40)(H q + Γ/4)) / A`
          have he' : (qPack * (B + Hpack ι) + Gammapk / 4 : ℝ) / (alpha * A) =
              (qPack * W + (qPack * (2 * X + 1) + (Hpack ι * qPack + Gammapk / 4)) *
                (1 / alpha)) / A := by
            rw [hBdef]
            field_simp
            ring
          rw [he']
          refine div_le_div_of_nonneg_right ?_ hA.le
          have hP := packConst_lt_Qpack
          have hpos : 0 ≤ (qPack * (2 * X + 1) + (Hpack ι * qPack + Gammapk / 4) : ℝ) := by
            positivity
          have := mul_le_mul_of_nonneg_left hP.le hpos
          linarith
        · -- `4 q (B + H) + Γ ≤ 4 q (B⁺ + H) + Γ` and `(B + H)/(λ A) ≤ (127/40)(B⁺ + H)/A`
          have hsq : 0 ≤ √(ω : ℝ) := Real.sqrt_nonneg _
          have hBH0 : 0 ≤ B + Hpack ι := by
            have : (0 : ℝ) ≤ t := t.cast_nonneg
            linarith
          have hratio : (B + Hpack ι) / (alpha * A) ≤
              127 / 40 * (2 * X + 8 / 25 * W + 1 + Hpack ι) / A := by
            rw [show (B + Hpack ι) / (alpha * A) = (1 / alpha) * ((B + Hpack ι) / A) by
              field_simp, mul_div_assoc]
            have h1 : (B + Hpack ι) / A ≤ (2 * X + 8 / 25 * W + 1 + Hpack ι) / A :=
              div_le_div_of_nonneg_right (by linarith) hA.le
            have h2 : 0 ≤ (B + Hpack ι) / A := div_nonneg hBH0 hA.le
            calc 1 / alpha * ((B + Hpack ι) / A) ≤ 127 / 40 * ((B + Hpack ι) / A) :=
                  mul_le_mul_of_nonneg_right packConst_lt_Qpack.le h2
              _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by norm_num)
          have hf0 : 0 ≤ 4 * (qPack : ℝ) * (B + Hpack ι) + Gammapk := by positivity
          have hg0 : 0 ≤ 1 + (B + Hpack ι) / (alpha * A) := by
            have := div_nonneg hBH0 (mul_pos hα hA).le
            linarith
          refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hsq) (by norm_num)
          refine mul_le_mul (by gcongr) (by linarith) hg0 (by positivity)

end CollatzPosDens
