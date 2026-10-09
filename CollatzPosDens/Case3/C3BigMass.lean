/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkDrift
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.Case3.C3Big
public import CollatzPosDens.Case3.C3Eprime
public import CollatzPosDens.Case3.C3Exc
public import CollatzPosDens.Case3.C3EprimeMass
public import CollatzPosDens.Case3.C3OutsideMass
public import CollatzPosDens.Transfer.Qpack

/-!
# Mass of the large-triangle event

Let `J = ⌊n/2⌋`, `e = (j₀, l₀) ∈ Δ₀ ∈ 𝔗`, `G ∈ ℕ` with `l₀ + G = l_{Δ₀}` and `G ≥ 2^160`,
`v ≤ J`, `X = 136 (v + 1)`, and let `s` be a real number with `4096 X ≤ s` and `s² < 2G`.
Assume `2 G^{3/5} + 2 α X + 1 ≤ G δ₀`. Then
$$\mu_{e,G}(\mathrm{Big}_{e,G,v,s}) \le Q_{\mathrm{pack}}\,\frac Xs + \frac1s + \mathrm{Exc}(v).$$

Since `Big_{e,G,v,s} ⊆ Ex_{e,G,v,X} ∪ (Big_{e,G,v,s} \ Ex_{e,G,v,X})` and all masses are
nonnegative, the mass of `Big` is at most the sum of the masses of the exceptional event, which
is at most `1/s + Exc(v)`, and of `Big \ Ex`, which is less than `Q_pack X / s` (here
`G ≥ 2^160 ≥ 1024` and `X ≥ 1`).

## Main results

* `CollatzPosDens.tsum_trFreshLaw_c3Big_le`: the mass bound, as a sum in `[0, ∞]`.
* `CollatzPosDens.summable_trFreshLaw_c3Big`: the fresh law is summable on `Big`.
* `CollatzPosDens.tsum_trFreshLaw_c3Big_le_real`: the mass bound, as a real sum.

## Implementation notes

The family is `𝔗 = 𝔗_{n,ξ,ε_*}` for a unit `ξ`. The mass `μ_{e,G}(·)` of an event is the
unconditional sum over the subtype of the event of `ENNReal.ofReal (trFreshLaw n e G a)`, which
needs no summability assumption; the real-valued form follows. The parameter `X = 136 (v + 1)`
is substituted in the statement.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.3.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- **Mass of the large-triangle event**. Let `ξ` be a unit, `e = (j₀, l₀) ∈ Δ₀ ∈ 𝔗 = 𝔗_{n,ξ,ε_*}`,
`G ∈ ℕ` with `l₀ + G = l_{Δ₀}` and `G ≥ 2^160`, `v ≤ ⌊n/2⌋`, `X = 136 (v + 1)`, and `s` real
with `4096 X ≤ s` and `s² < 2G`, and assume `2 G^{3/5} + 2 α X + 1 ≤ G δ₀`. Then
`μ_{e,G}(Big_{e,G,v,s}) ≤ Q_pack X / s + 1/s + Exc(v)`. -/
@[collatz_pos_dens "lem_c3_lemma710"]
theorem tsum_trFreshLaw_c3Big_le {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {Δ₀ : BkTriangle} (hΔ₀ : Δ₀ ∈ bkFamily n ξ epsStar) {e : ℤ × ℤ}
    (he : e ∈ Δ₀) {G v : ℕ} (hG : bkL e + G = Δ₀.l) (hG160 : 2 ^ 160 ≤ G) (hv : v ≤ n / 2)
    {s : ℝ} (hs : 4096 * (136 * ((v : ℝ) + 1)) ≤ s) (hsG : s ^ 2 < 2 * G)
    (hGδ : 2 * (G : ℝ) ^ ((3 : ℝ) / 5) + 2 * alpha * (136 * ((v : ℝ) + 1)) + 1 ≤ G * drift) :
    ∑' a : c3Big n ξ epsStar e G v s, ENNReal.ofReal (trFreshLaw n e G a) ≤
      ENNReal.ofReal (Qpack * (136 * ((v : ℝ) + 1) / s) + 1 / s + c3Exc v) := by
  set X : ℤ := 136 * ((v : ℤ) + 1) with hXdef
  have hXr : ((X : ℤ) : ℝ) = 136 * ((v : ℝ) + 1) := by
    rw [hXdef]
    push_cast
    ring
  have hX1 : 1 ≤ X := by omega
  have hs0 : 0 < s := by linarith [(Nat.cast_nonneg v : (0 : ℝ) ≤ v)]
  have hBig := tsum_trFreshLaw_c3Big_diff_c3Exceptional_lt (v := v) hξ hΔ₀ he hG
    (le_trans (by norm_num) hG160) hX1 (s := s) (by rwa [hXr]) hsG (by rwa [hXr])
  rw [hXr] at hBig
  have hEx := tsum_trFreshLaw_c3Exceptional_le (n := n) e hG160 hv hs hsG
  set B := c3Big n ξ epsStar e G v s
  set E := c3Exceptional n e G v (136 * ((v : ℝ) + 1))
  set f : (ℕ × ℤ) × List (List ℤ × ℤ) → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (trFreshLaw n e G a)
  have hsub : B ⊆ E ∪ B \ E := fun a ha ↦ (em (a ∈ E)).imp id fun h ↦ ⟨ha, h⟩
  have hQ : (0 : ℝ) < Qpack := by exact_mod_cast Qpack_pos
  calc ∑' a : B, f a ≤ ∑' a : ↥(E ∪ B \ E), f a := ENNReal.tsum_mono_subtype f hsub
    _ ≤ ∑' a : E, f a + ∑' a : ↥(B \ E), f a := ENNReal.tsum_union_le f E (B \ E)
    _ ≤ ENNReal.ofReal (1 / s + c3Exc v) +
          ENNReal.ofReal (Qpack * (136 * ((v : ℝ) + 1) / s)) := add_le_add hEx hBig.le
    _ = _ := by
        rw [← ENNReal.ofReal_add (by have := c3Exc_pos v; positivity) (by positivity)]
        congr 1
        ring

/-- The fresh law is summable on `Big_{e,G,v,s}`, under the hypotheses of
`tsum_trFreshLaw_c3Big_le`. -/
theorem summable_trFreshLaw_c3Big {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {Δ₀ : BkTriangle} (hΔ₀ : Δ₀ ∈ bkFamily n ξ epsStar) {e : ℤ × ℤ}
    (he : e ∈ Δ₀) {G v : ℕ} (hG : bkL e + G = Δ₀.l) (hG160 : 2 ^ 160 ≤ G) (hv : v ≤ n / 2)
    {s : ℝ} (hs : 4096 * (136 * ((v : ℝ) + 1)) ≤ s) (hsG : s ^ 2 < 2 * G)
    (hGδ : 2 * (G : ℝ) ^ ((3 : ℝ) / 5) + 2 * alpha * (136 * ((v : ℝ) + 1)) + 1 ≤ G * drift) :
    Summable fun a : c3Big n ξ epsStar e G v s ↦ trFreshLaw n e G a :=
  summable_trFreshLaw_of_tsum_ofReal_ne_top
    ((tsum_trFreshLaw_c3Big_le hξ hΔ₀ he hG hG160 hv hs hsG hGδ).trans_lt
      ENNReal.ofReal_lt_top).ne

/-- **Mass of the large-triangle event**, as a real sum:
`μ_{e,G}(Big_{e,G,v,s}) ≤ Q_pack X / s + 1/s + Exc(v)` with `X = 136 (v + 1)`. -/
theorem tsum_trFreshLaw_c3Big_le_real {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {Δ₀ : BkTriangle} (hΔ₀ : Δ₀ ∈ bkFamily n ξ epsStar) {e : ℤ × ℤ}
    (he : e ∈ Δ₀) {G v : ℕ} (hG : bkL e + G = Δ₀.l) (hG160 : 2 ^ 160 ≤ G) (hv : v ≤ n / 2)
    {s : ℝ} (hs : 4096 * (136 * ((v : ℝ) + 1)) ≤ s) (hsG : s ^ 2 < 2 * G)
    (hGδ : 2 * (G : ℝ) ^ ((3 : ℝ) / 5) + 2 * alpha * (136 * ((v : ℝ) + 1)) + 1 ≤ G * drift) :
    ∑' a : c3Big n ξ epsStar e G v s, trFreshLaw n e G a ≤
      Qpack * (136 * ((v : ℝ) + 1) / s) + 1 / s + c3Exc v := by
  have hs0 : 0 < s := by linarith [(Nat.cast_nonneg v : (0 : ℝ) ≤ v)]
  have h := tsum_trFreshLaw_c3Big_le hξ hΔ₀ he hG hG160 hv hs hsG hGδ
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ trFreshLaw_nonneg _ _ _ _)
    (summable_trFreshLaw_c3Big hξ hΔ₀ he hG hG160 hv hs hsG hGδ)] at h
  have hQ : (0 : ℝ) < Qpack := by exact_mod_cast Qpack_pos
  exact (ENNReal.ofReal_le_ofReal_iff (by have := c3Exc_pos v; positivity)).1 h

end CollatzPosDens
