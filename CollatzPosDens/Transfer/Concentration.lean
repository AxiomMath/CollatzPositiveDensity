/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Transfer.MgfBound
public import CollatzPosDens.FirstCrossing.FcMgf

/-!
# Concentration of the valuation sum under the geometric mass

Under the geometric mass `𝐩`, the letters of a word of length `t` behave like independent
geometric variables with `P(a) = 2^{-a}` and mean `2`, so the valuation sum `A(w)` concentrates
around `2t`. Precisely, for every `t ≥ 1` and real `v ≥ 0`,
$$\mathbf p(\{w \in \mathbb Z_{\ge 1}^t : |A(w) - 2t| \ge v\})
  \le 2 \exp\Bigl(-\min\Bigl\{\frac{v^2}{32t}, \frac v8\Bigr\}\Bigr).$$

The proof is a Chernoff bound: the exponential moment of `A(w) - 2t` factorises over the
letters (Tonelli), each factor is bounded by the moment generating function bound
`∑_{a ≥ 1} 2^{-a} e^{θ(a-2)} ≤ e^{8θ²}` for `|θ| ≤ 1/4`, and the choice
`θ = min {v/(16t), 1/4}` optimises the resulting exponent `8tθ² - θv`.

## Main results

* `CollatzPosDens.geomMass_abs_valSum_sub_ge_le`: the two-sided tail bound
  `𝐩(|A(w) - 2t| ≥ v) ≤ 2 exp(-min {v²/(32t), v/8})`.
* `CollatzPosDens.concentrationMgf_eq_ofReal`: for `e^θ < 2` the moment generating function is
  the real series `∑_{a ≥ 0} 2^{-(a+1)} e^{θ(a-1)}`.

## Implementation notes

The bound is stated in `ℝ≥0∞` with right-hand side `ENNReal.ofReal (2 * exp (-min …))`. The
hypothesis `t ≥ 1` is dropped: for `t = 0` Lean's convention `v² / 0 = 0` makes
the right-hand side `2`, and the bound still holds.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal
open Real

namespace CollatzPosDens

/-- The geometric moment generating function `∑_{a ≥ 1} 2^{-a} e^{θ(a-2)}`, in `ℝ≥0∞`. -/
noncomputable def concentrationMgf (θ : ℝ) : ℝ≥0∞ :=
  ∑' a : ℕ+, (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * ENNReal.ofReal (exp (θ * ((a : ℕ) - 2 : ℝ)))

/-- For `e^θ < 2` the moment generating function is the real series
`∑_{a ≥ 0} (1/2)^{a+1} e^{θ((a+1) - 2)}`. -/
theorem concentrationMgf_eq_ofReal {θ : ℝ} (h : exp θ < 2) :
    concentrationMgf θ =
      ENNReal.ofReal (∑' a : ℕ, (1 / 2 : ℝ) ^ (a + 1) * exp (θ * (((a + 1 : ℕ) : ℝ) - 2))) := by
  rw [concentrationMgf, tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ n * ENNReal.ofReal (exp (θ * ((n : ℝ) - 2)))),
    ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (fcMgf_hasSum h).summable]
  congr 1
  funext n
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  congr 2
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

/-- The exponential moment of `A(w) - 2t` over the words of length `t` factorises:
`∑_{|w| = t} 2^{-A(w)} e^{θ(A(w) - 2t)} = (∑_{a ≥ 1} 2^{-a} e^{θ(a-2)})^t`. -/
theorem tsum_massWeight_mul_exp_valSum (θ : ℝ) (t : ℕ) :
    ∑' w : {w : Word | w.length = t},
        (w : Word).massWeight * ENNReal.ofReal (exp (θ * ((w : Word).valSum - 2 * t : ℝ))) =
      concentrationMgf θ ^ t := by
  induction t with
  | zero =>
    rw [show {w : Word | w.length = 0} = {[]} by ext; simp]
    simp [Word.massWeight]
  | succ t ih =>
    rw [← (Word.consLengthEquiv t).tsum_eq]
    simp only [Word.consLengthEquiv, Equiv.coe_fn_mk, Word.massWeight, Word.valSum_cons]
    have key : ∀ (a : ℕ+) (w : {w : Word | w.length = t}),
        (2⁻¹ : ℝ≥0∞) ^ ((a : ℕ) + (w : Word).valSum) *
            ENNReal.ofReal (exp (θ * ((((a : ℕ) + (w : Word).valSum : ℕ) : ℝ) -
              2 * ((t + 1 : ℕ) : ℝ)))) =
          ((2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * ENNReal.ofReal (exp (θ * ((a : ℕ) - 2 : ℝ)))) *
            ((2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum *
              ENNReal.ofReal (exp (θ * ((w : Word).valSum - 2 * t : ℝ)))) := by
      intro a w
      have : θ * ((((a : ℕ) + (w : Word).valSum : ℕ) : ℝ) - 2 * ((t + 1 : ℕ) : ℝ)) =
          θ * ((a : ℕ) - 2 : ℝ) + θ * ((w : Word).valSum - 2 * t : ℝ) := by
        push_cast
        ring
      rw [this, exp_add, ENNReal.ofReal_mul (exp_pos _).le, pow_add]
      ring
    simp_rw [key]
    rw [ENNReal.tsum_prod (f := fun (a : ℕ+) (w : {w : Word | w.length = t}) =>
      ((2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * ENNReal.ofReal (exp (θ * ((a : ℕ) - 2 : ℝ)))) *
        ((2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum *
          ENNReal.ofReal (exp (θ * ((w : Word).valSum - 2 * t : ℝ)))))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ih, ENNReal.tsum_mul_right, pow_succ, concentrationMgf]
    ring

/-- `e^{1/4} < 2`. -/
private lemma concentration_exp_quarter_lt_two : exp (1 / 4) < 2 := by
  have := exp_bound_div_one_sub_of_interval' (x := 1 / 4) (by norm_num) (by norm_num)
  linarith [show (1 : ℝ) / (1 - 1 / 4) < 2 by norm_num]

/-- For `|θ| ≤ 1/4`, the geometric moment generating function is at most `e^{8θ²}`. -/
theorem concentrationMgf_le (θ : ℝ) (hθ : |θ| ≤ 1 / 4) :
    concentrationMgf θ ≤ ENNReal.ofReal (exp (8 * θ ^ 2)) := by
  have hθ' : θ ≤ 1 / 4 := (le_abs_self θ).trans hθ
  have he : exp θ < 2 := (exp_le_exp.2 hθ').trans_lt concentration_exp_quarter_lt_two
  set f : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n + 1) * exp (θ * (((n + 1 : ℕ) : ℝ) - 2)) with hf
  have hterm : ∀ n : ℕ, f n = exp (-θ) / 2 * (exp θ / 2) ^ n := by
    intro n
    have : θ * (((n + 1 : ℕ) : ℝ) - 2) = n * θ + -θ := by
      push_cast
      ring
    simp only [hf]
    rw [this, exp_add, exp_nat_mul, div_pow, pow_succ, inv_pow]
    field_simp
  have hsum : Summable f :=
    ((summable_geometric_of_lt_one (by positivity) (by linarith)).mul_left
      (exp (-θ) / 2)).congr fun n => (hterm n).symm
  rw [concentrationMgf, tsum_pnat_eq_tsum_succ
    (f := fun n => (2⁻¹ : ℝ≥0∞) ^ n * ENNReal.ofReal (exp (θ * ((n : ℝ) - 2))))]
  have hcongr : ∀ n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) *
      ENNReal.ofReal (exp (θ * (((n + 1 : ℕ) : ℝ) - 2))) = ENNReal.ofReal (f n) := by
    intro n
    simp only [hf]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  simp_rw [hcongr]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum]
  exact ENNReal.ofReal_le_ofReal (tsum_geometric_mul_exp_le θ hθ)

/-- **One-sided Chernoff bound.** For a sign `s` (`|s| = 1`) and `0 ≤ θ ≤ 1/4`,
`𝐩({|w| = t, s (A(w) - 2t) ≥ v}) ≤ e^{8tθ² - θv}`. -/
theorem geomMass_sign_valSum_sub_ge_le (t : ℕ) (v s θ : ℝ) (hs : |s| = 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 1 / 4) :
    geomMass {w : Word | w.length = t ∧ v ≤ s * ((w.valSum : ℝ) - 2 * t)} ≤
      ENNReal.ofReal (exp (8 * t * θ ^ 2 - θ * v)) := by
  set L := {w : Word | w.length = t}
  set S := {w : Word | w.length = t ∧ v ≤ s * ((w.valSum : ℝ) - 2 * t)}
  let g : Word → ℝ≥0∞ := fun w =>
    w.massWeight * ENNReal.ofReal (exp ((s * θ) * (w.valSum - 2 * t : ℝ))) *
      ENNReal.ofReal (exp (-(θ * v)))
  have hle : ∀ w : S, (w : Word).massWeight ≤ g w := by
    intro w
    have h1 : 1 ≤ ENNReal.ofReal (exp ((s * θ) * ((w : Word).valSum - 2 * t : ℝ))) *
        ENNReal.ofReal (exp (-(θ * v))) := by
      rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [one_le_exp_iff]
      nlinarith [w.2.2]
    exact (le_mul_of_one_le_right' h1).trans_eq (mul_assoc _ _ _).symm
  calc geomMass S = ∑' w : S, (w : Word).massWeight := geomMass_def S
    _ ≤ ∑' w : S, g w := ENNReal.tsum_le_tsum hle
    _ ≤ ∑' w : L, g w := ENNReal.tsum_mono_subtype g fun _ hw => hw.1
    _ = concentrationMgf (s * θ) ^ t * ENNReal.ofReal (exp (-(θ * v))) := by
      rw [ENNReal.tsum_mul_right, tsum_massWeight_mul_exp_valSum]
    _ ≤ ENNReal.ofReal (exp (8 * (s * θ) ^ 2)) ^ t * ENNReal.ofReal (exp (-(θ * v))) := by
      gcongr
      exact concentrationMgf_le _ (by rwa [abs_mul, hs, abs_of_nonneg hθ0, one_mul])
    _ = ENNReal.ofReal (exp (8 * t * θ ^ 2 - θ * v)) := by
      rw [← ENNReal.ofReal_pow (exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
        ← exp_nat_mul, ← exp_add]
      congr 2
      rw [mul_pow, ← sq_abs s, hs, one_pow]
      ring

/-- The exponent `8tθ² - θv` at `θ = min {v/(16t), 1/4}` is at most
`-min {v²/(32t), v/8}`. -/
private lemma concentration_exponent_le (t : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    8 * t * (min (v / (16 * t)) (1 / 4)) ^ 2 - min (v / (16 * t)) (1 / 4) * v ≤
      -min (v ^ 2 / (32 * t)) (v / 8) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp only [Nat.cast_zero, mul_zero, div_zero]
    rw [min_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 4), min_eq_left (by positivity)]
    simp
  have hT : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  rcases le_or_gt v (4 * t) with h | h
  · have hθ : v / (16 * t) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    rw [min_eq_left hθ]
    have : 8 * t * (v / (16 * t)) ^ 2 - v / (16 * t) * v = -(v ^ 2 / (32 * t)) := by
      field_simp
      ring
    rw [this]
    exact neg_le_neg (min_le_left _ _)
  · have hθ : 1 / 4 ≤ v / (16 * t) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    rw [min_eq_right hθ]
    have := min_le_right (v ^ 2 / (32 * t)) (v / 8)
    nlinarith

/-- The words of length `t` whose valuation sum deviates from `2t` by at least `v`: the event of
the concentration bound `geomMass_abs_valSum_sub_ge_le`. -/
abbrev valSumDevSet (v : ℝ) (t : ℕ) : Set Word :=
  {p : Word | p.length = t ∧ v ≤ |(p.valSum : ℝ) - 2 * t|}

/-- **Concentration of the valuation sum.** For every `t` and real `v ≥ 0`,
`𝐩({w ∈ ℤ_{≥1}^t : |A(w) - 2t| ≥ v}) ≤ 2 exp (-min {v²/(32t), v/8})`. -/
@[collatz_pos_dens "lem_concentration"]
theorem geomMass_abs_valSum_sub_ge_le (t : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    geomMass {w : Word | w.length = t ∧ v ≤ |(w.valSum : ℝ) - 2 * t|} ≤
      ENNReal.ofReal (2 * exp (-min (v ^ 2 / (32 * t)) (v / 8))) := by
  set θ := min (v / (16 * t)) (1 / 4)
  have hθ0 : 0 ≤ θ := le_min (by positivity) (by norm_num)
  have hθ : θ ≤ 1 / 4 := min_le_right _ _
  have hexp : ENNReal.ofReal (exp (8 * t * θ ^ 2 - θ * v)) ≤
      ENNReal.ofReal (exp (-min (v ^ 2 / (32 * t)) (v / 8))) :=
    ENNReal.ofReal_le_ofReal (exp_le_exp.2 (concentration_exponent_le t v hv))
  have hsub : {w : Word | w.length = t ∧ v ≤ |(w.valSum : ℝ) - 2 * t|} ⊆
      {w : Word | w.length = t ∧ v ≤ 1 * ((w.valSum : ℝ) - 2 * t)} ∪
        {w : Word | w.length = t ∧ v ≤ -1 * ((w.valSum : ℝ) - 2 * t)} := by
    rintro w ⟨hl, hw⟩
    rcases le_abs'.1 hw with h | h
    · exact Or.inr ⟨hl, by linarith⟩
    · exact Or.inl ⟨hl, by linarith⟩
  calc _ ≤ _ := geomMass_mono hsub
    _ ≤ _ := geomMass_union_le _ _
    _ ≤ ENNReal.ofReal (exp (-min (v ^ 2 / (32 * t)) (v / 8))) +
        ENNReal.ofReal (exp (-min (v ^ 2 / (32 * t)) (v / 8))) := by
      gcongr
      · exact (geomMass_sign_valSum_sub_ge_le t v 1 θ (by simp) hθ0 hθ).trans hexp
      · exact (geomMass_sign_valSum_sub_ge_le t v (-1) θ (by simp) hθ0 hθ).trans hexp
    _ = _ := by
      rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le, two_mul]

end CollatzPosDens
