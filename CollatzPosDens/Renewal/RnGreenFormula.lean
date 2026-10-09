/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnGreen
public import CollatzPosDens.Renewal.RnGreenClosed
public import CollatzPosDens.Renewal.RnGreenFinite
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldFinite
public import CollatzPosDens.Renewal.RnHoldList
public import CollatzPosDens.Renewal.RnHoldWords
public import CollatzPosDens.Renewal.RnRawMass
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The Green's function in closed form

For all `(j, s) ∈ ℤ × ℤ`, the Green's function of the holding-time law equals its closed form:
`𝒢(j, s) = 𝒢ᶜˡ(j, s)`. That is, `𝒢(0, 0) = 1`, `𝒢(j, s) = 0` for `j ≤ 0` and
`(j, s) ≠ (0, 0)`, and `𝒢(j, s) = ϖ(4) 𝖱(j - 1, s - 4) + ϖ(5) 𝖱(j - 1, s - 5)` for `j ≥ 1`.

Expanding each holding time into its hold word, `𝒢(j, s)` for `j ≥ 1` is the total weight
`∏_k ϖ(c_k)` of the words `c ∈ ℤ^j` with letters `≥ 2`, letter sum `s` and last letter in
`{4, 5}`; splitting according to the last letter gives the closed form.

## Main results

* `CollatzPosDens.green_eq_greenClosed`: `𝒢(j, s) = 𝒢ᶜˡ(j, s)` for all `(j, s) ∈ ℤ × ℤ`.

## Implementation notes

Rather than cutting words into blocks, the proof derives a letter recursion algebraically. Write
`ϖ = ϖ_in + ϖ_last`, where `ϖ_last` is `ϖ` restricted to `{4, 5}` and `ϖ_in` is `ϖ` restricted
to the complement. Splitting off the first letter of a hold word gives
`η = ϖ_last ⊗ δ_1 + (ϖ_in ⊗ δ_1) * η` on `𝒫`; the first-step decomposition of a hold list gives
`𝒢 = δ + R` with `R = η * 𝒢`. Together, `R = ϖ_last ⊗ δ_1 + (ϖ ⊗ δ_1) * R`, and the closed form
satisfies the same recursion in `j` by the convolution recursion of the raw-prefix mass `𝖱`.
These identities are proved in `ℝ≥0∞`, where all sums may be rearranged freely; `𝒢` is the real
part of its `ℝ≥0∞` counterpart because its defining family has finite support
(`CollatzPosDens.green_finite`). The two functions then agree by induction on `j`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-! ### The raw-prefix mass as a convolution in `ℝ≥0∞` -/

private lemma greenFormula_tsum_rawMass (k : ℕ) (t : ℤ) :
    ∑' b : ℤ, ENNReal.ofReal (varpi b) * ENNReal.ofReal (rawMass k (t - b)) =
      ENNReal.ofReal (rawMass (k + 1) t) := by
  rw [rawMass_succ, ENNReal.ofReal_sum_of_nonneg
    (fun a _ => mul_nonneg (varpi_nonneg _) (rawMass_nonneg _ _)),
    tsum_eq_sum (s := Finset.Icc 2 t)]
  · exact Finset.sum_congr rfl fun a _ => (ENNReal.ofReal_mul (varpi_nonneg _)).symm
  · intro b hb
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hb
    rcases hb with hb | hb
    · rw [varpi_of_le_one (by omega)]
      simp
    · rw [rawMass_of_neg _ (by omega)]
      simp

/-! ### The holding-time law, letter by letter -/

private lemma greenFormula_ofReal_holdLaw (n : ℕ) (l : ℤ) :
    ENNReal.ofReal (holdLaw n l) =
      ∑' c : Fin n → ℤ,
        (holdWords n l).indicator (fun c => ENNReal.ofReal (∏ i, varpi (c i))) c := by
  have := (holdWords_finite n l).to_subtype
  rw [holdLaw_def, ENNReal.ofReal_tsum_of_nonneg
    (fun _ => Finset.prod_nonneg fun _ _ => varpi_nonneg _) Summable.of_finite]
  exact tsum_subtype (holdWords n l) fun c => ENNReal.ofReal (∏ i, varpi (c i))

private lemma greenFormula_holdLaw_one (l : ℤ) :
    ENNReal.ofReal (holdLaw 1 l) = ENNReal.ofReal (varpiLast l) := by
  rw [greenFormula_ofReal_holdLaw, ← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq,
    tsum_eq_single l]
  · by_cases h : l ∈ ({4, 5} : Set ℤ)
    · rw [Set.indicator_of_mem, varpiLast_of_mem h]
      · simp
      · obtain h | h : l = 4 ∨ l = 5 := h <;> simp [mem_holdWords, h]
    · rw [Set.indicator_of_notMem, varpiLast_of_notMem h]
      · simp
      · simp only [mem_holdWords]
        rintro ⟨-, -, h45, -⟩
        exact h (by simpa using h45 0 rfl)
  · intro b hb
    rw [Set.indicator_of_notMem]
    simp only [mem_holdWords]
    rintro ⟨-, -, -, hs⟩
    exact hb (by simpa using hs)

private lemma greenFormula_cons_mem (n : ℕ) (l b : ℤ) (c : Fin (n + 1) → ℤ) :
    (Fin.cons b c : Fin (n + 2) → ℤ) ∈ holdWords (n + 2) l ↔
      (2 ≤ b ∧ ¬ (b = 4 ∨ b = 5)) ∧ c ∈ holdWords (n + 1) (l - b) := by
  simp only [mem_holdWords, Fin.forall_fin_succ (n := n + 1), Fin.cons_zero, Fin.cons_succ,
    Fin.sum_cons, Fin.val_zero, Fin.val_succ, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨h0, h2⟩, ⟨n0, n1⟩, ⟨-, e1⟩, hs⟩
    exact ⟨⟨h0, n0 (by omega)⟩, h2, fun i hi => n1 i (by omega), fun i hi => e1 i (by omega),
      by linarith⟩
  · rintro ⟨⟨h0, n0⟩, h2, n1, e1, hs⟩
    exact ⟨⟨h0, h2⟩, ⟨fun _ => n0, fun i hi => n1 i (by omega)⟩,
      ⟨fun h => by omega, fun i hi => e1 i (by omega)⟩, by linarith⟩

private lemma greenFormula_holdLaw_succ_succ (n : ℕ) (l : ℤ) :
    ENNReal.ofReal (holdLaw (n + 2) l) =
      ∑' b : ℤ,
        ENNReal.ofReal (varpiIn b) * ENNReal.ofReal (holdLaw (n + 1) (l - b)) := by
  simp only [greenFormula_ofReal_holdLaw, ← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod (f := fun b (c : Fin (n + 1) → ℤ) =>
      ENNReal.ofReal (varpiIn b) *
        (holdWords (n + 1) (l - b)).indicator (fun c => ENNReal.ofReal (∏ i, varpi (c i))) c),
    ← (Fin.consEquiv fun _ : Fin (n + 2) => ℤ).tsum_eq]
  refine tsum_congr fun p => ?_
  obtain ⟨b, c⟩ := p
  rw [show (Fin.consEquiv fun _ : Fin (n + 2) => ℤ) (b, c) = Fin.cons b c from rfl]
  by_cases h : (2 ≤ b ∧ ¬ (b = 4 ∨ b = 5)) ∧ c ∈ holdWords (n + 1) (l - b)
  · rw [Set.indicator_of_mem ((greenFormula_cons_mem n l b c).2 h), Set.indicator_of_mem h.2,
      ← ENNReal.ofReal_mul (varpiIn_nonneg b), Fin.prod_univ_succ, Fin.cons_zero,
      varpiIn_of_notMem h.1.2]
    simp only [Fin.cons_succ]
  · rw [Set.indicator_of_notMem (mt (greenFormula_cons_mem n l b c).1 h)]
    by_cases hc : c ∈ holdWords (n + 1) (l - b)
    · have : varpiIn b = 0 := by
        by_cases h45 : b ∈ ({4, 5} : Set ℤ)
        · exact varpiIn_of_mem h45
        · rw [varpiIn_of_notMem h45]
          exact varpi_of_le_one (by
            by_contra hb
            exact h ⟨⟨by omega, h45⟩, hc⟩)
      simp [this]
    · simp [Set.indicator_of_notMem hc]

/-- The holding-time law on `ℤ × ℤ`, extended by `0` outside `𝒫`, in `ℝ≥0∞`. -/
private noncomputable def greenFormulaEta (p : ℤ × ℤ) : ℝ≥0∞ :=
  if 1 ≤ p.1 then ENNReal.ofReal (holdLaw p.1.toNat p.2) else 0

private lemma greenFormula_one_le_of_eta_ne_zero {p : ℤ × ℤ} (h : greenFormulaEta p ≠ 0) :
    1 ≤ p.1 := by
  by_contra hp
  exact h (by simp [greenFormulaEta, hp])

/-- The first-letter recursion `η = ϖ_last ⊗ δ_1 + (ϖ_in ⊗ δ_1) * η`. -/
private lemma greenFormula_eta_eq (a : ℤ × ℤ) :
    greenFormulaEta a = (if a.1 = 1 then ENNReal.ofReal (varpiLast a.2) else 0) +
      ∑' b : ℤ, ENNReal.ofReal (varpiIn b) * greenFormulaEta (a - (1, b)) := by
  obtain ⟨j, l⟩ := a
  have hsub : ∀ b : ℤ, ((j, l) - (1, b) : ℤ × ℤ) = (j - 1, l - b) := fun b ↦ rfl
  simp only [hsub]
  rcases lt_trichotomy j 1 with hj | rfl | hj
  · simp [greenFormulaEta, show ¬ 1 ≤ j by omega, show ¬ 1 ≤ j - 1 by omega,
      show j ≠ 1 by omega]
  · simp [greenFormulaEta, greenFormula_holdLaw_one]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = (n : ℤ) + 2 := ⟨(j - 2).toNat, by omega⟩
    simp only [greenFormulaEta, show (1 : ℤ) ≤ n + 2 by omega, show (1 : ℤ) ≤ n + 2 - 1 by omega,
      ite_true, show (n : ℤ) + 2 ≠ 1 by omega, ite_false, zero_add]
    rw [show ((n : ℤ) + 2).toNat = n + 2 by omega, show ((n : ℤ) + 2 - 1).toNat = n + 1 by omega]
    exact greenFormula_holdLaw_succ_succ n l

/-! ### The Green's function as a sum in `ℝ≥0∞` -/

/-- The Green's function as a sum over all tuples in `(ℤ × ℤ)^N`, in `ℝ≥0∞`. -/
private noncomputable def greenFormulaG (x : ℤ × ℤ) : ℝ≥0∞ :=
  ∑' N : ℕ, ∑' h : Fin N → ℤ × ℤ, if ∑ i, h i = x then ∏ i, greenFormulaEta (h i) else 0

/-- The embedding `ℕ × ℤ → ℤ × ℤ`. -/
private def greenFormulaCast (p : ℕ × ℤ) : ℤ × ℤ := ((p.1 : ℤ), p.2)

private lemma greenFormula_G_eq_ofReal (j s : ℤ) :
    greenFormulaG (j, s) = ENNReal.ofReal (green j s) := by
  rw [green_def, ENNReal.ofReal_tsum_of_nonneg
    (fun N => tsum_nonneg fun h => holdListLaw_nonneg _)
    (summable_of_hasFiniteSupport (green_finite_support_outer j s))]
  refine tsum_congr fun N => ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun h => holdListLaw_nonneg _)
    (summable_of_hasFiniteSupport (green_finite_support j s N))]
  refine Eq.trans ?_ (tsum_subtype {h : Fin N → ℕ × ℤ |
      (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).1 : ℤ) = j ∧ ∑ i, (h i).2 = s}
    (fun h => ENNReal.ofReal (holdListLaw h))).symm
  have hinj : Function.Injective fun (h : Fin N → ℕ × ℤ) i => greenFormulaCast (h i) := by
    intro h h' e
    funext i
    have := congrFun e i
    simp only [greenFormulaCast, Prod.mk.injEq, Nat.cast_inj] at this
    exact Prod.ext this.1 this.2
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun h => ?_
    have hsum : (∑ i, greenFormulaCast (h i) = (j, s)) ↔
        ∑ i, ((h i).1 : ℤ) = j ∧ ∑ i, (h i).2 = s := by
      simp [greenFormulaCast, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]
    by_cases hP : ∀ i, 1 ≤ (h i).1
    · have hprod : ∏ i, greenFormulaEta (greenFormulaCast (h i)) =
          ENNReal.ofReal (holdListLaw h) := by
        rw [holdListLaw_def, ENNReal.ofReal_prod_of_nonneg fun i _ => holdLaw_nonneg _ _]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp [greenFormulaEta, greenFormulaCast, show (1 : ℤ) ≤ (h i).1 by exact_mod_cast hP i]
      simp only [hsum, hprod, Set.indicator, Set.mem_ofPred_eq, hP, implies_true, true_and]
    · push Not at hP
      obtain ⟨i, hi⟩ := hP
      have h0 : ∏ i, greenFormulaEta (greenFormulaCast (h i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by
          simp [greenFormulaEta, greenFormulaCast]
          omega)
      rw [h0, ite_self, Set.indicator_of_notMem]
      exact fun hh => absurd (hh.1 i) (by omega)
  · intro h' hh
    have hne : ∏ i, greenFormulaEta (h' i) ≠ 0 := fun h0 => hh (by simp [h0])
    have h1 := fun i =>
      greenFormula_one_le_of_eta_ne_zero (Finset.prod_ne_zero_iff.1 hne i (Finset.mem_univ _))
    refine ⟨fun i => ((h' i).1.toNat, (h' i).2), funext fun i => ?_⟩
    have := h1 i
    simp only [greenFormulaCast]
    exact Prod.ext (by simp; omega) rfl

private lemma greenFormula_G_of_neg {x : ℤ × ℤ} (hx : x.1 < 0) : greenFormulaG x = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun N => ENNReal.tsum_eq_zero.2 fun h => ?_
  split_ifs with hs
  · by_contra hne
    have h1 := fun i =>
      greenFormula_one_le_of_eta_ne_zero (Finset.prod_ne_zero_iff.1 hne i (Finset.mem_univ _))
    have : 0 ≤ (∑ i, h i).1 := by
      rw [Prod.fst_sum]
      exact Finset.sum_nonneg fun i _ => by linarith [h1 i]
    rw [hs] at this
    omega
  · rfl

/-- First-step decomposition: `𝒢 = δ + η * 𝒢`. -/
private lemma greenFormula_G_eq (x : ℤ × ℤ) :
    greenFormulaG x =
      (if x = 0 then 1 else 0) + ∑' a, greenFormulaEta a * greenFormulaG (x - a) := by
  rw [greenFormulaG, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  · rw [tsum_fintype]
    simp [eq_comm]
  · simp only [greenFormulaG, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun N => ?_
    rw [← (Fin.consEquiv fun _ : Fin (N + 1) => ℤ × ℤ).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun a => tsum_congr fun t => ?_
    rw [show (Fin.consEquiv fun _ : Fin (N + 1) => ℤ × ℤ) (a, t) = Fin.cons a t from rfl]
    simp only [Fin.sum_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    by_cases h : a + ∑ i, t i = x
    · rw [ite_eq_left h, ite_eq_left (eq_sub_of_add_eq' h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h']; abel)), mul_zero]

/-- The contribution `R(x) = ∑_a η(a) 𝒢(x - a)` of the nonempty tuples to `𝒢(x)`. -/
private noncomputable def greenFormulaR (x : ℤ × ℤ) : ℝ≥0∞ :=
  ∑' a, greenFormulaEta a * greenFormulaG (x - a)

private lemma greenFormula_G_eq_R (x : ℤ × ℤ) :
    greenFormulaG x = (if x = 0 then 1 else 0) + greenFormulaR x :=
  greenFormula_G_eq x

private lemma greenFormula_R_of_nonpos {x : ℤ × ℤ} (hx : x.1 ≤ 0) : greenFormulaR x = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun a => ?_
  by_cases ha : 1 ≤ a.1
  · rw [greenFormula_G_of_neg (by simp only [Prod.fst_sub]; omega), mul_zero]
  · simp [greenFormulaEta, ha]

/-- The letter recursion `R = ϖ_last ⊗ δ_1 + (ϖ ⊗ δ_1) * R`. -/
private lemma greenFormula_R_eq (x : ℤ × ℤ) :
    greenFormulaR x = (if x.1 = 1 then ENNReal.ofReal (varpiLast x.2) else 0) +
      ∑' b : ℤ, ENNReal.ofReal (varpi b) * greenFormulaR (x - (1, b)) := by
  have hshift : ∀ b : ℤ, ∑' a, greenFormulaEta (a - (1, b)) * greenFormulaG (x - a) =
      greenFormulaR (x - (1, b)) := by
    intro b
    rw [greenFormulaR, ← (Equiv.addRight ((1, b) : ℤ × ℤ)).tsum_eq]
    refine tsum_congr fun a => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    congr 2
    abel
  have hfirst : ∑' a : ℤ × ℤ, (if a.1 = 1 then ENNReal.ofReal (varpiLast a.2) else 0) *
      greenFormulaG (x - a) =
        ∑' l : ℤ, ENNReal.ofReal (varpiLast l) * greenFormulaG (x - (1, l)) := by
    rw [ENNReal.tsum_prod', tsum_eq_single (1 : ℤ) fun j hj => by simp [hj]]
    simp
  have hdelta : ∑' l : ℤ, ENNReal.ofReal (varpiLast l) *
      (if x - (1, l) = 0 then 1 else 0) =
        if x.1 = 1 then ENNReal.ofReal (varpiLast x.2) else 0 := by
    by_cases hx : x.1 = 1
    · rw [ite_eq_left hx, tsum_eq_single x.2]
      · rw [ite_eq_left (by ext <;> simp [hx]), mul_one]
      · intro l hl
        rw [ite_eq_right (fun h => hl (by have := congrArg Prod.snd h; simp at this; omega)),
          mul_zero]
    · rw [ite_eq_right hx]
      refine ENNReal.tsum_eq_zero.2 fun l => ?_
      rw [ite_eq_right (fun h => hx (by have := congrArg Prod.fst h; simp at this; omega)),
        mul_zero]
  calc greenFormulaR x
      = ∑' a, ((if a.1 = 1 then ENNReal.ofReal (varpiLast a.2) else 0) *
            greenFormulaG (x - a) +
          ∑' b : ℤ, ENNReal.ofReal (varpiIn b) *
            (greenFormulaEta (a - (1, b)) * greenFormulaG (x - a))) := by
        refine tsum_congr fun a => ?_
        rw [greenFormula_eta_eq a, add_mul, ← ENNReal.tsum_mul_right]
        simp only [mul_assoc]
    _ = ∑' l : ℤ, ENNReal.ofReal (varpiLast l) * greenFormulaG (x - (1, l)) +
          ∑' b : ℤ, ENNReal.ofReal (varpiIn b) * greenFormulaR (x - (1, b)) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_comm (f := fun a b => ENNReal.ofReal
          (varpiIn b) * (greenFormulaEta (a - (1, b)) * greenFormulaG (x - a))), hfirst]
        congr 1
        refine tsum_congr fun b => ?_
        rw [ENNReal.tsum_mul_left, hshift]
    _ = _ := by
        simp only [greenFormula_G_eq_R (x - _), mul_add, ENNReal.tsum_add, hdelta,
          ← varpiLast_add_varpiIn,
          ENNReal.ofReal_add (varpiLast_nonneg _) (varpiIn_nonneg _), add_mul]
        ring

/-- The closed form at `j = 1`: `𝒢ᶜˡ(1, s) = ϖ_last(s)`. -/
private lemma greenFormula_greenClosed_one (s : ℤ) :
    greenClosed ((0 : ℕ) + 1 : ℤ) s = varpiLast s := by
  rw [greenClosed_succ, rawMass_zero, rawMass_zero]
  simp only [varpiLast, Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases h4 : s = 4
  · subst h4
    norm_num
  by_cases h5 : s = 5
  · subst h5
    norm_num
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  ring

/-- `R(n + 1, s) = 𝒢ᶜˡ(n + 1, s)` for `n ∈ ℕ`, in `ℝ≥0∞`. -/
private lemma greenFormula_R_natCast_succ (n : ℕ) (s : ℤ) :
    greenFormulaR ((n : ℤ) + 1, s) = ENNReal.ofReal (greenClosed ((n : ℤ) + 1) s) := by
  induction n generalizing s with
  | zero =>
    have hx : ∀ b : ℤ, (((0 : ℕ) : ℤ) + 1, s) - (1, b) = (((0 : ℕ) : ℤ), s - b) :=
      fun b => by ext <;> simp
    have h0 : ∀ b : ℤ, greenFormulaR (((0 : ℕ) : ℤ), s - b) = 0 := fun b =>
      greenFormula_R_of_nonpos (by simp)
    rw [greenFormula_R_eq]
    simp only [hx, h0, mul_zero, tsum_zero, add_zero]
    rw [ite_eq_left (by simp), greenFormula_greenClosed_one]
  | succ n ih =>
    have hx : ∀ b : ℤ, (((n + 1 : ℕ) : ℤ) + 1, s) - (1, b) = ((n : ℤ) + 1, s - b) :=
      fun b => by ext <;> simp
    rw [greenFormula_R_eq, ite_eq_right (by push_cast; omega), zero_add]
    simp only [hx, ih, greenClosed_succ]
    rw [ENNReal.ofReal_add (mul_nonneg (varpi_nonneg _) (rawMass_nonneg _ _))
        (mul_nonneg (varpi_nonneg _) (rawMass_nonneg _ _)),
      ENNReal.ofReal_mul (varpi_nonneg _), ENNReal.ofReal_mul (varpi_nonneg _),
      ← greenFormula_tsum_rawMass n (s - 4), ← greenFormula_tsum_rawMass n (s - 5),
      ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun b => ?_
    rw [ENNReal.ofReal_add (mul_nonneg (varpi_nonneg _) (rawMass_nonneg _ _))
        (mul_nonneg (varpi_nonneg _) (rawMass_nonneg _ _)),
      ENNReal.ofReal_mul (varpi_nonneg _), ENNReal.ofReal_mul (varpi_nonneg _),
      sub_right_comm s b 4, sub_right_comm s b 5]
    ring

/-- `𝒢(n, s) = 𝒢ᶜˡ(n, s)` for `n ∈ ℕ`, in `ℝ≥0∞`. -/
private lemma greenFormula_G_natCast (n : ℕ) (s : ℤ) :
    greenFormulaG ((n : ℤ), s) = ENNReal.ofReal (greenClosed n s) := by
  cases n with
  | zero =>
    rw [greenFormula_G_eq_R, greenFormula_R_of_nonpos (by simp), add_zero, Nat.cast_zero,
      greenClosed_zero]
    by_cases hs : s = 0 <;> simp [hs, Prod.ext_iff]
  | succ n =>
    rw [greenFormula_G_eq_R, ite_eq_right (by simp [Prod.ext_iff]; omega), zero_add,
      Nat.cast_add_one, greenFormula_R_natCast_succ]

/-- **The Green's function in closed form.** For all `(j, s) ∈ ℤ × ℤ`,
`𝒢(j, s) = 𝒢ᶜˡ(j, s)`. -/
@[collatz_pos_dens "lem_rn_green_formula"]
theorem green_eq_greenClosed (j s : ℤ) : green j s = greenClosed j s := by
  rcases lt_or_ge j 0 with hj | hj
  · have h := greenFormula_G_eq_ofReal j s
    rw [greenFormula_G_of_neg hj, eq_comm, ENNReal.ofReal_eq_zero] at h
    rw [le_antisymm h (green_nonneg j s), greenClosed_of_neg hj]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    have h := greenFormula_G_eq_ofReal n s
    rw [greenFormula_G_natCast] at h
    exact ((ENNReal.ofReal_eq_ofReal_iff (greenClosed_nonneg _ _) (green_nonneg _ _)).1 h).symm

end CollatzPosDens
