/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChWhiteFactor
public import CollatzPosDens.CharSum.ChQRange
public import CollatzPosDens.CharSum.ChQRecursionLe
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnFpFirstStep
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.Renewal.RnFpSupport
public import CollatzPosDens.Renewal.RnHoldMass
public import CollatzPosDens.Renewal.RnHoldSupport

/-!
# The stopped inequality for the renewal function `Q`

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For every level `s ∈ ℕ` and every
point `p ∈ 𝒫`, the renewal function satisfies the stopped inequality
`Q(p) ≤ ∑_{x ∈ ℕ × ℤ} F_s(x) Q(p + x)`, where `F_s` is the first-passage law.

The proof is by strong induction on `s`, for all `p` at once. By the renewal inequality,
`Q(p) ≤ w(p) ∑_{h ∈ 𝒫} η(h) Q(p + h) ≤ ∑_{h ∈ 𝒫} η(h) Q(p + h)` since `w(p) ≤ 1` and
`Q ≥ 0`. Only `h` with `η(h) ≠ 0`, hence `l(h) ≥ 2 j(h) + 2 ≥ 1`, matter. The terms with
`l(h) > s` are kept; for the terms with `1 ≤ l(h) ≤ s` the induction hypothesis at level
`s - l(h)` and point `p + h` is applied, and the translation `x = h + y` recombines everything,
by the first-step decomposition of the first-passage law, into `∑_x F_s(x) Q(p + x)`.

## Main results

* `CollatzPosDens.chQ_le_tsum_firstPassageLaw_mul`:
  `Q(p) ≤ ∑_{x ∈ ℕ × ℤ} F_s(x) Q(p + x)`.

## Implementation notes

The inequality is first proved in `ℝ≥0∞`, for the images under `ENNReal.ofReal` and with the
sum over all of `ℤ × ℤ`, where nonnegative sums can be interchanged and translated without
summability side conditions. Since `F_s(r, ℓ) = 0` for `r ≤ 0`, the sum over `ℤ × ℤ` agrees
with the sum over `ℕ × ℤ`, and the latter real series converges because `0 ≤ Q ≤ 1` and `F_s`
has total mass `1`. The threshold `ε` is arbitrary.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.4.
-/

@[expose] public section

namespace CollatzPosDens

open ENNReal

open Classical in
/-- The first-step decomposition of `F_s(x)` in `ℝ≥0∞`, as an upper bound for the sums of
the images of its terms. -/
private lemma chQStopped_first_step_le (s : ℕ) (x : ℤ × ℤ) :
    (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h},
        ENNReal.ofReal (if x = h.1 then holdLaw h.1.1.toNat h.1.2 else 0)) +
      ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s},
        ENNReal.ofReal (holdLaw h.1.1.toNat h.1.2 * firstPassageLaw (s - bkL h) (x - h)) ≤
      ENNReal.ofReal (firstPassageLaw s x) := by
  rw [ofReal_firstPassageLaw_eq_first_step]
  refine add_le_add (le_of_eq ?_) (le_of_eq (tsum_congr fun h ↦ ENNReal.ofReal_mul
    (holdLaw_nonneg _ _)))
  by_cases hx : x ∈ bkPoints ∧ (s : ℤ) < bkL x
  · rw [tsum_eq_single ⟨x, hx⟩ fun h hne ↦ by
      simp [show x ≠ h.1 from fun e ↦ hne (Subtype.ext e.symm)]]
    simp [hx]
  · simp only [hx, ↓reduceIte]
    exact ENNReal.tsum_eq_zero.2 fun h ↦ by
      simp [show x ≠ h.1 by rintro rfl; exact hx h.2]

/-- The renewal bound `Q(p) ≤ ∑_{h ∈ 𝒫} η(h) Q(p + h)` in `ℝ≥0∞`. -/
private lemma chQStopped_ofReal_le_tsum (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ)
    {p : ℤ × ℤ} (hp : p ∈ bkPoints) :
    ENNReal.ofReal (chQ n ξ ε p) ≤
      ∑' h : bkPoints, ENNReal.ofReal (holdLaw h.1.1.toNat h.1.2) *
        ENNReal.ofReal (chQ n ξ ε (p + h)) := by
  have hnn : ∀ h : bkPoints, 0 ≤ holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε (p + h) := fun h ↦
    mul_nonneg (holdLaw_nonneg _ _) (chQ_nonneg _ _ _ _)
  have hQ : chQ n ξ ε p ≤ ∑' h : bkPoints, holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε (p + h) :=
    (chQ_le_mul_tsum n ξ ε hp).trans
      (mul_le_of_le_one_left (tsum_nonneg hnn) (chWhiteFactor_le_one n ξ ε p))
  refine ((ENNReal.ofReal_le_ofReal hQ).trans
    (ENNReal.ofReal_tsum_of_nonneg hnn (chQ_le_mul_tsum_summable n ξ ε p)).le).trans ?_
  exact le_of_eq (tsum_congr fun h ↦ ENNReal.ofReal_mul (holdLaw_nonneg _ _))

/-- The stopped inequality in `ℝ≥0∞`, with the sum over all of `ℤ × ℤ`. -/
private lemma chQStopped_ofReal_le (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (s : ℕ) :
    ∀ p ∈ bkPoints, ENNReal.ofReal (chQ n ξ ε p) ≤
      ∑' x : ℤ × ℤ, ENNReal.ofReal (firstPassageLaw s x) *
        ENNReal.ofReal (chQ n ξ ε (p + x)) := by
  classical
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro p hp
  have h1 := chQStopped_ofReal_le_tsum n ξ ε hp
  set Q := chQ n ξ ε
  set G : ℤ × ℤ → ℝ≥0∞ := fun h ↦ ENNReal.ofReal (holdLaw h.1.toNat h.2) *
    ENNReal.ofReal (Q (p + h)) with hG
  have h2 := (tsum_bkPoints_eq_add s (G := G) fun h hη ↦ by simp [hG, hη]).le
  have hA : ∀ h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h},
      G h = ∑' x : ℤ × ℤ,
        ENNReal.ofReal (if x = h.1 then holdLaw h.1.1.toNat h.1.2 else 0) *
          ENNReal.ofReal (Q (p + x)) := fun h ↦ by
    simp only [apply_ite ENNReal.ofReal, ENNReal.ofReal_zero, ite_mul, zero_mul, tsum_ite_eq, hG]
  have hB : ∀ h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s},
      G h ≤ ∑' x : ℤ × ℤ,
        ENNReal.ofReal (holdLaw h.1.1.toNat h.1.2 * firstPassageLaw (s - bkL h) (x - h)) *
          ENNReal.ofReal (Q (p + x)) := by
    rintro ⟨h, hP, hl1, hls⟩
    set m : ℕ := s - (bkL h).toNat with hm
    have hcast : (s : ℤ) - bkL h = (m : ℤ) := by omega
    have hms : m < s := by omega
    simp only [hcast, hG]
    refine (mul_le_mul_of_nonneg_left (ih m hms (p + h) (add_mem_bkPoints hp hP)) bot_le).trans
      (le_of_eq ?_)
    rw [← ENNReal.tsum_mul_left]
    refine ((Equiv.subRight h).tsum_eq _).symm.trans (tsum_congr fun x ↦ ?_)
    simp only [Equiv.subRight_apply, ENNReal.ofReal_mul (holdLaw_nonneg _ _), mul_assoc]
    congr 3
    abel_nf
  calc ENNReal.ofReal (Q p)
      ≤ (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h}, G h) +
        ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s}, G h := h1.trans h2
    _ ≤ (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h}, ∑' x : ℤ × ℤ,
          ENNReal.ofReal (if x = h.1 then holdLaw h.1.1.toNat h.1.2 else 0) *
            ENNReal.ofReal (Q (p + x))) +
        ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s}, ∑' x : ℤ × ℤ,
          ENNReal.ofReal (holdLaw h.1.1.toNat h.1.2 * firstPassageLaw (s - bkL h) (x - h)) *
            ENNReal.ofReal (Q (p + x)) :=
        add_le_add (le_of_eq (tsum_congr hA)) (ENNReal.tsum_le_tsum hB)
    _ = ∑' x : ℤ × ℤ,
          ((∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h},
            ENNReal.ofReal (if x = h.1 then holdLaw h.1.1.toNat h.1.2 else 0)) +
          ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s},
            ENNReal.ofReal (holdLaw h.1.1.toNat h.1.2 * firstPassageLaw (s - bkL h) (x - h))) *
          ENNReal.ofReal (Q (p + x)) := by
        rw [ENNReal.tsum_comm, ENNReal.tsum_comm (f := fun (h : {h : ℤ × ℤ // h ∈ bkPoints ∧
          1 ≤ bkL h ∧ bkL h ≤ s}) x ↦ _), ← ENNReal.tsum_add]
        refine tsum_congr fun x ↦ ?_
        rw [add_mul, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
    _ ≤ ∑' x : ℤ × ℤ, ENNReal.ofReal (firstPassageLaw s x) * ENNReal.ofReal (Q (p + x)) :=
        ENNReal.tsum_le_tsum fun x ↦ mul_le_mul_of_nonneg_right
          (chQStopped_first_step_le s x) bot_le

/-- **Stopped inequality at a first passage.** For every level `s ∈ ℕ` and every `p ∈ 𝒫`,
`Q(p) ≤ ∑_{x ∈ ℕ × ℤ} F_s(x) Q(p + x)`, where `F_s` is the first-passage law. -/
@[collatz_pos_dens "lem_ch_Q_stopped"]
theorem chQ_le_tsum_firstPassageLaw_mul (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (s : ℕ)
    {p : ℤ × ℤ} (hp : p ∈ bkPoints) :
    chQ n ξ ε p ≤
      ∑' x : ℕ × ℤ, firstPassageLaw s ((x.1 : ℤ), x.2) * chQ n ξ ε (p + ((x.1 : ℤ), x.2)) := by
  set ι : ℕ × ℤ → ℤ × ℤ := fun x ↦ ((x.1 : ℤ), x.2) with hι
  have hinj : Function.Injective ι := natCast_prod_injective
  have hnn : ∀ x : ℕ × ℤ, 0 ≤ firstPassageLaw s (ι x) * chQ n ξ ε (p + ι x) := fun x ↦
    mul_nonneg (firstPassageLaw_nonneg _ _) (chQ_nonneg _ _ _ _)
  have hsum : Summable fun x : ℕ × ℤ ↦ firstPassageLaw s (ι x) * chQ n ξ ε (p + ι x) :=
    Summable.of_nonneg_of_le hnn
      (fun x ↦ mul_le_of_le_one_right (firstPassageLaw_nonneg _ _) (chQ_le_one n ξ ε _))
      (summable_firstPassageLaw_natCast s)
  have hsupp : Function.support
      (fun x : ℤ × ℤ ↦ ENNReal.ofReal (firstPassageLaw s x) *
        ENNReal.ofReal (chQ n ξ ε (p + x))) ⊆ Set.range ι := by
    intro x hx
    have hF : firstPassageLaw s x ≠ 0 := fun h0 ↦ hx (by simp [h0])
    have h1 := (firstPassageLaw_support hF).1
    exact ⟨(x.1.toNat, x.2), by simp only [hι]; ext <;> simp; omega⟩
  rw [← ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hnn), ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  refine (chQStopped_ofReal_le n ξ ε s p hp).trans (le_of_eq ?_)
  rw [← hinj.tsum_eq hsupp]
  exact tsum_congr fun x ↦ (ENNReal.ofReal_mul (firstPassageLaw_nonneg _ _)).symm

end CollatzPosDens
