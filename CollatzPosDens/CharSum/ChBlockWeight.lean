/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The weight of a block

A block is a pair `β = (c, e)` of a word `c = (c₁, …, c_m)` of integers (its nonclosing letters)
and a closing letter `e ∈ {4, 5}`. Its weight is
`bw(β) = ϖ(e) ∏_{i=1}^m [cᵢ ∉ {4, 5}] ϖ(cᵢ)`,
where `ϖ` is the Pascal holding-time law. Thus a block has nonzero weight only if none of its
nonclosing letters is a closing letter `4` or `5`; the weights describe the paired letters as a
renewal sequence, cut after each closing letter.

## Main definitions

* `CollatzPosDens.chBlockWeight`: the block weight `bw : ℤ^{<ω} × ℤ → ℝ`.

## Main results

* `CollatzPosDens.chBlockWeight_nil`: `bw((), e) = ϖ(e)`.
* `CollatzPosDens.chBlockWeight_cons`: prepending a letter `a` multiplies the weight by
  `ϖ_in(a) = [a ∉ {4, 5}] ϖ(a)`.
* `CollatzPosDens.chBlockWeight_ofFn`: `bw((v₁, …, v_m), e) = ϖ(e) ∏ᵢ ϖ_in(vᵢ)`.
* `CollatzPosDens.chBlockWeight_append`: the weight of `(c ++ d, e)` factors through `(d, e)`.
* `CollatzPosDens.chBlockWeight_nonneg`: every block weight is nonnegative.
* `CollatzPosDens.chBlockWeight_eq_zero_of_mem`: a nonclosing letter in `{4, 5}` kills the
  weight.

## Implementation notes

Words in `ℤ^{<ω}` are modelled as `List ℤ`, so the length `m` is `c.length`, and a block as a
pair `List ℤ × ℤ`. The closing letter is allowed to be an arbitrary integer: the formula makes
sense for every `e`, and the set of blocks `𝔅 = ℤ^{<ω} × {4, 5}` is recovered by restricting to
`β.2 ∈ {4, 5}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The block weight `bw(β) = ϖ(e) ∏_{i=1}^m [cᵢ ∉ {4, 5}] ϖ(cᵢ)` of a block
`β = (c, e)` with `c = (c₁, …, c_m)`, written with `ϖ_in(a) = [a ∉ {4, 5}] ϖ(a)`. -/
@[collatz_pos_dens "def_ch_block_weight"]
noncomputable def chBlockWeight (β : List ℤ × ℤ) : ℝ :=
  varpi β.2 * (β.1.map varpiIn).prod

/-- Unfolding `bw` on a pair `(c, e)`. -/
lemma chBlockWeight_mk (c : List ℤ) (e : ℤ) :
    chBlockWeight (c, e) = varpi e * (c.map varpiIn).prod :=
  rfl

/-- A block with no nonclosing letters has weight `ϖ(e)`. -/
@[simp]
lemma chBlockWeight_nil (e : ℤ) : chBlockWeight ([], e) = varpi e := by
  simp [chBlockWeight]

/-- Prepending a nonclosing letter `a` multiplies the block weight by `ϖ_in(a)`. -/
lemma chBlockWeight_cons (a : ℤ) (c : List ℤ) (e : ℤ) :
    chBlockWeight (a :: c, e) = varpiIn a * chBlockWeight (c, e) := by
  simp only [chBlockWeight, List.map_cons, List.prod_cons]
  ring

/-- Prepending a word `c` multiplies the block weight by `∏ ϖ_in(cᵢ)`. -/
lemma chBlockWeight_append (c d : List ℤ) (e : ℤ) :
    chBlockWeight (c ++ d, e) = (c.map varpiIn).prod * chBlockWeight (d, e) := by
  simp only [chBlockWeight, List.map_append, List.prod_append]
  ring

/-- Every block weight is nonnegative. -/
lemma chBlockWeight_nonneg (β : List ℤ × ℤ) : 0 ≤ chBlockWeight β :=
  mul_nonneg (varpi_nonneg _) <| List.prod_nonneg fun x hx ↦ by
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    exact varpiIn_nonneg b

/-- A block one of whose nonclosing letters is `4` or `5` has weight zero. -/
lemma chBlockWeight_eq_zero_of_mem {β : List ℤ × ℤ} {a : ℤ} (ha : a ∈ β.1)
    (h45 : a ∈ ({4, 5} : Set ℤ)) : chBlockWeight β = 0 := by
  refine mul_eq_zero_of_right _ (List.prod_eq_zero ?_)
  exact List.mem_map.mpr ⟨a, ha, varpiIn_of_mem h45⟩

/-- On words avoiding `{4, 5}`, the block weight is `ϖ(e) ∏ ϖ(cᵢ)`. -/
lemma chBlockWeight_of_forall_notMem {c : List ℤ} (e : ℤ)
    (hc : ∀ a ∈ c, a ∉ ({4, 5} : Set ℤ)) :
    chBlockWeight (c, e) = varpi e * (c.map varpi).prod := by
  rw [chBlockWeight_mk, List.map_congr_left (g := varpi) fun a ha ↦ varpiIn_of_notMem (hc a ha)]

/-- The block weight of a word given as a tuple: `bw((v₁, …, v_m), e) = ϖ(e) ∏ᵢ ϖ_in(vᵢ)`. -/
lemma chBlockWeight_ofFn {m : ℕ} (v : Fin m → ℤ) (e : ℤ) :
    chBlockWeight (List.ofFn v, e) = varpi e * ∏ i, varpiIn (v i) := by
  rw [chBlockWeight_mk, List.map_ofFn, List.prod_ofFn]
  rfl

/-- Every nonclosing letter of a block of nonzero weight is at least `2`. -/
theorem two_le_of_chBlockWeight_ne_zero {β : List ℤ × ℤ} (hβ : chBlockWeight β ≠ 0)
    {a : ℤ} (ha : a ∈ β.1) : 2 ≤ a := by
  by_contra h
  apply hβ
  exact mul_eq_zero_of_right _
    (List.prod_eq_zero (List.mem_map.mpr ⟨a, ha, varpiIn_of_le_one (by omega)⟩))

/-- The closing letter of a block of nonzero weight is at least `2`. -/
theorem two_le_snd_of_chBlockWeight_ne_zero {β : List ℤ × ℤ} (hβ : chBlockWeight β ≠ 0) :
    2 ≤ β.2 :=
  two_le_of_varpi_ne_zero fun h0 ↦ hβ (by simp [chBlockWeight, h0])

/-- Every letter, closing letter included, of a block of nonzero weight is at least `2`. -/
theorem two_le_of_mem_append_of_chBlockWeight_ne_zero {β : List ℤ × ℤ}
    (hβ : chBlockWeight β ≠ 0) {x : ℤ} (hx : x ∈ β.1 ++ [β.2]) : 2 ≤ x := by
  rcases List.mem_append.mp hx with hx | hx
  · exact two_le_of_chBlockWeight_ne_zero hβ hx
  · rw [List.mem_singleton.mp hx]
    exact two_le_snd_of_chBlockWeight_ne_zero hβ

/-- The nonclosing word `c` of a block `β = (c, e)` of nonzero weight has `2|c| ≤ ∑ c`. -/
theorem two_mul_length_le_sum_of_chBlockWeight_ne_zero {β : List ℤ × ℤ}
    (hβ : chBlockWeight β ≠ 0) : 2 * (β.1.length : ℤ) ≤ β.1.sum := by
  have key : ∀ c : List ℤ, (∀ a ∈ c, 2 ≤ a) → 2 * (c.length : ℤ) ≤ c.sum := by
    intro c hc
    induction c with
    | nil => simp
    | cons a t ih =>
      simp only [List.length_cons, List.sum_cons, List.mem_cons] at hc ⊢
      have := hc a (Or.inl rfl)
      have := ih fun b hb ↦ hc b (Or.inr hb)
      push_cast
      omega
  exact key β.1 fun a ha ↦ two_le_of_chBlockWeight_ne_zero hβ ha

end CollatzPosDens
