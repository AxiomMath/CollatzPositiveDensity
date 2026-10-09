/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.CharSum.ChRaw
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.Renewal.RnPascal

/-!
# The law of the raw prefix of a list of blocks

Let `𝔅 = ℤ^{<ω} × {4, 5}` be the set of blocks, weighted by the block weight `bw`. Weigh a list
`β = (β¹, …, βᴺ) ∈ 𝔅^N` by `∏ₖ bw(βᵏ)`. For `J' ≤ N` and `b ∈ ℤ^{J'}`, the total weight of the
lists whose raw prefix `raw_{J'}(β¹, …, βᴺ)` equals `b` is `∏ᵢ ϖ(bᵢ)`: under the block weights,
the paired letters are independent with law `ϖ`.

The proof is by induction on `J'`, for all `N ≥ J'` at once. For `J' = 0` this is the statement
that lists of blocks have total weight one. For the inductive step one splits on whether the
first block is `(∅, e)` (then the first letter is the closing letter `e`, and
`bw(∅, e) = ϖ(e)`) or `((a)c', e)` (then the first letter is `a`, and
`bw((a)c', e) = [a ∉ {4, 5}] ϖ(a) bw(c', e)`). The two prefactors `[b₀ ∈ {4, 5}] ϖ(b₀)` and
`[b₀ ∉ {4, 5}] ϖ(b₀)` add up to `ϖ(b₀)`.

## Main results

* `CollatzPosDens.hasSum_prod_chBlockWeight_chRaw_eq`: the law of the raw prefix,
  `∑_{β ∈ 𝔅^N} ∏ₖ bw(βᵏ) [raw_{J'}(β) = b] = ∏ᵢ ϖ(bᵢ)`, as a `HasSum`.

## Implementation notes

As in `CollatzPosDens.hasSum_prod_chBlockWeight`, `𝔅` is the subtype of pairs
`List ℤ × ℤ` whose closing letter lies in `{4, 5}`, a list of `N` blocks is a function
`Fin N → 𝔅` (turned into the list expected by `chRaw` with `List.ofFn`), and `b ∈ ℤ^{J'}` is a
function `Fin J' → ℤ`. The series of nonnegative terms is stated with `HasSum`, which records
both its convergence and its value.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- A block is either `(∅, e)` with `e ∈ {4, 5}`, or `((a)c', e)`, which corresponds to the pair
`(a, (c', e))`. -/
private def chRawLawBlockEquiv :
    {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)} ≃
      {e : ℤ // e ∈ ({4, 5} : Set ℤ)} ⊕ (ℤ × {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}) where
  toFun
    | ⟨([], e), he⟩ => .inl ⟨e, he⟩
    | ⟨(a :: c, e), he⟩ => .inr (a, ⟨(c, e), he⟩)
  invFun
    | .inl ⟨e, he⟩ => ⟨([], e), he⟩
    | .inr (a, ⟨(c, e), he⟩) => ⟨(a :: c, e), he⟩
  left_inv := by rintro ⟨⟨_ | ⟨a, c⟩, e⟩, he⟩ <;> rfl
  right_inv := by rintro (⟨e, he⟩ | ⟨a, ⟨⟨c, e⟩, he⟩⟩) <;> rfl

/-- The term `∏ₖ bw(βᵏ) [raw_J(β) = b]` of the series, for a list of `K` blocks. -/
private noncomputable def chRawLawTerm (J : ℕ) (b : Fin J → ℤ) {K : ℕ}
    (β : Fin K → {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}) : ℝ :=
  (∏ k, chBlockWeight (β k)) *
    if chRaw J (List.ofFn fun k ↦ (β k).1) = List.ofFn b then 1 else 0

/-- **Law of the raw prefix.** For `J' ≤ N` and `b ∈ ℤ^{J'}`, the series of nonnegative terms
`∑_{β ∈ 𝔅^N} ∏ₖ bw(βᵏ) [raw_{J'}(β¹, …, βᴺ) = b]` converges, with sum `∏ᵢ ϖ(bᵢ)`. -/
@[collatz_pos_dens "lem_ch_raw_law"]
theorem hasSum_prod_chBlockWeight_chRaw_eq {J N : ℕ} (hJN : J ≤ N) (b : Fin J → ℤ) :
    HasSum (fun β : Fin N → {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)} ↦
        (∏ k, chBlockWeight (β k)) *
          if chRaw J (List.ofFn fun k ↦ (β k).1) = List.ofFn b then 1 else 0)
      (∏ i, varpi (b i)) := by
  induction J generalizing N with
  | zero => simpa using hasSum_prod_chBlockWeight N
  | succ J ih =>
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    set B := {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}
    set S := {e : ℤ // e ∈ ({4, 5} : Set ℤ)}
    set b' : Fin J → ℤ := fun i ↦ b i.succ
    set P : ℝ := ∏ i, varpi (b' i)
    have hG0 : ∀ {K : ℕ} (β : Fin K → B), 0 ≤ chRawLawTerm J b' β := fun β ↦
      mul_nonneg (prod_chBlockWeight_nonneg β) (by split_ifs <;> norm_num)
    -- the first letter, when the first block is `(∅, e)`
    set f₁ : S → ℝ := fun e ↦ varpi e * if (e : ℤ) = b 0 then 1 else 0
    set c₁ : ℝ := varpiLast (b 0)
    have hf₁0 : ∀ e, 0 ≤ f₁ e := fun e ↦
      mul_nonneg (varpi_nonneg _) (by split_ifs <;> norm_num)
    have hf₁ : HasSum f₁ c₁ := by
      by_cases hb : b 0 ∈ ({4, 5} : Set ℤ)
      · convert hasSum_single (f := f₁) ⟨b 0, hb⟩ fun e he ↦ ?_ using 1
        · simp [f₁, c₁, hb, varpiLast]
        · have : (e : ℤ) ≠ b 0 := fun h ↦ he (Subtype.ext h)
          simp [f₁, this]
      · convert hasSum_zero (α := ℝ) (β := S) using 1
        · funext ⟨e, he⟩
          have : e ≠ b 0 := by rintro rfl; exact hb he
          simp [f₁, this]
        · simp [c₁, hb, varpiLast]
    -- the first letter, when the first block is `((a)c', e)`
    set f₂ : ℤ → ℝ := fun a ↦ varpiIn a * if a = b 0 then 1 else 0
    set c₂ : ℝ := varpiIn (b 0)
    have hf₂0 : ∀ a, 0 ≤ f₂ a := fun a ↦ mul_nonneg (varpiIn_nonneg a) (by split_ifs <;> norm_num)
    have hf₂ : HasSum f₂ c₂ := by
      convert hasSum_single (f := f₂) (b 0) fun a ha ↦ ?_ using 1
      · simp only [f₂, c₂, ↓reduceIte, mul_one]
      · simp only [f₂, ha, ↓reduceIte, mul_zero]
    -- the remaining blocks
    have hM : HasSum (fun r : Fin M → B ↦ chRawLawTerm J b' r) P := by
      have := ih (N := M) (by omega) b'
      exact this
    have hM1 : HasSum (fun x : B × (Fin M → B) ↦
        chRawLawTerm J b' (Fin.consEquiv (fun _ ↦ B) x)) P :=
      (Fin.consEquiv (fun _ : Fin (M + 1) ↦ B)).hasSum_iff
        (f := fun β ↦ chRawLawTerm J b' β) |>.mpr (ih (N := M + 1) (by omega) b')
    have h1 : HasSum (fun x : S × (Fin M → B) ↦ f₁ x.1 * chRawLawTerm J b' x.2) (c₁ * P) :=
      hf₁.mul hM (Summable.mul_of_nonneg hf₁.summable hM.summable hf₁0 fun r ↦ hG0 r)
    have h2' : HasSum (fun x : ℤ × (B × (Fin M → B)) ↦
        f₂ x.1 * chRawLawTerm J b' (Fin.consEquiv (fun _ ↦ B) x.2)) (c₂ * P) :=
      hf₂.mul hM1 (Summable.mul_of_nonneg (f := f₂)
        (g := fun x : B × (Fin M → B) ↦ chRawLawTerm J b' (Fin.consEquiv (fun _ ↦ B) x))
        hf₂.summable hM1.summable hf₂0 fun r ↦ hG0 _)
    have h2 : HasSum (fun x : (ℤ × B) × (Fin M → B) ↦
        f₂ x.1.1 * chRawLawTerm J b' (Fin.consEquiv (fun _ ↦ B) (x.1.2, x.2))) (c₂ * P) :=
      (Equiv.prodAssoc ℤ B (Fin M → B)).hasSum_iff (f := fun x : ℤ × (B × (Fin M → B)) ↦
        f₂ x.1 * chRawLawTerm J b' (Fin.consEquiv (fun _ ↦ B) x.2)) |>.mpr h2'
    set e : (S × (Fin M → B)) ⊕ ((ℤ × B) × (Fin M → B)) ≃ (Fin (M + 1) → B) :=
      (Equiv.sumProdDistrib _ _ _).symm.trans
        ((Equiv.prodCongr chRawLawBlockEquiv.symm (Equiv.refl _)).trans
          (Fin.consEquiv fun _ ↦ B))
    have htot : ∏ i, varpi (b i) = c₁ * P + c₂ * P := by
      rw [Fin.prod_univ_succ, ← add_mul]
      by_cases hb : b 0 ∈ ({4, 5} : Set ℤ) <;> simp [c₁, c₂, hb, P, b', varpiIn, varpiLast]
    rw [htot, ← e.hasSum_iff]
    refine HasSum.sum ?_ ?_
    · convert h1 using 1
      funext ⟨⟨e', he'⟩, r⟩
      simp only [e, Function.comp_apply, Equiv.trans_apply, Equiv.sumProdDistrib_symm_apply_left,
        Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, f₁, chRawLawTerm]
      simp [chRawLawBlockEquiv, Fin.consEquiv, Fin.prod_univ_succ, List.ofFn_succ, b']
      by_cases h : e' = b 0
      · subst h; simp
      · simp [h]
    · convert h2 using 1
      funext ⟨⟨a, ⟨⟨c', e'⟩, he'⟩⟩, r⟩
      simp only [e, Function.comp_apply, Equiv.trans_apply,
        Equiv.sumProdDistrib_symm_apply_right, Equiv.prodCongr_apply, Prod.map,
        Equiv.refl_apply, f₂, chRawLawTerm]
      simp [chRawLawBlockEquiv, Fin.consEquiv, Fin.prod_univ_succ, List.ofFn_succ, b',
        chBlockWeight_cons]
      by_cases h : a = b 0
      · subst h; simp [mul_assoc]
      · simp [h]

end CollatzPosDens
