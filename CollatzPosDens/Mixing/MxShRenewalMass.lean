/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShPartialSums
public import CollatzPosDens.Transfer.GeometricTotal

/-!
# Renewal mass of a prescribed trace of partial sums

Under the geometric mass `𝐩`, the letters of a word of length `q` behave like independent
geometric variables of parameter `1/2`, so the set `Pt(w)` of partial sums of `w` is a renewal
process on `ℤ_{≥1}` in which every integer is hit independently with probability `1/2`. In
particular every trace `β ⊆ {1, …, q}` on the first `q` integers is equally likely:
$$\mathbf p\bigl(\{w \in \mathbb Z_{\ge 1}^q : \mathrm{Pt}(w) \cap \{1, \dots, q\} = \beta\}\bigr)
  = 2^{-q}.$$

More generally, for words of length `t` and a window `{1, …, N}` with `N ≤ t`, every trace
`β ⊆ {1, …, N}` has mass `2^{-N}`. This is proved by induction on `t`, splitting off the first
letter `a`: if `a > N` the trace is empty, which accounts for the mass `∑_{a > N} 2^{-a} = 2^{-N}`
of the empty trace; if `a ≤ N` the trace is `{a} ∪ (a + β')` where `β'` is the trace of the
remaining word on `{1, …, N - a}`, so a nonempty trace `β` forces `a = min β` and the induction
hypothesis gives the mass `2^{-a} · 2^{-(N - a)} = 2^{-N}`.

## Main results

* `CollatzPosDens.geomMass_partialSums_inter_Icc_eq_of_le`: for `N ≤ t` and `β ⊆ {1, …, N}`,
  `𝐩({w ∈ ℤ_{≥1}^t : Pt(w) ∩ {1, …, N} = β}) = 2^{-N}`.
* `CollatzPosDens.geomMass_partialSums_inter_Icc_eq`: the renewal mass identity
  `𝐩({w ∈ ℤ_{≥1}^q : Pt(w) ∩ {1, …, q} = β}) = 2^{-q}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal
open Finset

namespace CollatzPosDens

/-- `∑_{a > N} 2^{-a} = 2^{-N}`, the sum running over positive integers `a`. -/
theorem tsum_pnat_ite_lt_two_inv_pow (N : ℕ) :
    ∑' a : ℕ+, (if N < (a : ℕ) then (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) else 0) = 2⁻¹ ^ N := by
  rw [tsum_pnat_eq_tsum_succ (f := fun n => if N < n then (2⁻¹ : ℝ≥0∞) ^ n else 0),
    ← (Summable.sum_add_tsum_nat_add' (k := N) ENNReal.summable)]
  have h1 : ∑ i ∈ range N, (if N < i + 1 then (2⁻¹ : ℝ≥0∞) ^ (i + 1) else 0) = 0 :=
    sum_eq_zero fun i hi => ite_eq_right_iff.2 fun h => absurd h (by simp at hi; omega)
  have h2 : ∀ i : ℕ, (if N < i + N + 1 then (2⁻¹ : ℝ≥0∞) ^ (i + N + 1) else 0) =
      2⁻¹ ^ (N + 1) * 2⁻¹ ^ i := fun i => by
    simp only [show N < i + N + 1 by omega, ↓reduceIte]
    rw [← pow_add]
    congr 1
    omega
  simp only [h1, h2]
  rw [zero_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    pow_succ, mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]

namespace Word

/-- If the first letter `a` exceeds `N`, the word has no partial sum in `{1, …, N}`. -/
theorem partialSums_cons_inter_Icc_of_lt {N : ℕ} {a : ℕ+} (h : N < a) (y : Word) :
    partialSums (a :: y) ∩ Icc 1 N = ∅ := by
  ext s
  simp only [partialSums_cons, mem_inter, mem_insert, mem_map, addLeftEmbedding_apply, mem_Icc,
    notMem_empty, iff_false, not_and]
  rintro (rfl | ⟨x, -, rfl⟩) <;> omega

/-- If the first letter `a` is at most `N`, the partial sums of `a y` in `{1, …, N}` are `a` and
the shifts by `a` of the partial sums of `y` in `{1, …, N - a}`. -/
theorem partialSums_cons_inter_Icc_of_le {N : ℕ} {a : ℕ+} (h : (a : ℕ) ≤ N) (y : Word) :
    partialSums (a :: y) ∩ Icc 1 N =
      insert (a : ℕ) ((partialSums y ∩ Icc 1 (N - a)).map (addLeftEmbedding (a : ℕ))) := by
  ext s
  simp only [partialSums_cons, mem_inter, mem_insert, mem_map, addLeftEmbedding_apply, mem_Icc]
  have ha := a.pos
  constructor
  · rintro ⟨rfl | ⟨x, hx, rfl⟩, -, hs⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨x, ⟨hx, pos_of_mem_partialSums hx, by omega⟩, rfl⟩
  · rintro (rfl | ⟨x, ⟨hx, hx1, hxN⟩, rfl⟩)
    · exact ⟨Or.inl rfl, by omega, h⟩
    · exact ⟨Or.inr ⟨x, hx, rfl⟩, by omega, by omega⟩

end Word

/-- For a nonempty `β ⊆ {1, …, N}` with least element `m`, the shifted trace
`γ = {s - m : s ∈ β, s ≠ m}` satisfies `γ ⊆ {1, …, N - m}` and `β = {m} ∪ (m + γ)`. -/
private theorem exists_insert_map_eq {N : ℕ} {β : Finset ℕ} (hβ : β ⊆ Icc 1 N) (hne : β.Nonempty) :
    ∃ γ ⊆ Icc 1 (N - β.min' hne),
      insert (β.min' hne) (γ.map (addLeftEmbedding (β.min' hne))) = β := by
  set m := β.min' hne
  have hmβ : m ∈ β := min'_mem β hne
  have hmin : ∀ s ∈ β, m ≤ s := fun s hs => min'_le β s hs
  refine ⟨(β.erase m).image (· - m), ?_, ?_⟩
  · intro x hx
    simp only [mem_image, mem_erase] at hx
    obtain ⟨s, ⟨hsm, hs⟩, rfl⟩ := hx
    have := hmin s hs
    have := mem_Icc.1 (hβ hs)
    simp only [mem_Icc]
    omega
  · ext s
    simp only [mem_insert, mem_map, mem_image, mem_erase, addLeftEmbedding_apply]
    constructor
    · rintro (rfl | ⟨x, ⟨u, ⟨-, hu⟩, rfl⟩, rfl⟩)
      · exact hmβ
      · rwa [Nat.add_sub_cancel' (hmin u hu)]
    · intro hs
      by_cases hsm : s = m
      · exact Or.inl hsm
      · exact Or.inr ⟨s - m, ⟨s, ⟨hsm, hs⟩, rfl⟩, Nat.add_sub_cancel' (hmin s hs)⟩

/-- `m ∉ m + γ` when `γ` consists of positive integers. -/
private theorem notMem_map_addLeft {m M : ℕ} {γ : Finset ℕ} (hγ : γ ⊆ Icc 1 M) :
    m ∉ γ.map (addLeftEmbedding m) := by
  simp only [mem_map, addLeftEmbedding_apply, not_exists, not_and]
  intro x hx
  have := (mem_Icc.1 (hγ hx)).1
  omega

/-- **Renewal mass, general window.** For words of length `t`, a window `{1, …, N}` with
`N ≤ t` and any `β ⊆ {1, …, N}`, the words whose partial sums meet `{1, …, N}` exactly in `β`
have geometric mass `2^{-N}`. -/
theorem geomMass_partialSums_inter_Icc_eq_of_le {t N : ℕ} (hN : N ≤ t) {β : Finset ℕ}
    (hβ : β ⊆ Icc 1 N) :
    geomMass {w : Word | w.length = t ∧ w.partialSums ∩ Icc 1 N = β} = 2⁻¹ ^ N := by
  induction t generalizing N β with
  | zero =>
    obtain rfl : N = 0 := by omega
    obtain rfl : β = ∅ := subset_empty.1 (by simpa using hβ)
    have : {w : Word | w.length = 0 ∧ w.partialSums ∩ Icc 1 0 = ∅} = {w | w.length = 0} := by
      ext w; simp
    rw [this, geomMass_setOf_length_eq, pow_zero]
  | succ t ih =>
    rw [geomMass_setOf_length_succ_and t (fun x => x.partialSums ∩ Icc 1 N = β)]
    rcases β.eq_empty_or_nonempty with rfl | hne
    · rw [← tsum_pnat_ite_lt_two_inv_pow N]
      refine tsum_congr fun a => ?_
      split_ifs with ha
      · have : {y : Word | y.length = t ∧ Word.partialSums (a :: y) ∩ Icc 1 N = (∅ : Finset ℕ)} =
            {y | y.length = t} := by
          ext y; simp [Word.partialSums_cons_inter_Icc_of_lt ha]
        rw [this, geomMass_setOf_length_eq, mul_one]
      · have : {y : Word | y.length = t ∧ Word.partialSums (a :: y) ∩ Icc 1 N = (∅ : Finset ℕ)} =
            ∅ := by
          ext y; simp [Word.partialSums_cons_inter_Icc_of_le (not_lt.1 ha)]
        rw [this, geomMass_empty, mul_zero]
    · obtain ⟨γ, hγ, hγβ⟩ := exists_insert_map_eq hβ hne
      set m := β.min' hne with hm_def
      have hmβ : m ∈ β := min'_mem β hne
      have hm1 : 1 ≤ m := (mem_Icc.1 (hβ hmβ)).1
      have hmN : m ≤ N := (mem_Icc.1 (hβ hmβ)).2
      rw [tsum_eq_single (β := ℕ+) ⟨m, hm1⟩]
      · have : {y : Word | y.length = t ∧
            Word.partialSums ((⟨m, hm1⟩ : ℕ+) :: y) ∩ Icc 1 N = β} =
            {y | y.length = t ∧ y.partialSums ∩ Icc 1 (N - m) = γ} := by
          ext y
          simp only [Set.mem_ofPred_eq, Word.partialSums_cons_inter_Icc_of_le
            (a := ⟨m, hm1⟩) hmN, PNat.mk_coe]
          rw [← hγβ]
          refine and_congr_right fun _ => ⟨fun h => ?_, fun h => by rw [h]⟩
          have h' := congrArg (fun s => s.erase m) h
          rwa [erase_insert (notMem_map_addLeft inter_subset_right),
            erase_insert (notMem_map_addLeft hγ), map_inj] at h'
        rw [this, ih (by omega) hγ, PNat.mk_coe, ← pow_add, Nat.add_sub_cancel' hmN]
      · intro a ha
        have : {y : Word | y.length = t ∧ Word.partialSums (a :: y) ∩ Icc 1 N = β} = ∅ := by
          ext y
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro _
          rcases lt_or_ge N (a : ℕ) with h | h
          · rw [Word.partialSums_cons_inter_Icc_of_lt h]
            exact hne.ne_empty.symm
          · rw [Word.partialSums_cons_inter_Icc_of_le h]
            intro hβ'
            apply ha
            have haβ : (a : ℕ) ∈ β := hβ' ▸ mem_insert_self _ _
            have hle : (a : ℕ) ≤ m := by
              rw [← hβ'] at hmβ
              rcases mem_insert.1 hmβ with h' | h'
              · exact h'.ge
              · obtain ⟨x, -, hx⟩ := mem_map.1 h'
                simp only [addLeftEmbedding_apply] at hx
                omega
            exact PNat.coe_inj.1 (le_antisymm hle (min'_le β _ haβ))
        rw [this, geomMass_empty, mul_zero]

/-- **Renewal mass.** For `q ∈ ℕ` and `β ⊆ {1, …, q}`, the words `w ∈ ℤ_{≥1}^q` whose partial
sums meet `{1, …, q}` exactly in `β` have geometric mass
`𝐩({w ∈ ℤ_{≥1}^q : Pt(w) ∩ {1, …, q} = β}) = 2^{-q}`. -/
@[collatz_pos_dens "lem_mx_sh_renewal_mass"]
theorem geomMass_partialSums_inter_Icc_eq (q : ℕ) {β : Finset ℕ} (hβ : β ⊆ Icc 1 q) :
    geomMass {w : Word | w.length = q ∧ w.partialSums ∩ Icc 1 q = β} = 2⁻¹ ^ q :=
  geomMass_partialSums_inter_Icc_eq_of_le le_rfl hβ

end CollatzPosDens
