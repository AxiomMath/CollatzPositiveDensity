/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3CapRange
public import CollatzPosDens.Case3.C3H17Cost
public import CollatzPosDens.Case3.C3H17Weight
public import CollatzPosDens.Case3.C3SuffixWords
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldFinite
public import CollatzPosDens.Renewal.RnHoldMass
public import CollatzPosDens.Renewal.RnPascalTotal
public import Mathlib.Algebra.Order.Group.Indicator

/-!
# The future cost sums the retained factors

Let `𝒮₂` be the set of hold words (`CollatzPosDens.c3SuffixWords 2`): the nonempty finite words
of letters at least `2` whose last letter, and no other, lies in `{4, 5}`. For every integer `h`
and real `z`,
`∑_{u ∈ 𝒮₂} (∏_i ϖ(u_i)) · wt_h(z; u) = cf_h(z)`,
where `ϖ` is the Pascal weight, `wt_h(z; u)` the product of the capped packet factors retained
along `u` and `cf_h(z)` the height-seventeen future cost.

The proof is by downward induction on `h`. The words of `𝒮₂` carry total Pascal mass `1`, the
total mass of the holding-time law, which settles `h ≥ 15`. For `h < 15`, a word of `𝒮₂` is
`d :: u⁻` with `d ≥ 2`, where `u⁻ = ()` if `d ∈ {4, 5}` and `u⁻ ∈ 𝒮₂` otherwise; summing first
over `u⁻` with the induction hypothesis at height `h + d` and then over `d` with
`∑_d ϖ(d) = 1` gives the recursion defining `cf_h(z)`.

## Main results

* `CollatzPosDens.cons_mem_c3SuffixWords_two`: `d :: u ∈ 𝒮₂` iff `d ≥ 2` and either
  `d ∈ {4, 5}` and `u = ()`, or `d ∉ {4, 5}` and `u ∈ 𝒮₂`.
* `CollatzPosDens.hasSum_prod_varpi_c3SuffixWords_two`: `∑_{u ∈ 𝒮₂} ∏_i ϖ(u_i) = 1`.
* `CollatzPosDens.hasSum_c3H17Weight`: the series `∑_{u ∈ 𝒮₂} (∏_i ϖ(u_i)) wt_h(z; u)`
  converges unconditionally to `cf_h(z)`.
* `CollatzPosDens.tsum_c3H17Weight`: its sum is `cf_h(z)`.

## Implementation notes

The sum over the infinite set `𝒮₂` is an unconditional sum (`HasSum`) of nonnegative terms over
the subtype of `𝒮₂ : Set (List ℤ)`, and `∏_i ϖ(u_i)` is `(u.map ϖ).prod`. The paper states
the identity for `h ≥ 1`; it holds, with the same proof, for every integer `h`, which is the
form proved here.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A word lies in `𝒮₂` iff it is nonempty, its letters are at least `2`, and a letter lies in
`{4, 5}` exactly when it is the last one. -/
private theorem mem_c3SuffixWords_two_iff {u : List ℤ} :
    u ∈ c3SuffixWords 2 ↔ u ≠ [] ∧ ∀ i : Fin u.length,
      2 ≤ u.get i ∧ (u.get i ∈ ({4, 5} : Set ℤ) ↔ (i : ℕ) + 1 = u.length) := by
  rw [mem_c3SuffixWords_of_notMem (by norm_num)]
  simp only [mem_holdWords_iff, exists_and_left, exists_eq', and_true, forall_and]
  rw [Nat.one_le_iff_ne_zero, Ne, List.length_eq_zero_iff]

/-- A word `d :: u` lies in `𝒮₂` iff `d ≥ 2` and either `d ∈ {4, 5}` and `u` is empty, or
`d ∉ {4, 5}` and `u ∈ 𝒮₂`. -/
theorem cons_mem_c3SuffixWords_two {d : ℤ} {u : List ℤ} :
    d :: u ∈ c3SuffixWords 2 ↔
      2 ≤ d ∧ (d ∈ ({4, 5} : Set ℤ) → u = []) ∧ (d ∉ ({4, 5} : Set ℤ) → u ∈ c3SuffixWords 2) := by
  rw [mem_c3SuffixWords_two_iff, mem_c3SuffixWords_two_iff]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and, List.length_cons]
  rw [Fin.forall_fin_succ]
  simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, zero_add,
    Fin.val_succ, List.getElem_cons_succ, add_left_inj]
  have hl : 1 = u.length + 1 ↔ u = [] := by
    rw [eq_comm, add_eq_right, List.length_eq_zero_iff]
  rw [hl]
  by_cases hd : d ∈ ({4, 5} : Set ℤ)
  · constructor
    · rintro ⟨⟨h2, h⟩, -⟩
      exact ⟨h2, fun _ => h.1 hd, fun h' => (h' hd).elim⟩
    · rintro ⟨h2, h0, -⟩
      obtain rfl := h0 hd
      exact ⟨⟨h2, iff_of_true hd rfl⟩, fun i => i.elim0⟩
  · simp only [hd, false_iff, not_false_eq_true, forall_const, false_imp_iff, true_and,
      and_assoc]

/-- **Mass of the hold words.** The words of `𝒮₂` carry total Pascal mass `1`:
`∑_{u ∈ 𝒮₂} ∏_i ϖ(u_i) = 1`. -/
theorem hasSum_prod_varpi_c3SuffixWords_two :
    HasSum (fun u : c3SuffixWords 2 => (u.1.map varpi).prod) 1 := by
  have hS : c3SuffixWords 2 = ⋃ j : ℕ, ⋃ (_ : 1 ≤ j), ⋃ l : ℤ, List.ofFn '' holdWords j l :=
    c3SuffixWords_of_notMem (by norm_num)
  let g : (Σ x : ℕ × ℤ, holdWords (x.1 + 1) x.2) → c3SuffixWords 2 := fun p =>
    ⟨List.ofFn p.2.1, by
      rw [hS]
      exact Set.mem_iUnion₂.2 ⟨p.1.1 + 1, by omega,
        Set.mem_iUnion.2 ⟨p.1.2, ⟨p.2.1, p.2.2, rfl⟩⟩⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨⟨m, l⟩, w, hw⟩ ⟨⟨m', l'⟩, w', hw'⟩ h
      have h' : List.ofFn w = List.ofFn w' := congrArg Subtype.val h
      have hm : m = m' := by simpa using congrArg List.length h'
      subst hm
      obtain rfl : w = w' := List.ofFn_injective h'
      obtain rfl : l = l' := (holdWords_sum_eq hw).symm.trans (holdWords_sum_eq hw')
      rfl
    · rintro ⟨u, hu⟩
      rw [hS] at hu
      simp only [Set.mem_iUnion, Set.mem_image] at hu
      obtain ⟨j, hj, l, w, hw, rfl⟩ := hu
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      exact ⟨⟨(m, l), w, hw⟩, rfl⟩
  rw [← (Equiv.ofBijective g hg).hasSum_iff]
  have hfib (x : ℕ × ℤ) : HasSum (fun w : holdWords (x.1 + 1) x.2 => ∏ i, varpi (w.1 i))
      (holdLaw (x.1 + 1) x.2) := by
    have := (holdWords_finite (x.1 + 1) x.2).to_subtype
    exact Summable.of_finite.hasSum
  have hf0 : 0 ≤ fun p : (Σ x : ℕ × ℤ, holdWords (x.1 + 1) x.2) => ∏ i, varpi (p.2.1 i) :=
    fun p => Finset.prod_nonneg fun _ _ => varpi_nonneg _
  have hs : Summable fun p : (Σ x : ℕ × ℤ, holdWords (x.1 + 1) x.2) => ∏ i, varpi (p.2.1 i) := by
    rw [summable_sigma_of_nonneg hf0]
    refine ⟨fun x => (hfib x).summable, ?_⟩
    convert hasSum_holdLaw_bkPoints_succ.summable using 1
    funext x
    exact (hfib x).tsum_eq
  convert hs.hasSum using 1
  · funext p
    simp only [g, Equiv.ofBijective_apply, Function.comp_apply, List.map_ofFn, List.prod_ofFn]
  · exact ((hs.hasSum.sigma hfib).unique hasSum_holdLaw_bkPoints_succ).symm

/-- A word of `𝒮₂` is nonempty. -/
theorem ne_nil_of_mem_c3SuffixWords_two {u : List ℤ} (hu : u ∈ c3SuffixWords 2) : u ≠ [] :=
  (mem_c3SuffixWords_two_iff.1 hu).1

private theorem hasSum_c3H17Weight_aux (n : ℕ) : ∀ h : ℤ, (15 - h).toNat = n → ∀ z : ℝ,
    HasSum (fun u : c3SuffixWords 2 => (u.1.map varpi).prod * c3H17Weight h z u.1)
      (c3H17Cost h z) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro h hn z
  rcases le_or_gt 15 h with hh | hh
  · simpa [c3H17Weight_of_le hh, c3H17Cost_of_le hh] using hasSum_prod_varpi_c3SuffixWords_two
  have IH : ∀ d : ℤ, 2 ≤ d → ∀ z', HasSum (fun u : c3SuffixWords 2 =>
      (u.1.map varpi).prod * c3H17Weight (h + d) z' u.1) (c3H17Cost (h + d) z') :=
    fun d hd z' => ih _ (by omega) _ rfl z'
  have hprod0 : ∀ u : List ℤ, 0 ≤ (u.map varpi).prod := fun u =>
    List.prod_nonneg fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
      exact varpi_nonneg b
  have hcf : ∀ d : ℤ, 2 ≤ d → ∀ z', c3H17Cost (h + d) z' ∈ Set.Icc (0 : ℝ) 1 := fun d hd z' =>
    ⟨(IH d hd z').nonneg fun u => mul_nonneg (hprod0 _) (c3H17Weight_nonneg _ _ _),
      hasSum_le (fun u => mul_le_of_le_one_right (hprod0 _) (c3H17Weight_le_one _ _ _))
        (IH d hd z') hasSum_prod_varpi_c3SuffixWords_two⟩
  -- the retained factor `A_d` of the first letter and the inner sum `R_d`
  set A : ℤ → ℝ := fun d => if d ≤ 17 - h then trCapFactor d (z / (2 : ℝ) ^ (h + d)) else 1
    with hA
  set R : ℤ → ℝ := fun d => if d ∈ ({4, 5} : Finset ℤ) then 1 else c3H17Cost (h + d) (9 * z)
    with hR
  set B : ℤ → ℝ := fun d => varpi d * A d * R d with hB
  have hA01 : ∀ d, A d ∈ Set.Icc (0 : ℝ) 1 := fun d => by
    simp only [hA]
    split_ifs
    · exact trCapFactor_mem_Icc _ _
    · simp
  have hB0 : ∀ d, 0 ≤ B d ∧ B d ≤ varpi d := by
    intro d
    by_cases hd : 2 ≤ d
    · have hR01 : R d ∈ Set.Icc (0 : ℝ) 1 := by
        simp only [hR]
        split_ifs
        · simp
        · exact hcf d hd _
      refine ⟨mul_nonneg (mul_nonneg (varpi_nonneg d) (hA01 d).1) hR01.1, ?_⟩
      have := mul_le_mul (mul_le_of_le_one_right (varpi_nonneg d) (hA01 d).2) hR01.2 hR01.1
        (varpi_nonneg d)
      simpa [hB] using this
    · simp [hB, varpi_of_le_one (by omega : d ≤ 1)]
  have hcons : ∀ d u, ((d :: u).map varpi).prod * c3H17Weight h z (d :: u) =
      varpi d * A d * ((u.map varpi).prod *
        if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Weight (h + d) (9 * z) u else 1) := by
    intro d u
    rw [c3H17Weight_cons_of_lt hh, List.map_cons, List.prod_cons]
    ring
  -- the summand, as a function of the first letter and the rest of the word
  let T : Set (ℤ × List ℤ) := {p | p.1 :: p.2 ∈ c3SuffixWords 2}
  let f : ℤ × List ℤ → ℝ :=
    T.indicator fun p => ((p.1 :: p.2).map varpi).prod * c3H17Weight h z (p.1 :: p.2)
  have hfib : ∀ d, HasSum (fun u => f (d, u)) (B d) := by
    intro d
    by_cases hd2 : 2 ≤ d
    swap
    · have h0 : ∀ u, f (d, u) = 0 := fun u =>
        Set.indicator_of_notMem (s := T) (fun hu => hd2 (cons_mem_c3SuffixWords_two.1 hu).1) _
      simp only [h0, hB, varpi_of_le_one (by omega : d ≤ 1), zero_mul]
      exact hasSum_zero
    by_cases hd45 : d ∈ ({4, 5} : Set ℤ)
    · have hdF : d ∈ ({4, 5} : Finset ℤ) := by simpa using hd45
      have hfun : (fun u => f (d, u)) = fun u => if u = [] then B d else 0 := by
        funext u
        by_cases hu : u = []
        · subst hu
          rw [ite_eq_left rfl]
          simp only [f]
          rw [Set.indicator_of_mem (show (d, ([] : List ℤ)) ∈ T from
            cons_mem_c3SuffixWords_two.2 ⟨hd2, fun _ => rfl, fun h => (h hd45).elim⟩), hcons]
          rw [ite_eq_right (fun h' => h'.1 hdF)]
          simp only [hB, hR, ite_eq_left hdF, List.map_nil, List.prod_nil, mul_one]
        · rw [ite_eq_right hu]
          exact Set.indicator_of_notMem (s := T)
            (fun h => hu ((cons_mem_c3SuffixWords_two.1 h).2.1 hd45)) _
      rw [hfun]
      exact hasSum_ite_eq [] (B d)
    · have hdF : d ∉ ({4, 5} : Finset ℤ) := by simpa using hd45
      have hG : ∀ u, (if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then
          c3H17Weight (h + d) (9 * z) u else 1) = c3H17Weight (h + d) (9 * z) u := by
        intro u
        split_ifs with hc
        · rfl
        · have : ¬ h + d ≤ 15 := fun h' => hc ⟨hdF, h'⟩
          exact (c3H17Weight_of_le (by omega) _ _).symm
      have hfun : (fun u => f (d, u)) = (c3SuffixWords 2).indicator fun u =>
          varpi d * A d * ((u.map varpi).prod * c3H17Weight (h + d) (9 * z) u) := by
        funext u
        by_cases hu : u ∈ c3SuffixWords 2
        · rw [Set.indicator_of_mem hu]
          simp only [f]
          rw [Set.indicator_of_mem (show (d, u) ∈ T from
            cons_mem_c3SuffixWords_two.2 ⟨hd2, fun h => (hd45 h).elim, fun _ => hu⟩), hcons, hG]
        · rw [Set.indicator_of_notMem hu]
          exact Set.indicator_of_notMem (s := T)
            (fun h => hu ((cons_mem_c3SuffixWords_two.1 h).2.2 hd45)) _
      rw [hfun, ← hasSum_subtype_iff_indicator]
      have hBd : B d = varpi d * A d * c3H17Cost (h + d) (9 * z) := by
        simp only [hB, hR, ite_eq_right hdF]
      rw [hBd]
      exact (IH d hd2 (9 * z)).mul_left _
  have hf0 : 0 ≤ f := fun p =>
    Set.indicator_nonneg (fun p _ => mul_nonneg (hprod0 _) (c3H17Weight_nonneg _ _ _)) p
  have hfs : Summable f := by
    rw [summable_prod_of_nonneg hf0]
    refine ⟨fun d => (hfib d).summable, ?_⟩
    have : (fun d => ∑' u, f (d, u)) = B := funext fun d => (hfib d).tsum_eq
    rw [this]
    exact summable_varpi.of_nonneg_of_le (fun d => (hB0 d).1) (fun d => (hB0 d).2)
  -- the sum over the first letter is the recursion defining `cf_h(z)`
  have hBsum : HasSum B (c3H17Cost h z) := by
    set C : ℤ → ℝ := fun d => varpi d * (1 - A d * R d) with hC
    have hCs : HasSum C (∑ d ∈ Finset.Icc (2 : ℤ) (17 - h), C d) := by
      apply hasSum_sum_of_ne_finset_zero
      intro d hd
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hd
      rcases hd with hd | hd
      · simp [hC, varpi_of_le_one (by omega : d ≤ 1)]
      · have hA1 : A d = 1 := by
          simp only [hA]
          rw [ite_eq_right (by omega)]
        have hR1 : R d = 1 := by
          simp only [hR]
          split_ifs
          · rfl
          · exact c3H17Cost_of_le (by omega) _
        simp [hC, hA1, hR1]
    have hsub := hasSum_varpi.sub hCs
    rw [c3H17Cost_of_lt hh]
    convert hsub using 1
    · funext d
      simp only [hB, hC]
      ring
    · congr 1
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mem_Icc] at hd
      have hRd : R d = if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then
          c3H17Cost (h + d) (9 * z) else 1 := by
        simp only [hR]
        by_cases h1 : d ∈ ({4, 5} : Finset ℤ)
        · rw [ite_eq_left h1, ite_eq_right (fun h' => h'.1 h1)]
        · rw [ite_eq_right h1]
          by_cases h2 : h + d ≤ 15
          · rw [ite_eq_left ⟨h1, h2⟩]
          · rw [ite_eq_right (fun h' => h2 h'.2)]
            exact c3H17Cost_of_le (by omega) _
      simp only [hC, hRd, hA, ite_eq_left hd.2]
  have hf : HasSum f (c3H17Cost h z) :=
    (hBsum.unique (hfs.hasSum.prod_fiberwise hfib)) ▸ hfs.hasSum
  -- back to the words: `u ↦ (first letter, rest)` is injective on `𝒮₂` with range `T`
  have hgu : ∀ u : c3SuffixWords 2, u.1.headI :: u.1.tail = u.1 := by
    rintro ⟨u, hu⟩
    cases u with
    | nil => exact absurd rfl (ne_nil_of_mem_c3SuffixWords_two hu)
    | cons a u => rfl
  let g : c3SuffixWords 2 → ℤ × List ℤ := fun u => (u.1.headI, u.1.tail)
  have hg : Function.Injective g := fun u v huv => by
    simp only [g, Prod.mk.injEq] at huv
    exact Subtype.ext (by rw [← hgu u, ← hgu v, huv.1, huv.2])
  have hrange : ∀ p ∉ Set.range g, f p = 0 := fun p hp =>
    Set.indicator_of_notMem (s := T) (fun hpT => hp ⟨⟨p.1 :: p.2, hpT⟩, rfl⟩) _
  rw [← hg.hasSum_iff hrange] at hf
  convert hf using 1
  funext u
  rw [Function.comp_apply]
  simp only [f]
  rw [Set.indicator_of_mem (s := T) (show (g u).1 :: (g u).2 ∈ c3SuffixWords 2 by
    rw [hgu]; exact u.2)]
  simp only [g, hgu]

/-- **The future cost sums the retained factors.** For every integer `h` and real `z`, the
series `∑_{u ∈ 𝒮₂} (∏_i ϖ(u_i)) · wt_h(z; u)` over the hold words `𝒮₂` converges
unconditionally to `cf_h(z)`. -/
@[collatz_pos_dens "lem_c3_h17_tree"]
theorem hasSum_c3H17Weight (h : ℤ) (z : ℝ) :
    HasSum (fun u : c3SuffixWords 2 => (u.1.map varpi).prod * c3H17Weight h z u.1)
      (c3H17Cost h z) :=
  hasSum_c3H17Weight_aux _ h rfl z

/-- **The future cost sums the retained factors.** For every integer `h` and real `z`,
`∑_{u ∈ 𝒮₂} (∏_i ϖ(u_i)) · wt_h(z; u) = cf_h(z)`. -/
@[collatz_pos_dens "lem_c3_h17_tree"]
theorem tsum_c3H17Weight (h : ℤ) (z : ℝ) :
    ∑' u : c3SuffixWords 2, (u.1.map varpi).prod * c3H17Weight h z u.1 = c3H17Cost h z :=
  (hasSum_c3H17Weight h z).tsum_eq

end CollatzPosDens
