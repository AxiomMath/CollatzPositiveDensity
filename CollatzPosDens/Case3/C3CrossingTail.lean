/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3CrossingMass
public import CollatzPosDens.Case3.C3CrossingTransfer
public import CollatzPosDens.Renewal.RnPascalTotal

/-!
# Long suffixes after a first raw crossing

Let `ω ∈ ℕ` and let `c, o, r` be integers with `c ≥ 2`, `c ∉ {4, 5}`, `1 ≤ o ≤ c` and `r ≥ 1`.
For `H ∈ ℕ`, the lists `π` of the first raw crossing set `𝒞_ω(c, o, r)` whose raw word runs more
than `H` letters past position `r`, i.e. `j(Bp_{|π|}(π)) - r > H`, carry total weight
`∑ bw^⊗(π) = ϖ(c) 𝖱(r - 1, ω + o - c) (11/16)^H`.

By the raw word transfer `tsum_c3CrossingSet_mul_eq`, applied to the indicator of `|z| - r > H`,
the sum factors as `ϖ(c)` times the raw-prefix mass `𝖱(r - 1, ω + o - c)` times the weight of
the suffix words `u ∈ 𝒮_c` with `|u| > H`. As `c ∉ {4, 5}`, these are the words `u' (e')` with
`u'` a word of length at least `H` of letters `≥ 2` outside `{4, 5}` and `e' ∈ {4, 5}`; the
nonclosing letters carry Pascal mass `11/16` and the closing letters `5/16`, so their weight is
`∑_{m ≥ H} (11/16)^m (5/16) = (11/16)^H`.

## Main results

* `CollatzPosDens.append_singleton_mem_c3SuffixWords_iff`: for `c ∉ {4, 5}`, `l (e) ∈ 𝒮_c` iff
  the letters of `l` are at least `2` and outside `{4, 5}` and `e ∈ {4, 5}`.
* `CollatzPosDens.tsum_ofReal_prod_varpi_c3SuffixWords_lt_length`: for `c ∉ {4, 5}`, the suffix
  words `u ∈ 𝒮_c` with `|u| > H` have total weight `(11/16)^H`.
* `CollatzPosDens.hasSum_trListWeight_c3CrossingSet_tail`: the tail identity above.

## Implementation notes

The sum over the lists with `j(Bp_{|π|}(π)) - r > H` is stated as a `HasSum` over the subtype of
the set `{π ∈ 𝒞_ω(c, o, r) | H < j(Bp_{|π|}(π)) - r}`, which records convergence as well as the
value. The hypothesis `c ≥ 2` is not needed: for `c < 2` every list of `𝒞_ω(c, o, r)` has
weight `0` and `ϖ(c) = 0`, so both sides vanish. The intermediate sums over words are
unconditional sums in `ℝ≥0∞`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The suffix words of a nonclosing crossing letter `c ∉ {4, 5}`, characterised letterwise. -/
private lemma mem_c3SuffixWords_iff' {c : ℤ} (hc : c ∉ ({4, 5} : Set ℤ)) {u : List ℤ} :
    u ∈ c3SuffixWords c ↔ u ≠ [] ∧ (∀ x ∈ u, 2 ≤ x) ∧
      ∀ i (hi : i < u.length), (u[i] ∈ ({4, 5} : Set ℤ) ↔ i + 1 = u.length) := by
  rw [mem_c3SuffixWords_of_notMem hc]
  constructor
  · rintro ⟨hlen, l, hl⟩
    obtain ⟨h2, hiff, -⟩ := mem_holdWords_iff.1 hl
    refine ⟨List.ne_nil_of_length_pos hlen, fun x hx => ?_, fun i hi => hiff ⟨i, hi⟩⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem hx
    exact h2 i
  · rintro ⟨hne, h2, hiff⟩
    exact ⟨List.length_pos_iff.2 hne, _, mem_holdWords_iff.2
      ⟨fun i => h2 _ (List.getElem_mem _), fun i => hiff i i.2, rfl⟩⟩

/-- For `c ∉ {4, 5}`, a word `l (e)` lies in `𝒮_c` iff the letters of `l` are at least `2` and
outside `{4, 5}` and `e ∈ {4, 5}`. -/
theorem append_singleton_mem_c3SuffixWords_iff {c : ℤ} (hc : c ∉ ({4, 5} : Set ℤ))
    {l : List ℤ} {e : ℤ} :
    l ++ [e] ∈ c3SuffixWords c ↔
      (∀ x ∈ l, 2 ≤ x ∧ x ∉ ({4, 5} : Set ℤ)) ∧ e ∈ ({4, 5} : Set ℤ) := by
  rw [mem_c3SuffixWords_iff' hc]
  constructor
  · rintro ⟨-, h2, hiff⟩
    refine ⟨fun x hx => ⟨h2 x (by simp [hx]), fun hx45 => ?_⟩, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have := (hiff i (by simp; omega)).1 (by rwa [List.getElem_append_left hi])
      simp at this
      omega
    · have := (hiff l.length (by simp)).2 (by simp)
      simpa using this
  · rintro ⟨hl, he⟩
    refine ⟨by simp, fun x hx => ?_, fun i hi => ?_⟩
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact (hl x hx).1
      · rcases he with rfl | rfl <;> norm_num
    · simp only [List.length_append, List.length_singleton] at hi ⊢
      rcases (show i < l.length ∨ i = l.length by omega) with hi' | rfl
      · rw [List.getElem_append_left hi']
        exact ⟨fun h => absurd h (hl _ (List.getElem_mem hi')).2, fun h => by omega⟩
      · simpa using he

private lemma ofReal_varpiIn_tsum :
    ∑' b, ENNReal.ofReal (varpiIn b) = ENNReal.ofReal (11 / 16) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg varpiIn_nonneg hasSum_varpiIn.summable,
    hasSum_varpiIn.tsum_eq]

private lemma ofReal_varpiLast_tsum :
    ∑' b, ENNReal.ofReal (varpiLast b) = ENNReal.ofReal (5 / 16) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg varpiLast_nonneg hasSum_varpiLast.summable,
    hasSum_varpiLast.tsum_eq]

/-- The weight of a word `v (e)`, cut off outside `𝒮_c`, is `∏ ϖ_in(vᵢ) ϖ_last(e)`. -/
private lemma indicator_c3SuffixWords_ofFn_append {c : ℤ} (hc : c ∉ ({4, 5} : Set ℤ)) {n : ℕ}
    (v : Fin n → ℤ) (e : ℤ) :
    (c3SuffixWords c).indicator (fun u => ENNReal.ofReal (u.map varpi).prod)
        (List.ofFn v ++ [e]) =
      (∏ i, ENNReal.ofReal (varpiIn (v i))) * ENNReal.ofReal (varpiLast e) := by
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => varpiIn_nonneg _,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => varpiIn_nonneg _)]
  by_cases hmem : List.ofFn v ++ [e] ∈ c3SuffixWords c
  · rw [Set.indicator_of_mem hmem]
    obtain ⟨hl, he⟩ := (append_singleton_mem_c3SuffixWords_iff hc).1 hmem
    congr 1
    simp only [List.map_append, List.map_ofFn, List.prod_append, List.prod_ofFn,
      Function.comp_apply, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      varpiLast_of_mem he]
    refine congrArg (· * varpi e) (Finset.prod_congr rfl fun i _ => ?_)
    exact (varpiIn_of_notMem (hl _ (List.mem_ofFn.2 ⟨i, rfl⟩)).2).symm
  · rw [Set.indicator_of_notMem hmem]
    symm
    rw [ENNReal.ofReal_eq_zero]
    refine le_of_eq ?_
    by_contra hne
    apply hmem
    rw [append_singleton_mem_c3SuffixWords_iff hc]
    obtain ⟨hv, he⟩ := mul_ne_zero_iff.1 hne
    rw [Finset.prod_ne_zero_iff] at hv
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      have hi := hv i (Finset.mem_univ _)
      have h45 : v i ∉ ({4, 5} : Set ℤ) := fun h => hi (varpiIn_of_mem h)
      rw [varpiIn_of_notMem h45] at hi
      exact ⟨two_le_of_varpi_ne_zero hi, h45⟩
    · by_contra h
      exact he (varpiLast_of_notMem h)

/-- For `c ∉ {4, 5}`, the suffix words `u ∈ 𝒮_c` with `|u| > H` have total weight
`∑ ∏ᵢ ϖ(uᵢ) = (11/16)^H`. -/
theorem tsum_ofReal_prod_varpi_c3SuffixWords_lt_length {c : ℤ} (hc : c ∉ ({4, 5} : Set ℤ))
    (H : ℕ) :
    ∑' u : c3SuffixWords c, ENNReal.ofReal (u.1.map varpi).prod *
        (if H < u.1.length then 1 else 0) = ENNReal.ofReal ((11 / 16) ^ H) := by
  let F : List ℤ → ℝ≥0∞ := fun u => (c3SuffixWords c).indicator
    (fun u => ENNReal.ofReal (u.map varpi).prod) u * (if H < u.length then 1 else 0)
  let g : (Σ k : ℕ, (Fin (H + k) → ℤ) × ℤ) → List ℤ := fun x => List.ofFn x.2.1 ++ [x.2.2]
  have hg : Function.Injective g := by
    rintro ⟨k, v, e⟩ ⟨k', v', e'⟩ h
    simp only [g] at h
    have hk : k = k' := by simpa using congrArg List.length h
    subst hk
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    obtain rfl := List.ofFn_injective h1
    obtain rfl : e = e' := by simpa using h2
    rfl
  have hsupp : Function.support F ⊆ Set.range g := by
    intro u hu
    simp only [Function.mem_support, F, ne_eq, mul_eq_zero, not_or, ite_eq_right_iff,
      one_ne_zero, imp_false, not_not] at hu
    obtain ⟨hu1, hlen⟩ := hu
    have hmem : u ∈ c3SuffixWords c := by
      by_contra h
      exact hu1 (Set.indicator_of_notMem h _)
    have hne : u ≠ [] := by rintro rfl; simp at hlen
    obtain ⟨k, hk⟩ : ∃ k, u.dropLast.length = H + k :=
      ⟨u.dropLast.length - H, by simp; omega⟩
    refine ⟨⟨k, fun i => u.dropLast[(i : ℕ)]'(by have := i.2; omega), u.getLast hne⟩, ?_⟩
    simp only [g]
    conv_rhs => rw [← List.dropLast_append_getLast hne]
    congr 1
    refine List.ext_getElem (by simp [hk]) fun i h1 h2 => ?_
    simp
  have hF : ∀ x, F (g x) = (∏ i, ENNReal.ofReal (varpiIn (x.2.1 i))) *
      ENNReal.ofReal (varpiLast x.2.2) := by
    rintro ⟨k, v, e⟩
    simp only [F, g, indicator_c3SuffixWords_ofFn_append hc]
    simp only [List.length_append, List.length_ofFn, List.length_singleton]
    have : H < H + k + 1 := by omega
    simp [this]
  have h1 : (1 : ℝ≥0∞) - ENNReal.ofReal (11 / 16) = ENNReal.ofReal (5 / 16) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
    norm_num
  have h2 : ENNReal.ofReal (11 / 16) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)
  calc ∑' u : c3SuffixWords c, ENNReal.ofReal (u.1.map varpi).prod *
        (if H < u.1.length then 1 else 0)
      = ∑' u, F u := by
        rw [tsum_subtype (c3SuffixWords c)
          (fun u => ENNReal.ofReal (u.map varpi).prod * (if H < u.length then 1 else 0))]
        refine tsum_congr fun u => ?_
        by_cases hu : u ∈ c3SuffixWords c
        · simp [F, Set.indicator_of_mem hu]
        · simp [F, Set.indicator_of_notMem hu]
    _ = ∑' x, F (g x) := (hg.tsum_eq hsupp).symm
    _ = ∑' k : ℕ, ∑' x : (Fin (H + k) → ℤ) × ℤ,
          (∏ i, ENNReal.ofReal (varpiIn (x.1 i))) * ENNReal.ofReal (varpiLast x.2) := by
        rw [ENNReal.tsum_sigma']
        exact tsum_congr fun k => tsum_congr fun x => hF ⟨k, x⟩
    _ = ∑' k : ℕ, ENNReal.ofReal (11 / 16) ^ H * ENNReal.ofReal (5 / 16) *
          ENNReal.ofReal (11 / 16) ^ k := by
        refine tsum_congr fun k => ?_
        rw [ENNReal.tsum_prod']
        simp only [ENNReal.tsum_mul_left, ofReal_varpiLast_tsum, ENNReal.tsum_mul_right]
        rw [tsum_pi_fin_prod_ennreal_const (fun b => ENNReal.ofReal (varpiIn b)),
          ofReal_varpiIn_tsum, pow_add]
        ring
    _ = ENNReal.ofReal ((11 / 16) ^ H) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, h1, mul_assoc,
          ENNReal.mul_inv_cancel (by simp) ENNReal.ofReal_ne_top, mul_one,
          ENNReal.ofReal_pow (by norm_num)]

/-- **Long suffixes after a first raw crossing.** Let `ω ∈ ℕ`, let `c, o, r` be integers with
`c ∉ {4, 5}`, `1 ≤ o ≤ c` and `r ≥ 1`, and let `H ∈ ℕ`. Then the series
`∑ bw^⊗(π)`, over the lists `π ∈ 𝒞_ω(c, o, r)` with `j(Bp_{|π|}(π)) - r > H`, converges to
`ϖ(c) 𝖱(r - 1, ω + o - c) (11/16)^H`. -/
@[collatz_pos_dens "lem_c3_crossing_tail"]
theorem hasSum_trListWeight_c3CrossingSet_tail (ω : ℕ) {c o : ℤ} {r : ℕ}
    (hc45 : c ∉ ({4, 5} : Set ℤ)) (ho : 1 ≤ o) (hoc : o ≤ c) (hr : 1 ≤ r) (H : ℕ) :
    HasSum (fun π : {π ∈ c3CrossingSet ω c o r | (H : ℤ) < (chBlockPath π π.length).1 - r} ↦
        trListWeight π.1)
      (varpi c * rawMass (r - 1) (ω + o - c) * (11 / 16) ^ H) := by
  set S := {π ∈ c3CrossingSet ω c o r | (H : ℤ) < (chBlockPath π π.length).1 - r}
  by_cases hc : 2 ≤ c
  · have hf (π : S) : 0 ≤ trListWeight π.1 := trListWeight_nonneg _
    have hx : 0 ≤ varpi c * rawMass (r - 1) (ω + o - c) * (11 / 16) ^ H :=
      mul_nonneg (mul_nonneg (varpi_nonneg c) (rawMass_nonneg _ _)) (by positivity)
    let Ψ : List ℤ → ℝ≥0∞ := fun z => if (H : ℤ) < (z.length : ℤ) - r then 1 else 0
    have key := tsum_c3CrossingSet_mul_eq ω hc ho hoc hr Ψ
    have hL : ∑' π : c3CrossingSet ω c o r,
        ENNReal.ofReal (trListWeight π.1) * Ψ (c3RawWord π.1) =
          ∑' π : S, ENNReal.ofReal (trListWeight π.1) := by
      rw [tsum_subtype (c3CrossingSet ω c o r)
          (fun π => ENNReal.ofReal (trListWeight π) * Ψ (c3RawWord π)),
        tsum_subtype S (fun π => ENNReal.ofReal (trListWeight π))]
      refine tsum_congr fun π => ?_
      have hlen : ((c3RawWord π).length : ℤ) = (chBlockPath π π.length).1 := by
        rw [length_c3RawWord, Int.toNat_of_nonneg (chBlockPath_fst_nonneg _ _)]
      by_cases hπ : π ∈ c3CrossingSet ω c o r
      · rw [Set.indicator_of_mem hπ]
        by_cases hH : (H : ℤ) < (chBlockPath π π.length).1 - r
        · rw [Set.indicator_of_mem (show π ∈ S from ⟨hπ, hH⟩)]
          simp [Ψ, hlen, hH]
        · rw [Set.indicator_of_notMem (show π ∉ S from fun h => hH h.2)]
          simp [Ψ, hlen, hH]
      · rw [Set.indicator_of_notMem hπ, Set.indicator_of_notMem (show π ∉ S from fun h => hπ h.1)]
    have hR : ∀ w : {w : List ℤ // w.length = r - 1 ∧ (∀ x ∈ w, 2 ≤ x) ∧ w.sum = ω + o - c},
        ∑' u : c3SuffixWords c, ENNReal.ofReal (w.1.map varpi).prod *
          ENNReal.ofReal (u.1.map varpi).prod * Ψ (w.1 ++ c :: u.1) =
        ENNReal.ofReal (w.1.map varpi).prod * ENNReal.ofReal ((11 / 16) ^ H) := by
      intro w
      rw [← tsum_ofReal_prod_varpi_c3SuffixWords_lt_length hc45 H, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun u => ?_
      have : (H : ℤ) < (((w.1 ++ c :: u.1).length : ℕ) : ℤ) - r ↔ H < u.1.length := by
        simp only [List.length_append, List.length_cons, w.2.1]
        omega
      simp only [Ψ, this, mul_assoc]
    simp only [hR, hL, ENNReal.tsum_mul_right, tsum_ofReal_prod_varpi_rawWords] at key
    rw [← ENNReal.ofReal_mul (rawMass_nonneg _ _), ← ENNReal.ofReal_mul (varpi_nonneg c),
      ← mul_assoc] at key
    have hs : Summable fun π : S ↦ trListWeight π.1 := by
      have := ENNReal.summable_toReal (key ▸ ENNReal.ofReal_ne_top)
      simpa [ENNReal.toReal_ofReal (hf _)] using this
    rw [← ENNReal.ofReal_tsum_of_nonneg hf hs,
      ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hf) hx] at key
    exact key ▸ hs.hasSum
  · rw [varpi_of_le_one (by omega), zero_mul, zero_mul]
    convert hasSum_zero with π
    exact trListWeight_eq_zero_of_mem_c3CrossingSet (by omega) hr π.2.1

end CollatzPosDens
