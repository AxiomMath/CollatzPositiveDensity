/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnCrossE
public import CollatzPosDens.Renewal.RnCrossP
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnGeom4
public import CollatzPosDens.Renewal.RnCrossLaw
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.Renewal.RnFpMgf
public import CollatzPosDens.Renewal.RnFpSupport
public import CollatzPosDens.Renewal.RnHoeffding
public import CollatzPosDens.Renewal.RnMgfSixteenth
public import CollatzPosDens.Renewal.RnRawOddSum

/-!
# Horizontal tail bounds for the first-passage law

For `s ∈ ℕ` and real `u ≥ 2`, this file bounds the mass of the first-passage law `F_s` on the
columns `r` far from the drift, `|r - s/4| ≥ u`, in two cases.

For `s ≤ 5` every contributing column has `r ≥ 1`, which together with `u ≥ 2 > 5/4` forces
`r ≥ u`; the exponential moment `∑ F_s(r, ℓ) e^{r/16} ≤ M₄₅(1/16)^{s+1} ≤ (5/4)^6 ≤ 4` then
gives the bound `4 e^{-u/16}`.

For `s ≥ 6` put `n = s - 4`; the exact crossing law bounds the column mass by
`e_n(r - 1) + ∑_j p_n(j) ν₄₅(r - 1 - j)`. Since `0 ≤ e_n ≤ p_n`, the tail is at most twice the
mass of the straddle weights `p_n(j)` with `|j - n/4| ≥ u/2`, plus the total straddle mass
`∑_j p_n(j) = 1` times the geometric tail `∑_{H ≥ u/2} ν₄₅(H)`. As `u ≥ 2`, both indices
`k ∈ {2j, 2j + 1}` of such a `j` satisfy `|k - n/2| ≥ u - 1 ≥ u/2`, so the Hoeffding bound for
row `n` makes the first mass at most `2 e^{-u²/(2n)}`, and the exponential moment
`M₄₅(1/16) ≤ 5/4` makes the geometric tail at most `(5/4) e^{-u/32}`.

## Main results

* `CollatzPosDens.summable_firstPassageLaw_hor_tail`: the column masses on
  `|r - s/4| ≥ u` are summable.
* `CollatzPosDens.tsum_firstPassageLaw_hor_tail_le_four_mul_exp`: the bound `4 e^{-u/16}` for
  `s ≤ 5` and `u ≥ 2`.
* `CollatzPosDens.tsum_firstPassageLaw_add_four_hor_tail_le`: the bound
  `4 e^{-u²/(2n)} + (5/4) e^{-u/32}` for `s = n + 4 ≥ 6` and `u ≥ 2`.

## Implementation notes

The sum over `r` with `|r - s/4| ≥ u` is the unconditional sum over the subtype of such `r`.
Since `tsum` of a non-summable family is `0`, summability is stated separately. The geometric
tail of `ν₄₅` is bounded through the exponential moment `M₄₅(1/16) ≤ 5/4` rather than summed in
closed form.

## References

* [Mazur, *Collatz positive density*], §6.5.
-/

@[expose] public section

namespace CollatzPosDens

open Real Finset

/-- A real family whose `ofReal`-sum is at most `ofReal c` is summable with sum at most `c`. -/
private lemma horTail_summable_tsum_le {α : Type*} {g : α → ℝ} (hg : ∀ a, 0 ≤ g a) {c : ℝ}
    (hc : 0 ≤ c) (h : ∑' a, ENNReal.ofReal (g a) ≤ ENNReal.ofReal c) :
    Summable g ∧ ∑' a, g a ≤ c := by
  have hne : ∑' a, ENNReal.ofReal (g a) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hs : Summable g := by
    simpa [ENNReal.toReal_ofReal (hg _)] using ENNReal.summable_toReal hne
  refine ⟨hs, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg hg hs] at h
  exact (ENNReal.ofReal_le_ofReal_iff hc).1 h

/-- Fiberwise sums of a summable family on `ℤ × ℤ`. -/
private lemma horTail_hasSum_fiber {f : ℤ × ℤ → ℝ} (hf : Summable f) :
    HasSum (fun r : ℤ ↦ ∑' ℓ : ℤ, f (r, ℓ)) (∑' x, f x) :=
  hf.hasSum.prod_fiberwise fun b ↦ (hf.prod_factor b).hasSum

/-- The column masses `∑_ℓ F_s(r, ℓ)` have sum `1`. -/
private lemma horTail_hasSum_col (s : ℕ) :
    HasSum (fun r : ℤ ↦ ∑' ℓ : ℤ, firstPassageLaw s (r, ℓ)) 1 := by
  have h := horTail_hasSum_fiber (hasSum_firstPassageLaw s).summable
  rwa [tsum_firstPassageLaw] at h

/-- The column masses on `|r - s/4| ≥ u` are summable. -/
theorem summable_firstPassageLaw_hor_tail (s : ℕ) (u : ℝ) :
    Summable fun r : {r : ℤ // u ≤ |(r : ℝ) - s / 4|} ↦
      ∑' ℓ : ℤ, firstPassageLaw s ((r : ℤ), ℓ) :=
  (horTail_hasSum_col s).summable.comp_injective Subtype.val_injective

/-- The boundary weight is at most the straddle weight. -/
private lemma horTail_boundaryWeight_le (n : ℕ) (j : ℤ) :
    boundaryWeight n j ≤ straddleWeight n j := by
  by_cases h : 1 ≤ n ∧ 1 ≤ j
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = (k : ℤ) + 1 := ⟨(j - 1).toNat, by omega⟩
    rw [boundaryWeight_succ_natCast_succ, show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; rfl,
      straddleWeight_natCast]
    have h1 : m.choose (2 * k + 1) ≤ (m + 1 + 1).choose (2 * (k + 1) + 1) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by ring, Nat.choose_succ_succ',
        show 2 * k + 2 = (2 * k + 1) + 1 by ring, Nat.choose_succ_succ']
      omega
    have h1' : (m.choose (2 * k + 1) : ℝ) ≤ ((m + 1 + 1).choose (2 * (k + 1) + 1) : ℝ) := by
      exact_mod_cast h1
    have hp : (0 : ℝ) < 2 ^ (m + 1) := by positivity
    rw [div_div, div_le_div_iff₀ (by positivity) hp]
    nlinarith [Nat.cast_nonneg (α := ℝ) (m.choose (2 * k + 1))]
  · rw [boundaryWeight_of_not h]
    exact straddleWeight_nonneg _ _

/-- The straddle weight `p_n(j)` vanishes for `j > n`. -/
private lemma horTail_straddleWeight_eq_zero {n j : ℕ} (hj : n < j) : straddleWeight n j = 0 := by
  rw [straddleWeight_natCast, Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- Pascal's rule for the straddle weight. -/
private lemma horTail_straddleWeight_eq (n j : ℕ) :
    straddleWeight n j = ((n.choose (2 * j) : ℝ) + n.choose (2 * j + 1)) / 2 ^ n := by
  rw [straddleWeight_natCast, Nat.choose_succ_succ']
  push_cast; rfl

private lemma horTail_sum_pairs (g : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ range m, (g (2 * j) + g (2 * j + 1)) = ∑ k ∈ range (2 * m), g k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ,
      sum_range_succ]
    ring

/-- Hoeffding bound for the straddle weights of row `n`. -/
private lemma horTail_sum_straddle_le (n : ℕ) (hn : 1 ≤ n) (P : ℕ → Prop) [DecidablePred P]
    {w : ℝ} (hw : 0 ≤ w)
    (hP : ∀ j, P j → w ≤ |((2 * j : ℕ) : ℝ) - n / 2| ∧ w ≤ |((2 * j + 1 : ℕ) : ℝ) - n / 2|) :
    ∑ j ∈ range (n + 1), (if P j then straddleWeight n j else 0) ≤
      2 * exp (-(2 * w ^ 2 / n)) := by
  set g : ℕ → ℝ := fun k ↦ if w ≤ |(k : ℝ) - n / 2| then (n.choose k : ℝ) / 2 ^ n else 0
  have hg0 : ∀ k, 0 ≤ g k := fun k ↦ ite_nonneg (by positivity) le_rfl
  calc ∑ j ∈ range (n + 1), (if P j then straddleWeight n j else 0)
      ≤ ∑ j ∈ range (n + 1), (g (2 * j) + g (2 * j + 1)) := by
        refine sum_le_sum fun j _ ↦ ?_
        split_ifs with hj
        · obtain ⟨h1, h2⟩ := hP j hj
          simp only [g, h1, h2, ↓reduceIte, horTail_straddleWeight_eq, add_div, le_refl]
        · exact add_nonneg (hg0 _) (hg0 _)
    _ = ∑ k ∈ range (2 * (n + 1)), g k := horTail_sum_pairs g _
    _ = ∑ k ∈ range (n + 1), g k := by
        refine (sum_subset (range_subset_range.2 (by omega)) fun k _ hk ↦ ?_).symm
        simp only [mem_range, not_lt] at hk
        simp [g, Nat.choose_eq_zero_of_lt (show n < k by omega)]
    _ = ∑ k ∈ (range (n + 1)).filter (fun k : ℕ ↦ w ≤ |(k : ℝ) - n / 2|),
          (n.choose k : ℝ) / 2 ^ n := by rw [sum_filter]
    _ ≤ 2 * exp (-(2 * w ^ 2 / n)) := binomial_tail_hoeffding n hn w hw

/-- The straddle weights of row `n` have total mass `1`: the odd-index entries of row `n + 1`
sum to `2^n`. -/
private lemma horTail_sum_straddleWeight (n : ℕ) :
    ∑ j ∈ range (n + 1), straddleWeight n j = 1 := by
  simp only [straddleWeight_natCast]
  rw [← sum_div, div_eq_one_iff_eq (by positivity)]
  have h2 : ∑ i ∈ range (2 * (n + 1)), n.choose i = ∑ i ∈ range (n + 1), n.choose i :=
    (sum_subset (range_subset_range.2 (by omega)) fun i _ hi ↦ by
      simp only [mem_range, not_lt] at hi
      exact Nat.choose_eq_zero_of_lt (by omega)).symm
  have h := (sum_range_choose_succ_odd n (n + 1)).trans (h2.trans (Nat.sum_range_choose n))
  exact_mod_cast h

private lemma horTail_mgfNu45_le : mgfNu45 (1 / 16) ≤ ENNReal.ofReal (5 / 4) := by
  refine mgfNu45_one_div_sixteen_le.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- `∑_{H} ν₄₅(H) e^{H/16} ≤ 5/4` as a real series. -/
private lemma horTail_nu45_mgf :
    Summable (fun h : ℤ ↦ nu45 h * exp (1 / 16 * h)) ∧
      ∑' h : ℤ, nu45 h * exp (1 / 16 * h) ≤ 5 / 4 := by
  refine horTail_summable_tsum_le (fun h ↦ mul_nonneg (nu45_nonneg h) (exp_pos _).le)
    (by norm_num) ?_
  rw [← mgfNu45_eq_tsum_int]
  exact horTail_mgfNu45_le

/-- The geometric tail `∑_{H ≥ v} ν₄₅(H) ≤ (5/4) e^{-v/16}`. -/
private lemma horTail_nu45_tail (v : ℝ) :
    Summable (fun h : ℤ ↦ if v ≤ (h : ℝ) then nu45 h else 0) ∧
      ∑' h : ℤ, (if v ≤ (h : ℝ) then nu45 h else 0) ≤ 5 / 4 * exp (-(v / 16)) := by
  obtain ⟨hs, hle⟩ := horTail_nu45_mgf
  have hpt : ∀ h : ℤ, (if v ≤ (h : ℝ) then nu45 h else 0) ≤
      exp (-(v / 16)) * (nu45 h * exp (1 / 16 * h)) := by
    intro h
    split_ifs with hh
    · have : 1 ≤ exp (-(v / 16)) * exp (1 / 16 * h) := by
        rw [← exp_add]; exact one_le_exp (by linarith)
      nlinarith [nu45_nonneg h]
    · exact mul_nonneg (exp_pos _).le (mul_nonneg (nu45_nonneg h) (exp_pos _).le)
  have h0 : ∀ h : ℤ, 0 ≤ (if v ≤ (h : ℝ) then nu45 h else 0) := fun h ↦
    ite_nonneg (nu45_nonneg h) le_rfl
  have hs' := Summable.of_nonneg_of_le h0 hpt (hs.mul_left _)
  refine ⟨hs', ?_⟩
  calc ∑' h : ℤ, (if v ≤ (h : ℝ) then nu45 h else 0)
      ≤ ∑' h : ℤ, exp (-(v / 16)) * (nu45 h * exp (1 / 16 * h)) :=
        hs'.tsum_le_tsum hpt (hs.mul_left _)
    _ = exp (-(v / 16)) * ∑' h : ℤ, nu45 h * exp (1 / 16 * h) := tsum_mul_left
    _ ≤ exp (-(v / 16)) * (5 / 4) := by gcongr
    _ = 5 / 4 * exp (-(v / 16)) := by ring

/-- For `s ≤ 5` and `u ≥ 2`, the horizontal tail of `F_s` is at most `4 e^{-u/16}`. -/
theorem tsum_firstPassageLaw_hor_tail_le_four_mul_exp {s : ℕ} (hs : s ≤ 5) {u : ℝ}
    (hu : 2 ≤ u) :
    ∑' r : {r : ℤ // u ≤ |(r : ℝ) - s / 4|}, ∑' ℓ : ℤ, firstPassageLaw s ((r : ℤ), ℓ) ≤
      4 * exp (-(u / 16)) := by
  set g : ℤ × ℤ → ℝ := fun x ↦ firstPassageLaw s x * exp (1 / 16 * x.1)
  have hg0 : ∀ x, 0 ≤ g x := fun x ↦ mul_nonneg (firstPassageLaw_nonneg _ _) (exp_pos _).le
  obtain ⟨hgs, hgle⟩ := horTail_summable_tsum_le hg0 (by norm_num : (0 : ℝ) ≤ 4) (by
    refine (tsum_ofReal_firstPassageLaw_mul_exp_le s (by norm_num : (0 : ℝ) ≤ 1 / 16)).trans ?_
    calc mgfNu45 (1 / 16) ^ (s + 1) ≤ ENNReal.ofReal (5 / 4) ^ (s + 1) := by
          gcongr
          exact horTail_mgfNu45_le
      _ = ENNReal.ofReal ((5 / 4) ^ (s + 1)) := (ENNReal.ofReal_pow (by norm_num) _).symm
      _ ≤ ENNReal.ofReal 4 := ENNReal.ofReal_le_ofReal
          (((pow_le_pow_right₀ (by norm_num) (by omega : s + 1 ≤ 6))).trans (by norm_num)))
  have hG := horTail_hasSum_fiber hgs
  have hpt : ∀ r : {r : ℤ // u ≤ |(r : ℝ) - s / 4|},
      ∑' ℓ : ℤ, firstPassageLaw s ((r : ℤ), ℓ) ≤ exp (-(u / 16)) * ∑' ℓ : ℤ, g ((r : ℤ), ℓ) := by
    intro r
    rw [← tsum_mul_left]
    refine ((hasSum_firstPassageLaw s).summable.prod_factor r).tsum_le_tsum (fun ℓ ↦ ?_)
      ((hgs.prod_factor r).mul_left _)
    by_cases h0 : firstPassageLaw s ((r : ℤ), ℓ) = 0
    · rw [h0]; exact mul_nonneg (exp_pos _).le (hg0 _)
    · have h1 : (1 : ℝ) ≤ ((r : ℤ) : ℝ) := by exact_mod_cast (firstPassageLaw_support h0).1
      have hs' : (s : ℝ) ≤ 5 := by exact_mod_cast hs
      have hru : u ≤ ((r : ℤ) : ℝ) := by
        rcases le_abs'.1 r.2 with h | h <;> linarith
      have he : 1 ≤ exp (-(u / 16)) * exp (1 / 16 * ((r : ℤ) : ℝ)) := by
        rw [← exp_add]; exact one_le_exp (by linarith)
      simp only [g]
      nlinarith [firstPassageLaw_nonneg s ((r : ℤ), ℓ)]
  calc ∑' r : {r : ℤ // u ≤ |(r : ℝ) - s / 4|}, ∑' ℓ : ℤ, firstPassageLaw s ((r : ℤ), ℓ)
      ≤ ∑' r : {r : ℤ // u ≤ |(r : ℝ) - s / 4|}, exp (-(u / 16)) * ∑' ℓ : ℤ, g ((r : ℤ), ℓ) :=
        (summable_firstPassageLaw_hor_tail s u).tsum_le_tsum hpt
          ((hG.summable.mul_left _).comp_injective Subtype.val_injective)
    _ ≤ ∑' r : ℤ, exp (-(u / 16)) * ∑' ℓ : ℤ, g (r, ℓ) :=
        tsum_comp_le_tsum_of_inj (hG.summable.mul_left _)
          (fun r ↦ mul_nonneg (exp_pos _).le (tsum_nonneg fun ℓ ↦ hg0 _)) Subtype.val_injective
    _ = exp (-(u / 16)) * ∑' x, g x := by rw [tsum_mul_left, hG.tsum_eq]
    _ ≤ exp (-(u / 16)) * 4 := by gcongr
    _ = 4 * exp (-(u / 16)) := by ring

/-- Shifting the index of a series on `ℤ` by `1 + c`. -/
private lemma horTail_hasSum_shift' {φ : ℤ → ℝ} {a : ℝ} (h : HasSum φ a) (c : ℤ) :
    HasSum (fun r : ℤ ↦ φ (r - 1 - c)) a := by
  have h' : HasSum (fun r : ℤ ↦ φ (r - (1 + c))) a := (Equiv.subRight (1 + c)).hasSum_iff.2 h
  simpa [sub_sub] using h'

/-- The boundary part of a column mass of the crossing law. -/
private lemma horTail_boundaryWeight_le_sum {n m : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hmu : u ≤ |(m : ℝ) - n / 4|) :
    boundaryWeight n m ≤ ∑ j ∈ range (n + 1),
      (if u / 2 ≤ |(j : ℝ) - n / 4| then straddleWeight n j else 0) *
        (if (m : ℤ) - j = 0 then (1 : ℝ) else 0) := by
  by_cases hm : m ≤ n
  · rw [sum_eq_single m]
    · simp only [sub_self, ↓reduceIte, mul_one]
      rw [ite_eq_left (by linarith)]
      exact horTail_boundaryWeight_le n m
    · intro b _ hb
      rw [ite_eq_right (show ¬((m : ℤ) - b = 0) by omega), mul_zero]
    · intro hm'
      simp only [mem_range] at hm'
      omega
  · calc boundaryWeight n m ≤ straddleWeight n m := horTail_boundaryWeight_le n m
      _ = 0 := horTail_straddleWeight_eq_zero (by omega)
      _ ≤ _ := sum_nonneg fun j _ ↦
        mul_nonneg (ite_nonneg (straddleWeight_nonneg _ _) le_rfl) (ite_nonneg zero_le_one le_rfl)

/-- A straddle term is split into its far-column part and its geometric-tail part. -/
private lemma horTail_straddle_nu45_le {n m j : ℕ} {u : ℝ} (hmu : u ≤ |(m : ℝ) - n / 4|) :
    straddleWeight n j * nu45 ((m : ℤ) - j) ≤
      (if u / 2 ≤ |(j : ℝ) - n / 4| then straddleWeight n j else 0) * nu45 ((m : ℤ) - j) +
        straddleWeight n j *
          (if u / 2 ≤ (((m : ℤ) - j : ℤ) : ℝ) then nu45 ((m : ℤ) - j) else 0) := by
  have hνt0 : 0 ≤ (if u / 2 ≤ (((m : ℤ) - j : ℤ) : ℝ) then nu45 ((m : ℤ) - j) else 0) :=
    ite_nonneg (nu45_nonneg _) le_rfl
  by_cases hD : u / 2 ≤ |(j : ℝ) - n / 4|
  · rw [ite_eq_left hD]
    linarith [mul_nonneg (straddleWeight_nonneg n j) hνt0]
  rw [ite_eq_right hD, zero_mul, zero_add]
  by_cases hmj : (m : ℤ) - j ≤ 0
  · simp [nu45_of_nonpos hmj]
  have hle : u / 2 ≤ (((m : ℤ) - j : ℤ) : ℝ) := by
    have hpos : (0 : ℝ) < (((m : ℤ) - j : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < m - j)
    push_cast at hpos ⊢
    obtain ⟨ha, hb⟩ := abs_lt.1 (not_le.1 hD)
    rcases le_abs'.1 hmu with hc | hc <;> linarith
  simp only [ite_eq_left hle, le_refl]

/-- In the case `s = n + 4`, a column mass far from the drift is bounded through the crossing
law by the far straddle weights and the geometric tail of `ν₄₅`. -/
private lemma horTail_col_le_of_two_le (n : ℕ) (hn : 2 ≤ n) {u : ℝ} (hu : 0 ≤ u) {r : ℤ}
    (hr : u ≤ |(r : ℝ) - ((n + 4 : ℕ) : ℝ) / 4|) :
    ∑' ℓ : ℤ, firstPassageLaw (n + 4 : ℕ) (r, ℓ) ≤ ∑ j ∈ range (n + 1),
      ((if u / 2 ≤ |(j : ℝ) - n / 4| then straddleWeight n j else 0) *
          ((if r - 1 - j = 0 then (1 : ℝ) else 0) + nu45 (r - 1 - j)) +
        straddleWeight n j *
          (if u / 2 ≤ ((r - 1 - j : ℤ) : ℝ) then nu45 (r - 1 - j) else 0)) := by
  rcases le_or_gt r 0 with h | h
  · have : ∀ ℓ, firstPassageLaw (n + 4 : ℕ) (r, ℓ) = 0 := fun ℓ ↦ by
      by_contra hne
      have := (firstPassageLaw_support hne).1
      simp only at this
      omega
    rw [tsum_congr this, tsum_zero]
    exact sum_nonneg fun j _ ↦ add_nonneg
      (mul_nonneg (ite_nonneg (straddleWeight_nonneg _ _) le_rfl)
        (add_nonneg (ite_nonneg zero_le_one le_rfl) (nu45_nonneg _)))
      (mul_nonneg (straddleWeight_nonneg _ _) (ite_nonneg (nu45_nonneg _) le_rfl))
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = m + 1 := ⟨(r - 1).toNat, by omega⟩
  have hcross := hasSum_firstPassageLaw_cross (G := n + 4) (r := m + 1) (by omega) (by omega)
  rw [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; rfl, hcross.tsum_eq]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Nat.add_sub_cancel]
  push_cast at hr
  have hmu : u ≤ |(m : ℝ) - n / 4| := by
    convert hr using 2; ring
  have h1 : ∑ j ∈ range m, (straddleWeight n j - boundaryWeight n j) * nu45 ((m : ℤ) - j) ≤
      ∑ j ∈ range m, straddleWeight n j * nu45 ((m : ℤ) - j) := by
    refine sum_le_sum fun j _ ↦ ?_
    rw [sub_mul]
    exact sub_le_self _ (mul_nonneg (boundaryWeight_nonneg _ _) (nu45_nonneg _))
  have h2 : ∑ j ∈ range m, straddleWeight n j * nu45 ((m : ℤ) - j) =
      ∑ j ∈ range (n + 1), straddleWeight n j * nu45 ((m : ℤ) - j) := by
    rw [sum_subset (range_subset_range.2 (by omega : m ≤ m + n + 1)) fun j _ hj ↦ ?_,
      sum_subset (range_subset_range.2 (by omega : n + 1 ≤ m + n + 1)) fun j _ hj ↦ ?_]
    · simp only [mem_range, not_lt] at hj
      rw [horTail_straddleWeight_eq_zero (by omega), zero_mul]
    · simp only [mem_range, not_lt] at hj
      rw [nu45_of_nonpos (by omega), mul_zero]
  calc _ ≤ _ := add_le_add (horTail_boundaryWeight_le_sum hu hmu)
        (h1.trans (h2.le.trans (sum_le_sum fun j _ ↦ horTail_straddle_nu45_le (j := j) hmu)))
    _ = _ := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun j _ ↦ by ring

/-- For `s = n + 4` with `n ≥ 2` and `u ≥ 2`, the horizontal tail of `F_s` is at most
`4 e^{-u²/(2n)} + (5/4) e^{-u/32}`. -/
theorem tsum_firstPassageLaw_add_four_hor_tail_le {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 2 ≤ u) :
    ∑' r : {r : ℤ // u ≤ |(r : ℝ) - ((n + 4 : ℕ) : ℝ) / 4|},
        ∑' ℓ : ℤ, firstPassageLaw (n + 4 : ℕ) ((r : ℤ), ℓ) ≤
      4 * exp (-(u ^ 2 / (2 * n))) + 5 / 4 * exp (-(u / 32)) := by
  set c1 : ℕ → ℝ := fun j ↦ if u / 2 ≤ |(j : ℝ) - n / 4| then straddleWeight n j else 0
  set δ : ℤ → ℝ := fun h ↦ if h = 0 then 1 else 0
  set νt : ℤ → ℝ := fun h ↦ if u / 2 ≤ (h : ℝ) then nu45 h else 0
  set B : ℤ → ℝ := fun r ↦ ∑ j ∈ range (n + 1),
    (c1 j * (δ (r - 1 - j) + nu45 (r - 1 - j)) + straddleWeight n j * νt (r - 1 - j))
  obtain ⟨hνts, hνtle⟩ := horTail_nu45_tail (u / 2)
  have hc10 : ∀ j, 0 ≤ c1 j := fun j ↦ ite_nonneg (straddleWeight_nonneg _ _) le_rfl
  have hδ0 : ∀ h, 0 ≤ δ h := fun _ ↦ ite_nonneg zero_le_one le_rfl
  have hνt0 : ∀ h, 0 ≤ νt h := fun h ↦ ite_nonneg (nu45_nonneg h) le_rfl
  have hB0 : ∀ r, 0 ≤ B r := fun r ↦ sum_nonneg fun j _ ↦
    add_nonneg (mul_nonneg (hc10 j) (add_nonneg (hδ0 _) (nu45_nonneg _)))
      (mul_nonneg (straddleWeight_nonneg _ _) (hνt0 _))
  have hB : HasSum B (∑ j ∈ range (n + 1),
      (c1 j * (1 + 1) + straddleWeight n j * ∑' h, νt h)) := by
    refine hasSum_sum fun j _ ↦ ?_
    exact ((horTail_hasSum_shift' (hasSum_ite_eq (0 : ℤ) (1 : ℝ) : HasSum δ 1) j).add
      (horTail_hasSum_shift' hasSum_nu45 j)).mul_left _ |>.add
      ((horTail_hasSum_shift' hνts.hasSum j).mul_left _)
  have hpt : ∀ r : {r : ℤ // u ≤ |(r : ℝ) - ((n + 4 : ℕ) : ℝ) / 4|},
      ∑' ℓ : ℤ, firstPassageLaw (n + 4 : ℕ) ((r : ℤ), ℓ) ≤ B r := fun r ↦
    horTail_col_le_of_two_le n hn (by linarith) r.2
  have hn1 : 1 ≤ n := by omega
  have hD : ∑ j ∈ range (n + 1), c1 j ≤ 2 * exp (-(2 * (u / 2) ^ 2 / n)) := by
    refine horTail_sum_straddle_le n hn1 (fun j : ℕ ↦ u / 2 ≤ |(j : ℝ) - n / 4|) (by linarith)
      fun j hj ↦ ?_
    push_cast
    rcases le_abs'.1 hj with ha | ha <;> constructor <;>
      first
      | exact le_abs'.2 (Or.inl (by linarith))
      | exact le_abs'.2 (Or.inr (by linarith))
  have hP : ∑ j ∈ range (n + 1), straddleWeight n j ≤ 1 :=
    (horTail_sum_straddleWeight n).le
  calc ∑' r : {r : ℤ // u ≤ |(r : ℝ) - ((n + 4 : ℕ) : ℝ) / 4|},
        ∑' ℓ : ℤ, firstPassageLaw (n + 4 : ℕ) ((r : ℤ), ℓ)
      ≤ ∑' r : {r : ℤ // u ≤ |(r : ℝ) - ((n + 4 : ℕ) : ℝ) / 4|}, B r :=
        (summable_firstPassageLaw_hor_tail (n + 4) u).tsum_le_tsum hpt
          (hB.summable.comp_injective Subtype.val_injective)
    _ ≤ ∑' r, B r := tsum_comp_le_tsum_of_inj hB.summable hB0 Subtype.val_injective
    _ = 2 * ∑ j ∈ range (n + 1), c1 j +
          (∑' h, νt h) * ∑ j ∈ range (n + 1), straddleWeight n j := by
        rw [hB.tsum_eq, sum_add_distrib, ← sum_mul, ← sum_mul]
        ring
    _ ≤ 2 * (2 * exp (-(2 * (u / 2) ^ 2 / n))) + 5 / 4 * exp (-(u / 2 / 16)) * 1 :=
        add_le_add (by linarith)
          (mul_le_mul hνtle hP (sum_nonneg fun _ _ ↦ straddleWeight_nonneg _ _) (by positivity))
    _ = 4 * exp (-(u ^ 2 / (2 * n))) + 5 / 4 * exp (-(u / 32)) := by
        rw [show 2 * (u / 2) ^ 2 / n = u ^ 2 / (2 * n) by ring, show u / 2 / 16 = u / 32 by ring]
        ring

end CollatzPosDens
