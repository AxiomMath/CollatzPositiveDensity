/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.BlackSet.BkExitWidth
public import CollatzPosDens.Case3.C3CapReward
public import CollatzPosDens.Case3.C3CrossingMass
public import CollatzPosDens.Case3.C3CrossingTransfer
public import CollatzPosDens.Case3.C3H17Angle
public import CollatzPosDens.Case3.C3H17FirstCost
public import CollatzPosDens.Case3.C3H17Tree
public import CollatzPosDens.CharSum.ChOddDyadicExitStrip
public import CollatzPosDens.StoppingTrace.TrCountRaw
public import CollatzPosDens.StoppingTrace.TrGap

/-!
# The paid cost of a first raw crossing set

Let `ξ ∈ G_n` be a unit and `e ∈ 𝒫` black (for `ε_*`) with gap `ω = gap(e) ≥ 224`, let
`Δ = Δ(e)`, and let `M₀` be an integer such that `2^{17}` divides `3^n M₀ + 3^n ϑ(j(e), l_Δ)`.
For integers `2 ≤ c ≤ 16`, `1 ≤ o ≤ c` and `1 ≤ r ≤ ⌊9ω/32⌋`,
```
∑_{π ∈ 𝒞_ω(c,o,r)} bw^⊗(π) exp(-z_* N^*(e, π; |π|))
  ≤ ϖ(c) 𝖱(r - 1, ω + o - c) xc_{c,o}(9^r (M₀ + ϑ(j(e), l_Δ))).
```

Put `x = 9^r (M₀ + ϑ(j(e), l_Δ))`. The count `N^*(e, π; |π|)` is the sum of the paid rewards of
the letters of the raw word `raw(π) = w (c) u`, each read at the point reached after it. Dropping
the rewards of the letters of `w` (they are nonnegative), the letter `c` is read at
`(j(e) + r, l_Δ + o)` and the letters of `u` at the points `(j(e) + r + i, l_Δ + h_i)` with
`h_i = o + u₁ + ⋯ + u_i`. At height at most `17` above the column top, the angle at
`(j(e) + s, l_Δ + h)` is `9^s (M₀ + ϑ(j(e), l_Δ)) / 2^h` up to an integer, and the strip
`j ≤ ⌊n/2⌋` is not left before height `15` is reached, so each paid factor is at most the
capped packet factor at that angle. This bounds the discount of `π` by
`Φ^cap_c(x / 2^o) wt_o(9x; u)`, a function of `raw(π)` alone, and the raw word transfer, the
mass of the crossing sets and the summation of the retained factors over the hold words give
the claim.

## Main results

* `CollatzPosDens.BkBlack.tsum_c3CrossingSet_mul_exp_le_c3H17FirstCost`: the bound above.

## Implementation notes

The gap `ω`, an integer in the source, is a natural number `ω` with `(ω : ℤ) = gap(e)`, as the
crossing set `𝒞_ω(c, o, r)` is indexed by a natural number. The bound `r ≤ ⌊9ω/32⌋` is stated
with the natural-number quotient `9 * ω / 32`, which is that floor. The standing hypothesis of
the source that `ξ` is a unit is an explicit hypothesis. The sum is the unconditional sum of a
summable family of nonnegative reals (it is dominated by the weights `bw^⊗(π)`, of finite total
mass).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The paid rewards along a word `v = (v₁, …, v_K)` read from the point `p`: the sum of
`R_{v_i}(p + (i, v₁ + ⋯ + v_i))` over `1 ≤ i ≤ K`. -/
private noncomputable def rewardAlong (n : ℕ) (ξ : ResidueGroup n) (p : ℤ × ℤ) : List ℤ → ℝ
  | [] => 0
  | d :: v => chPaidReward n ξ (epsStar : ℝ) d (p + (1, d)) + rewardAlong n ξ (p + (1, d)) v

section RewardAlong

variable {n : ℕ} {ξ : ResidueGroup n}

private lemma rewardAlong_nil (p : ℤ × ℤ) : rewardAlong n ξ p [] = 0 := rfl

private lemma rewardAlong_cons (p : ℤ × ℤ) (d : ℤ) (v : List ℤ) :
    rewardAlong n ξ p (d :: v) =
      chPaidReward n ξ (epsStar : ℝ) d (p + (1, d)) + rewardAlong n ξ (p + (1, d)) v := rfl

private lemma rewardAlong_nonneg (p : ℤ × ℤ) (v : List ℤ) : 0 ≤ rewardAlong n ξ p v := by
  induction v generalizing p with
  | nil => exact le_rfl
  | cons d v ih => exact add_nonneg (zero_le_chPaidReward _ _ _ _ _) (ih _)

private lemma rewardAlong_append (p : ℤ × ℤ) (w v : List ℤ) :
    rewardAlong n ξ p (w ++ v) =
      rewardAlong n ξ p w + rewardAlong n ξ (p + ((w.length : ℤ), w.sum)) v := by
  induction w generalizing p with
  | nil =>
    rw [List.nil_append, rewardAlong_nil, zero_add]
    congr 1
    ext <;> simp
  | cons d w ih =>
    rw [List.cons_append, rewardAlong_cons, rewardAlong_cons, ih,
      show p + (1, d) + ((w.length : ℤ), w.sum) = p + (((d :: w).length : ℤ), (d :: w).sum) by
        ext <;> simp <;> ring]
    ring

private lemma sum_range_eq_rewardAlong (p : ℤ × ℤ) (v : List ℤ) :
    ∑ i ∈ Finset.range v.length, chPaidReward n ξ (epsStar : ℝ) (v.getD i 0)
      (p + ((i : ℤ) + 1, (v.take (i + 1)).sum)) = rewardAlong n ξ p v := by
  induction v generalizing p with
  | nil => simp [rewardAlong_nil]
  | cons d v ih =>
    rw [List.length_cons, Finset.sum_range_succ', rewardAlong_cons, ← ih]
    refine (add_comm _ _).trans (congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun i _ => ?_))
    · simp
    · rw [List.getD_cons_succ, List.take_succ_cons, List.sum_cons]
      congr 1
      ext <;> simp <;> ring

/-- The weighted white count of all blocks of `π` is the sum of the paid rewards along the raw
word `raw(π)`. -/
private lemma trCount_eq_rewardAlong (o : ℤ × ℤ) (π : List (List ℤ × ℤ)) :
    trCount n ξ o π π.length = rewardAlong n ξ o (c3RawWord π) := by
  rw [trCount_eq_sum_flatMap, c3RawWord_eq_flatMap, sum_range_eq_rewardAlong]

/-- The downward induction on the suffix word: if every paid factor read at height `0 ≤ k ≤ 17`
above `q`, within `N` steps of `q`, is at most the capped factor at `9^s X / 2^k`, then the paid
factors along a word of letters `≥ 2` read from height `h ≥ 1` are at most the retained factors
`wt_h(9^{s+1} X; u)`. -/
private lemma exp_neg_rewardAlong_le_c3H17Weight (q : ℤ × ℤ) (X : ℝ) (N : ℕ)
    (hstep : ∀ (s : ℕ) (d k : ℤ), s ≤ N → 0 ≤ k → k ≤ 17 →
      Real.exp (-(zStar : ℝ) * chPaidReward n ξ (epsStar : ℝ) d (q + ((s : ℤ), k))) ≤
        trCapFactor d (9 ^ s * X / (2 : ℝ) ^ k)) :
    ∀ u : List ℤ, (∀ d ∈ u, 2 ≤ d) → ∀ (s : ℕ) (h : ℤ), 1 ≤ h → 2 * (s : ℤ) + 15 ≤ 2 * N + h →
      Real.exp (-(zStar : ℝ) * rewardAlong n ξ (q + ((s : ℤ), h)) u) ≤
        c3H17Weight h (9 ^ (s + 1) * X) u := by
  have hz : (0 : ℝ) ≤ zStar := by exact_mod_cast zStar_nonneg
  intro u
  induction u with
  | nil => intro _ s h _ _; simp [rewardAlong_nil]
  | cons d u ih =>
    intro hu s h h1 hinv
    have hd : 2 ≤ d := hu d List.mem_cons_self
    have hu' : ∀ x ∈ u, 2 ≤ x := fun x hx => hu x (List.mem_cons_of_mem _ hx)
    rcases le_or_gt 15 h with hh | hh
    · rw [c3H17Weight_of_le hh, Real.exp_le_one_iff]
      nlinarith [rewardAlong_nonneg (n := n) (ξ := ξ) (q + ((s : ℤ), h)) (d :: u)]
    rw [c3H17Weight_cons_of_lt hh, rewardAlong_cons]
    have hpt : q + ((s : ℤ), h) + (1, d) = q + (((s + 1 : ℕ) : ℤ), h + d) := by
      ext <;> simp <;> ring
    rw [hpt, mul_add, Real.exp_add]
    have hsN : s + 1 ≤ N := by omega
    refine mul_le_mul ?_ ?_ (Real.exp_pos _).le ?_
    · split_ifs
      · exact hstep (s + 1) d (h + d) hsN (by omega) (by omega)
      · rw [Real.exp_le_one_iff]
        nlinarith [zero_le_chPaidReward n ξ (epsStar : ℝ) d (q + (((s + 1 : ℕ) : ℤ), h + d))]
    · split_ifs
      · have := ih hu' (s + 1) (h + d) (by omega) (by push_cast; omega)
        rwa [show (9 : ℝ) ^ (s + 1 + 1) * X = 9 * (9 ^ (s + 1) * X) by ring] at this
      · rw [Real.exp_le_one_iff]
        nlinarith [rewardAlong_nonneg (n := n) (ξ := ξ) (q + (((s + 1 : ℕ) : ℤ), h + d)) u]
    · split_ifs
      · exact (trCapFactor_pos _ _).le
      · exact zero_le_one

end RewardAlong

private lemma prod_map_varpi_nonneg' (w : List ℤ) : 0 ≤ (w.map varpi).prod :=
  List.prod_nonneg fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact varpi_nonneg y

/-- **The paid cost of a first raw crossing set.** Let `ξ` be a unit, `e ∈ 𝒫` black (for `ε_*`)
with gap `ω = gap(e) ≥ 224`, `Δ = Δ(e)`, and `M₀` an integer such that `2^{17}` divides
`3^n M₀ + 3^n ϑ(j(e), l_Δ)`. For integers `2 ≤ c ≤ 16`, `1 ≤ o ≤ c` and `1 ≤ r ≤ ⌊9ω/32⌋`,
`∑_{π ∈ 𝒞_ω(c,o,r)} bw^⊗(π) exp(-z_* N^*(e, π; |π|)) ≤
ϖ(c) 𝖱(r - 1, ω + o - c) xc_{c,o}(9^r (M₀ + ϑ(j(e), l_Δ)))`. -/
@[collatz_pos_dens "lem_c3_h17_crossing_cost"]
theorem BkBlack.tsum_c3CrossingSet_mul_exp_le_c3H17FirstCost {n : ℕ} {ξ : ResidueGroup n}
    {e : ℤ × ℤ} (hb : BkBlack n ξ (epsStar : ℝ) e) (hξ : IsResidueUnit ξ) (he : e ∈ bkPoints)
    {ω : ℕ} (hω : (ω : ℤ) = trGap n ξ (epsStar : ℝ) e) (hω224 : 224 ≤ ω) (M₀ : ℤ)
    (hdvd : ∃ k : ℤ, (3 : ℝ) ^ n * M₀ +
      3 ^ n * bkTheta n ξ (bkJ e, (bkCanonTriangle n ξ (epsStar : ℝ) e he).l) = 2 ^ 17 * k)
    {c o : ℤ} {r : ℕ} (hc : 2 ≤ c) (hc16 : c ≤ 16) (ho : 1 ≤ o) (hoc : o ≤ c) (hr : 1 ≤ r)
    (hrω : r ≤ 9 * ω / 32) :
    ∑' π : c3CrossingSet ω c o r,
        trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length) ≤
      varpi c * rawMass (r - 1) (ω + o - c) *
        c3H17FirstCost c o
          (9 ^ r * (M₀ + bkTheta n ξ (bkJ e, (bkCanonTriangle n ξ (epsStar : ℝ) e he).l))) := by
  obtain ⟨lΔ, hlΔ⟩ : ∃ l, l = (bkCanonTriangle n ξ (epsStar : ℝ) e he).l := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = M₀ + bkTheta n ξ (bkJ e, lΔ) := ⟨_, rfl⟩
  rw [← hlΔ] at hdvd ⊢
  rw [← hX]
  have hz : (0 : ℝ) ≤ zStar := by exact_mod_cast zStar_nonneg
  have hωl : bkL e + ω = (bkCanonTriangle n ξ (epsStar : ℝ) e he).l := by
    rw [bkCanonTriangle_l, bkColTop_eq_add_trGap, ← hω]
  -- The horizon: the strip `j ≤ ⌊n/2⌋` contains the points up to `r + 7` columns right of `e`.
  have hJ : ∀ s : ℕ, s ≤ r + 7 → bkJ e + s ≤ ((n / 2 : ℕ) : ℤ) := fun s hs =>
    bkJ_add_le_of_le_bkExitWidth hξ epsStar_mem_bkRange.1 epsStar_mem_bkRange.2 he hb hωl
      (by rw [bkExitWidth_def]; omega)
  -- One paid factor at height at most `17` above the column top.
  have hstep : ∀ (s : ℕ) (d k : ℤ), s ≤ r + 7 → 0 ≤ k → k ≤ 17 →
      Real.exp (-(zStar : ℝ) * chPaidReward n ξ (epsStar : ℝ) d ((bkJ e, lΔ) + ((s : ℤ), k))) ≤
        trCapFactor d (9 ^ s * X / (2 : ℝ) ^ k) := by
    intro s d k hs hk0 hk17
    obtain ⟨m, hm⟩ := hb.exists_c3H17Angle_sub_eq_intCast he M₀ (hlΔ ▸ hdvd) s k.toNat
      (by omega)
    rw [← hlΔ, ← hX, Int.toNat_of_nonneg hk0] at hm
    have hpt : (bkJ e, lΔ) + ((s : ℤ), k) = (bkJ e + s, lΔ + k) := rfl
    rw [hpt]
    refine (exp_neg_zStar_mul_chPaidReward_le_trCapFactor (by simpa using hJ s hs)).trans_eq ?_
    -- `Φ^cap_d` has period `1`, all frequencies of the packet function being integers
    rw [eq_add_of_sub_eq hm, add_comm, ← zpow_natCast (2 : ℝ) k.toNat, Int.toNat_of_nonneg hk0]
    unfold trCapFactor
    rw [chPacketFn_add_intCast]
  -- The discount of a word `w (c) u` of the crossing set.
  have hword : ∀ w : List ℤ, w.length = r - 1 → w.sum = ω + o - c →
      ∀ u ∈ c3SuffixWords c,
        Real.exp (-(zStar : ℝ) * rewardAlong n ξ e (w ++ c :: u)) ≤
          trCapFactor c (9 ^ r * X / (2 : ℝ) ^ o) * c3H17Weight o (9 * (9 ^ r * X)) u := by
    intro w hwl hws u hu
    rw [rewardAlong_append, rewardAlong_cons, hwl, hws]
    have hpt : e + (((r - 1 : ℕ) : ℤ), (ω : ℤ) + o - c) + (1, c) =
        (bkJ e, lΔ) + ((r : ℤ), o) := by
      rw [hlΔ, ← hωl]
      ext
      · simp only [Prod.fst_add]
        push_cast [Nat.cast_sub hr]
        ring
      · simp only [Prod.snd_add, bkL]
        ring
    rw [hpt]
    have hA := hstep r c o (by omega) (by omega) (by omega)
    have hW := exp_neg_rewardAlong_le_c3H17Weight (bkJ e, lΔ) X (r + 7) hstep u
      (two_le_of_mem_c3SuffixWords hu) r o ho (by push_cast; omega)
    rw [show (9 : ℝ) ^ (r + 1) * X = 9 * (9 ^ r * X) by ring] at hW
    calc Real.exp (-(zStar : ℝ) * (rewardAlong n ξ e w +
          (chPaidReward n ξ (epsStar : ℝ) c ((bkJ e, lΔ) + ((r : ℤ), o)) +
            rewardAlong n ξ ((bkJ e, lΔ) + ((r : ℤ), o)) u)))
        ≤ Real.exp (-(zStar : ℝ) * (chPaidReward n ξ (epsStar : ℝ) c ((bkJ e, lΔ) + ((r : ℤ), o)) +
            rewardAlong n ξ ((bkJ e, lΔ) + ((r : ℤ), o)) u)) :=
          Real.exp_le_exp.2 (by nlinarith [rewardAlong_nonneg (n := n) (ξ := ξ) e w])
      _ = Real.exp (-(zStar : ℝ) *
            chPaidReward n ξ (epsStar : ℝ) c ((bkJ e, lΔ) + ((r : ℤ), o))) *
          Real.exp (-(zStar : ℝ) * rewardAlong n ξ ((bkJ e, lΔ) + ((r : ℤ), o)) u) := by
          rw [mul_add, Real.exp_add]
      _ ≤ _ := mul_le_mul hA hW (Real.exp_pos _).le (trCapFactor_pos _ _).le
  -- The sum over the suffix words.
  set A := trCapFactor c (9 ^ r * X / (2 : ℝ) ^ o) with hA
  have hnnU : ∀ u : List ℤ, 0 ≤ A * ((u.map varpi).prod * c3H17Weight o (9 * (9 ^ r * X)) u) :=
    fun u => mul_nonneg (trCapFactor_pos _ _).le
      (mul_nonneg (prod_map_varpi_nonneg' u) (c3H17Weight_nonneg _ _ _))
  have hsuff : (∑' u : c3SuffixWords c, ENNReal.ofReal (u.1.map varpi).prod = 1) ∧
      (∑' u : c3SuffixWords c,
          ENNReal.ofReal (A * ((u.1.map varpi).prod * c3H17Weight o (9 * (9 ^ r * X)) u.1)) =
        ENNReal.ofReal (c3H17FirstCost c o (9 ^ r * X))) ∧
      0 ≤ c3H17FirstCost c o (9 ^ r * X) := by
    by_cases hc45 : c = 4 ∨ c = 5
    · rw [c3SuffixWords_of_mem (by simpa using hc45), c3H17FirstCost_of_mem (by simpa using hc45)]
      rw [tsum_singleton ([] : List ℤ) (fun u => ENNReal.ofReal (u.map varpi).prod),
        tsum_singleton ([] : List ℤ) (fun u => ENNReal.ofReal
          (A * ((u.map varpi).prod * c3H17Weight o (9 * (9 ^ r * X)) u)))]
      refine ⟨by simp, by simp [hA], (trCapFactor_pos _ _).le⟩
    · have hS : c3SuffixWords c = c3SuffixWords 2 := by
        rw [c3SuffixWords_of_notMem (by simpa using hc45),
          c3SuffixWords_of_notMem (by norm_num)]
      have hT := (hasSum_c3H17Weight o (9 * (9 ^ r * X))).mul_left A
      rw [hS, c3H17FirstCost_of_not_mem (by simpa using hc45)]
      refine ⟨?_, ?_, ?_⟩
      · rw [← ENNReal.ofReal_tsum_of_nonneg (fun u => prod_map_varpi_nonneg' _)
          hasSum_prod_varpi_c3SuffixWords_two.summable,
          hasSum_prod_varpi_c3SuffixWords_two.tsum_eq, ENNReal.ofReal_one]
      · rw [← ENNReal.ofReal_tsum_of_nonneg (fun u => hnnU _) hT.summable, hT.tsum_eq]
      · exact hT.nonneg fun u => hnnU _
  obtain ⟨hU1, hU, hxc⟩ := hsuff
  -- The sum over the prefix words, from the mass of the crossing set.
  have hmass := hasSum_trListWeight_c3CrossingSet ω ho hoc hr
  have hWsum : ENNReal.ofReal (varpi c) *
      ∑' w : {w : List ℤ // w.length = r - 1 ∧ (∀ x ∈ w, 2 ≤ x) ∧ w.sum = ω + o - c},
        ENNReal.ofReal (w.1.map varpi).prod =
      ENNReal.ofReal (varpi c * rawMass (r - 1) (ω + o - c)) := by
    have h1 := tsum_c3CrossingSet_mul_eq ω hc ho hoc hr (fun _ => 1)
    simp only [mul_one] at h1
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun π => trListWeight_nonneg _) hmass.summable,
      hmass.tsum_eq] at h1
    simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hU1, mul_one] at h1
    exact h1.symm
  -- Summability and the passage to `[0, ∞]`.
  have hnn : ∀ π : c3CrossingSet ω c o r,
      0 ≤ trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length) :=
    fun π => mul_nonneg (trListWeight_nonneg _) (Real.exp_pos _).le
  have hsum : Summable fun π : c3CrossingSet ω c o r =>
      trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length) :=
    hmass.summable.of_nonneg_of_le hnn fun π => mul_le_of_le_one_right (trListWeight_nonneg _)
      (Real.exp_le_one_iff.2 (by nlinarith [trCount_nonneg (n := n) (ξ := ξ) e π.1 π.1.length]))
  have hRHS : 0 ≤ varpi c * rawMass (r - 1) (ω + o - c) * c3H17FirstCost c o (9 ^ r * X) :=
    mul_nonneg (mul_nonneg (varpi_nonneg c) (rawMass_nonneg _ _)) hxc
  rw [← ENNReal.ofReal_le_ofReal_iff hRHS, ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  let Ψ : List ℤ → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (-(zStar : ℝ) * rewardAlong n ξ e v))
  have hΨ : ∀ π : c3CrossingSet ω c o r,
      ENNReal.ofReal (trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length)) =
        ENNReal.ofReal (trListWeight π.1) * Ψ (c3RawWord π.1) := by
    intro π
    rw [ENNReal.ofReal_mul (trListWeight_nonneg _), trCount_eq_rewardAlong]
  rw [tsum_congr hΨ, tsum_c3CrossingSet_mul_eq ω hc ho hoc hr]
  calc ENNReal.ofReal (varpi c) *
        ∑' w : {w : List ℤ // w.length = r - 1 ∧ (∀ x ∈ w, 2 ≤ x) ∧ w.sum = ω + o - c},
          ∑' u : c3SuffixWords c, ENNReal.ofReal (w.1.map varpi).prod *
            ENNReal.ofReal (u.1.map varpi).prod * Ψ (w.1 ++ c :: u.1)
      ≤ ENNReal.ofReal (varpi c) *
        ∑' w : {w : List ℤ // w.length = r - 1 ∧ (∀ x ∈ w, 2 ≤ x) ∧ w.sum = ω + o - c},
          ∑' u : c3SuffixWords c, ENNReal.ofReal (w.1.map varpi).prod *
            ENNReal.ofReal (A * ((u.1.map varpi).prod *
              c3H17Weight o (9 * (9 ^ r * X)) u.1)) := by
        refine mul_le_mul_right (ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun u => ?_) _
        rw [mul_assoc]
        refine mul_le_mul_right ?_ _
        rw [show A * ((u.1.map varpi).prod * c3H17Weight o (9 * (9 ^ r * X)) u.1) =
          (u.1.map varpi).prod * (A * c3H17Weight o (9 * (9 ^ r * X)) u.1) by ring,
          ENNReal.ofReal_mul (prod_map_varpi_nonneg' _)]
        refine mul_le_mul_right ?_ _
        exact ENNReal.ofReal_le_ofReal (hword w.1 w.2.1 w.2.2.2 u.1 u.2)
    _ = ENNReal.ofReal (varpi c) *
        ∑' w : {w : List ℤ // w.length = r - 1 ∧ (∀ x ∈ w, 2 ≤ x) ∧ w.sum = ω + o - c},
          ENNReal.ofReal (w.1.map varpi).prod *
            ENNReal.ofReal (c3H17FirstCost c o (9 ^ r * X)) := by
        simp_rw [ENNReal.tsum_mul_left, hU]
    _ = _ := by
        rw [ENNReal.tsum_mul_right, ← mul_assoc, hWsum, ← ENNReal.ofReal_mul
          (mul_nonneg (varpi_nonneg c) (rawMass_nonneg _ _))]

end CollatzPosDens
