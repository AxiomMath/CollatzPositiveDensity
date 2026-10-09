/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQContinuation
public import CollatzPosDens.CharSum.ChQRange
public import CollatzPosDens.CharSum.ChQStopped
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.StoppingTrace.TrConcat
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrListSplit
public import CollatzPosDens.StoppingTrace.TrPrefixFreeMass
public import CollatzPosDens.StoppingTrace.TrWhiteCount

/-!
# Continuation through the first passage

Fix `n : ℕ`, `J = ⌊n/2⌋` and `ξ : ResidueGroup n`, and take whiteness with respect to
`(n, ξ, ε_*)`, where `ε_* = epsStar`. For a point `e ∈ 𝒫 = bkPoints`, a level `g ∈ ℕ` and a
horizon `P ≤ J`, the renewal function `Q = chQ n ξ ε_*` satisfies
`Q(e) ≤ ∑_a μ_{e,g}(a) e^{-z_* N^e_{P-1}(a)} Q(y^e_P(a))`, with `z_* = zStar`. The sum runs over
the atoms `a = ((r, ℓ), β) ∈ trAtoms n` of the fresh law `μ_{e,g} = trFreshLaw n e g`, the weighted
white count is `N^e_{P-1} = trWhiteCount n ξ e · (P - 1)`, and `y^e_P = trFreshPath e · P` is the
fresh path.

The stopped inequality gives `Q(e) ≤ ∑_x F_g(x) Q(e + x)`. For each `x`, put `o = e + x`; the
continuation identity with `P` blocks expands `Q(o)` over `γ ∈ 𝔅^P`. Dropping the factors
`w(q_0) ≤ 1` and `I(q_{P-1}; γ^P) ≤ 1` and grouping the rest by blocks, using
`w(q + bpt(b)) I(q; b) = e^{-z_* rw(q, b)}`, bounds the term of `γ` by
`bw^⊗(γ) e^{-z_* N^*(o, γ; P-1)} Q(x_P(o, γ))`. These quantities only depend on the first `P`
blocks of a list, and the remaining `J - P` blocks carry total weight `1`, so the sum may be
taken over `𝔅^J` instead. Multiplying by `F_g(x)` and summing over `x` gives the claim.

## Main results

* `CollatzPosDens.chQ_le_tsum_trFreshLaw_mul_exp`: the continuation inequality.

## Implementation notes

The reference assumes `1 ≤ P ≤ J`; the inequality holds for every `P ≤ J` and is stated so (for
`P = 0` it is the stopped inequality, with `N^e_{0 - 1} = N^e_0 = 0` in `ℕ`). The renewal function
`Q` is taken at the threshold `ε_*`, the one to which whiteness in the white count refers.
The sum over the atoms is a `tsum` over the subtype `𝒜_n = trAtoms n`; its terms are shown to be
summable, so the `tsum` is a genuine sum. The intermediate regrouping of the series is carried
out in `[0, ∞]`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.4.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- For a block `b` and a point `q`, `w(q + bpt(b)) I(q; b) = e^{-z_* rw(q, b)}`, whiteness
referring to `(n, ξ, ε_*)`. -/
private theorem chWhiteFactor_mul_chInternalWeight (n : ℕ) (ξ : ResidueGroup n) (q : ℤ × ℤ)
    (b : List ℤ × ℤ) :
    chWhiteFactor n ξ (epsStar : ℝ) (q + chBlockPoint b) *
        chInternalWeight n ξ (epsStar : ℝ) q b =
      Real.exp (-((zStar : ℝ) * trReward n ξ q b)) := by
  classical
  set m := b.1.length
  set p : ℕ → Prop := fun i => b.1.getD i 0 = 3 ∧
    IsBkWhite n ξ (epsStar : ℝ) (q + ((i : ℤ) + 1, (b.1.take (i + 1)).sum)) with hp
  have hI : chInternalWeight n ξ (epsStar : ℝ) q b =
      Real.exp (-((kappaStar : ℝ) * zStar)) ^ ((Finset.range m).filter p).card := by
    rw [chInternalWeight_eq_prod_ite]
    have h : (∏ i : Fin m, if b.1[i] = 3 then
        chRaw3Factor n ξ (epsStar : ℝ) (q + ((i : ℤ) + 1, (b.1.take (i + 1)).sum)) else 1) =
        ∏ i ∈ Finset.range m, if b.1.getD i 0 = 3 then
          chRaw3Factor n ξ (epsStar : ℝ) (q + ((i : ℤ) + 1, (b.1.take (i + 1)).sum)) else 1 := by
      rw [Finset.prod_range]
      exact Finset.prod_congr rfl fun i _ => by simp [m]
    rw [h, ← Finset.prod_const, Finset.prod_filter]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [chRaw3Factor]
    split_ifs <;> simp_all
  have hcard : ((Finset.Icc 1 m).filter fun i =>
      b.1.getD (i - 1) 0 = 3 ∧
        IsBkWhite n ξ (epsStar : ℝ) (q + ((i : ℤ), (b.1.take i).sum))).card =
      ((Finset.range m).filter p).card := by
    refine Finset.card_nbij' (· - 1) (· + 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, hp]
      refine ⟨by omega, hi.2.1, ?_⟩
      have h1 : i - 1 + 1 = i := by omega
      have h2 : ((i - 1 : ℕ) : ℤ) + 1 = (i : ℤ) := by omega
      rw [h1, h2]
      exact hi.2.2
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, hp] at hi
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
      refine ⟨by omega, by simpa using hi.2.1, ?_⟩
      push_cast
      exact hi.2.2
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hi
      change i - 1 + 1 = i
      omega
    · intro i _
      simp
  rw [hI, trReward_def, hcard, ← Real.exp_nat_mul, chWhiteFactor]
  split_ifs
  · rw [← Real.exp_add]
    congr 1
    ring
  · rw [one_mul]
    congr 1
    ring

/-- Along a list `L` of `P` blocks from `o`, with `q_i = o + Bp_i(L)`,
`∏_{i<P} w(q_i) ∏_{k<P} I(q_k; Lᵏ⁺¹) ≤ e^{-z_* N^*(o, L; P - 1)}`. -/
private theorem prod_chWhiteFactor_mul_prod_chInternalWeight_le (n : ℕ) (ξ : ResidueGroup n)
    (o : ℤ × ℤ) (L : List (List ℤ × ℤ)) :
    (∏ i ∈ Finset.range L.length, chWhiteFactor n ξ (epsStar : ℝ) (o + chBlockPath L i)) *
        (∏ k ∈ Finset.range L.length,
          chInternalWeight n ξ (epsStar : ℝ) (o + chBlockPath L k) (L.getD k ([], 0))) ≤
      Real.exp (-((zStar : ℝ) * trCount n ξ o L (L.length - 1))) := by
  rcases hL : L.length with _ | m
  · simp
  have hw : ∀ i, 0 ≤ chWhiteFactor n ξ (epsStar : ℝ) (o + chBlockPath L i) := fun _ ↦
    chWhiteFactor_nonneg _ _ _ _
  have hI : ∀ k, 0 ≤ chInternalWeight n ξ (epsStar : ℝ) (o + chBlockPath L k)
      (L.getD k ([], 0)) := fun _ ↦ chInternalWeight_nonneg _ _ _ _ _
  rw [Finset.prod_range_succ', Finset.prod_range_succ]
  calc _ ≤ (∏ i ∈ Finset.range m, chWhiteFactor n ξ (epsStar : ℝ) (o + chBlockPath L (i + 1))) *
        ∏ k ∈ Finset.range m,
          chInternalWeight n ξ (epsStar : ℝ) (o + chBlockPath L k) (L.getD k ([], 0)) :=
        mul_le_mul (mul_le_of_le_one_right (Finset.prod_nonneg fun _ _ ↦ hw _)
            (chWhiteFactor_le_one _ _ _ _))
          (mul_le_of_le_one_right (Finset.prod_nonneg fun _ _ ↦ hI _)
            (chInternalWeight_le_one _ _ _ _ _))
          (mul_nonneg (Finset.prod_nonneg fun _ _ ↦ hI _) (hI _))
          (Finset.prod_nonneg fun _ _ ↦ hw _)
    _ = ∏ k ∈ Finset.range m, Real.exp (-((zStar : ℝ) *
          trReward n ξ (trPath o L k) (L.getD k ([], 0)))) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k hk ↦ ?_
        have hk : k < L.length := by rw [Finset.mem_range] at hk; omega
        rw [chBlockPath_succ L hk, ← add_assoc, trPath_eq_add_chBlockPath,
          List.getD_eq_getElem _ _ hk]
        exact chWhiteFactor_mul_chInternalWeight n ξ _ _
    _ = _ := by
        rw [← Real.exp_sum, trCount_def, hL, Nat.add_sub_cancel,
          min_eq_left (Nat.le_succ m), Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- The continuation inequality from a base point `o` with `0 ≤ j(o)`, summed over `𝔅^J`,
`J ≥ P`, as a sum in `[0, ∞]`. -/
private theorem ofReal_chQ_le_tsum_trListWeight (n : ℕ) (ξ : ResidueGroup n) {o : ℤ × ℤ}
    (ho : 0 ≤ bkJ o) {P J : ℕ} (hPJ : P ≤ J) :
    ENNReal.ofReal (chQ n ξ (epsStar : ℝ) o) ≤
      ∑' β : {β : List (List ℤ × ℤ) //
          β.length = J ∧ ∀ x ∈ β, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
        ENNReal.ofReal (trListWeight β.1) *
          ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trCount n ξ o β.1 (P - 1))) *
            chQ n ξ (epsStar : ℝ) (trPath o β.1 P)) := by
  set Φ : List (List ℤ × ℤ) → ℝ := fun L ↦
    Real.exp (-((zStar : ℝ) * trCount n ξ o L (P - 1))) * chQ n ξ (epsStar : ℝ) (trPath o L P)
    with hΦ
  have hΦ0 : ∀ L, 0 ≤ Φ L := fun L ↦ mul_nonneg (Real.exp_pos _).le (chQ_nonneg _ _ _ _)
  have hΦ1 : ∀ L, Φ L ≤ 1 := fun L ↦ by
    refine (mul_le_of_le_one_left (chQ_nonneg _ _ _ _) ?_).trans (chQ_le_one _ _ _ _)
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (by exact_mod_cast zStar_nonneg) (trCount_nonneg _ _ _)
  have hΦapp : ∀ u f : List (List ℤ × ℤ), u.length = P → Φ (u ++ f) = Φ u := by
    intro u f hu
    simp only [hΦ]
    rw [trCount_append_of_le o u f (by omega), trPath_concat o u f hu.ge]
  set T : (Fin P → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) → ℝ := fun β ↦
    (∏ k, chBlockWeight (β k)) *
      (∏ i ∈ Finset.range P,
        chWhiteFactor n ξ (epsStar : ℝ) (o + chBlockPath (List.ofFn fun k ↦ (β k).1) i)) *
      (∏ k : Fin P, chInternalWeight n ξ (epsStar : ℝ)
        (o + chBlockPath (List.ofFn fun k ↦ (β k).1) k) (β k)) *
      chQ n ξ (epsStar : ℝ) (o + chBlockPath (List.ofFn fun k ↦ (β k).1) P) with hT
  have hT0 : ∀ β, 0 ≤ T β := fun β ↦
    mul_nonneg (mul_nonneg (mul_nonneg (prod_chBlockWeight_nonneg β)
      (Finset.prod_nonneg fun _ _ ↦ chWhiteFactor_nonneg _ _ _ _))
      (Finset.prod_nonneg fun _ _ ↦ chInternalWeight_nonneg _ _ _ _ _)) (chQ_nonneg _ _ _ _)
  have hTle : ∀ β, T β ≤ (∏ k, chBlockWeight (β k)) * Φ (List.ofFn fun k ↦ (β k).1) := by
    intro β
    set L := List.ofFn fun k ↦ (β k).1 with hL
    have hlen : L.length = P := List.length_ofFn
    have hI : (∏ k : Fin P, chInternalWeight n ξ (epsStar : ℝ) (o + chBlockPath L k) (β k)) =
        ∏ k ∈ Finset.range L.length,
          chInternalWeight n ξ (epsStar : ℝ) (o + chBlockPath L k) (L.getD k ([], 0)) := by
      rw [hlen, Finset.prod_range]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2)]
      simp [hL]
    have key := prod_chWhiteFactor_mul_prod_chInternalWeight_le n ξ o L
    rw [← hI, hlen] at key
    simp only [hT, hΦ]
    rw [← trPath_eq_add_chBlockPath, ← hL, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (prod_chBlockWeight_nonneg β)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right key (chQ_nonneg _ _ _ _)
  have hTS : Summable T := Summable.of_nonneg_of_le hT0
    (fun β ↦ (hTle β).trans (mul_le_of_le_one_right (prod_chBlockWeight_nonneg β) (hΦ1 _)))
    (hasSum_prod_chBlockWeight P).summable
  rw [chQ_eq_tsum_blockPath_of_nonneg n ξ _ P ho, ENNReal.ofReal_tsum_of_nonneg hT0 hTS]
  refine (ENNReal.tsum_le_tsum fun β ↦ (ENNReal.ofReal_le_ofReal (hTle β)).trans_eq
    (ENNReal.ofReal_mul (prod_chBlockWeight_nonneg β))).trans (le_of_eq ?_)
  rw [← (blockListEquivFin P).tsum_eq]
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hPJ
  have hstep : ∀ β : {β : List (List ℤ × ℤ) //
      β.length = P + b ∧ ∀ x ∈ β, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
      ENNReal.ofReal (Φ β.1) = ENNReal.ofReal (Φ (trSublist β.1 1 P)) := by
    intro β
    rw [trSublist_one]
    conv_lhs => rw [← List.take_append_drop P β.1]
    rw [hΦapp _ _ (by rw [List.length_take, β.2.1]; omega)]
  change _ = ∑' β : {β : List (List ℤ × ℤ) //
      β.length = P + b ∧ ∀ x ∈ β, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
    ENNReal.ofReal (trListWeight β.1) * ENNReal.ofReal (Φ β.1)
  simp_rw [hstep]
  rw [tsum_trListWeight_trSublist {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)} P b
    (fun u _ ↦ ENNReal.ofReal (Φ u))]
  refine tsum_congr fun u ↦ ?_
  simp_rw [mul_right_comm _ _ (ENNReal.ofReal (Φ u.1))]
  rw [ENNReal.tsum_mul_left, tsum_ofReal_trListWeight_length_eq, mul_one]
  obtain ⟨u, hu, hu'⟩ := u
  subst hu
  congr 2
  · simp only [blockListEquivFin, Equiv.coe_fn_mk, trListWeight_eq_prod_fin]
    rfl
  · simp only [blockListEquivFin, Equiv.coe_fn_mk]
    exact congrArg Φ (List.ofFn_getElem)

/-- **Continuation through the first passage.** For `e ∈ 𝒫`, `g ∈ ℕ` and `P ≤ J = ⌊n/2⌋`,
`Q(e) ≤ ∑_a μ_{e,g}(a) e^{-z_* N^e_{P-1}(a)} Q(y^e_P(a))`, the sum running over the atoms
`a ∈ 𝒜_n` of the fresh law, with `Q` and whiteness taken at the threshold `ε_*`. -/
@[collatz_pos_dens "lem_c3_continuation"]
theorem chQ_le_tsum_trFreshLaw_mul_exp (n : ℕ) (ξ : ResidueGroup n) {e : ℤ × ℤ}
    (he : e ∈ bkPoints) (g : ℕ) {P : ℕ} (hP : P ≤ n / 2) :
    chQ n ξ (epsStar : ℝ) e ≤
      ∑' a : trAtoms n, trFreshLaw n e g a *
        Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (P - 1))) *
        chQ n ξ (epsStar : ℝ) (trFreshPath e a P) := by
  set T : trAtoms n → ℝ := fun a ↦ trFreshLaw n e g a *
    Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (P - 1))) *
    chQ n ξ (epsStar : ℝ) (trFreshPath e a P) with hT
  have hT0 : ∀ a, 0 ≤ T a := fun a ↦ mul_nonneg (mul_nonneg (trFreshLaw_nonneg _ _ _ _)
    (Real.exp_pos _).le) (chQ_nonneg _ _ _ _)
  set o : ℕ × ℤ → ℤ × ℤ := fun x ↦ (bkJ e + x.1, bkL e + x.2) with ho
  set Φ : ℕ × ℤ → List (List ℤ × ℤ) → ℝ := fun x L ↦
    Real.exp (-((zStar : ℝ) * trCount n ξ (o x) L (P - 1))) *
      chQ n ξ (epsStar : ℝ) (trPath (o x) L P) with hΦ
  set S : ℝ≥0∞ := ∑' x : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw g ((x.1 : ℤ), x.2)) *
    ∑' β : {β : List (List ℤ × ℤ) //
        β.length = n / 2 ∧ ∀ x ∈ β, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
      ENNReal.ofReal (trListWeight β.1) * ENNReal.ofReal (Φ x β.1) with hS
  have hsplit : ∑' a, ENNReal.ofReal (T a) = S := by
    rw [← (trAtomsEquiv n).symm.tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun x ↦ ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun β ↦ ?_
    simp only [hT, trAtomsEquiv, Equiv.coe_fn_symm_mk, trFreshLaw_def, hΦ, ho]
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (firstPassageLaw_nonneg _ _)
        (trListWeight_nonneg _)) (Real.exp_pos _).le),
      ENNReal.ofReal_mul (mul_nonneg (firstPassageLaw_nonneg _ _) (trListWeight_nonneg _)),
      ENNReal.ofReal_mul (firstPassageLaw_nonneg _ _),
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp only [trWhiteCount_def, trFreshPath]
    ring
  have hlow : ENNReal.ofReal (chQ n ξ (epsStar : ℝ) e) ≤ S := by
    have hnn : ∀ x : ℕ × ℤ, 0 ≤ firstPassageLaw g ((x.1 : ℤ), x.2) *
        chQ n ξ (epsStar : ℝ) (e + ((x.1 : ℤ), x.2)) := fun x ↦
      mul_nonneg (firstPassageLaw_nonneg _ _) (chQ_nonneg _ _ _ _)
    have hsum : Summable fun x : ℕ × ℤ ↦ firstPassageLaw g ((x.1 : ℤ), x.2) *
        chQ n ξ (epsStar : ℝ) (e + ((x.1 : ℤ), x.2)) :=
      Summable.of_nonneg_of_le hnn
        (fun x ↦ mul_le_of_le_one_right (firstPassageLaw_nonneg _ _) (chQ_le_one _ _ _ _))
        (summable_firstPassageLaw_natCast g)
    refine (ENNReal.ofReal_le_ofReal (chQ_le_tsum_firstPassageLaw_mul n ξ _ g he)).trans ?_
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum]
    refine ENNReal.tsum_le_tsum fun x ↦ ?_
    rw [ENNReal.ofReal_mul (firstPassageLaw_nonneg _ _)]
    gcongr
    have hox : e + ((x.1 : ℤ), x.2) = o x := rfl
    rw [hox]
    exact ofReal_chQ_le_tsum_trListWeight n ξ
      (by simp only [ho, bkJ]; have := mem_bkPoints.1 he; simp only [bkJ] at this; omega) hP
  have hup : S ≤ ∑' x : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw g ((x.1 : ℤ), x.2)) := by
    refine ENNReal.tsum_le_tsum fun x ↦ mul_le_of_le_one_right' ?_
    refine (ENNReal.tsum_le_tsum fun β ↦ mul_le_of_le_one_right' ?_).trans_eq
      (tsum_ofReal_trListWeight_length_eq _)
    refine ENNReal.ofReal_le_one.2 ?_
    refine (mul_le_of_le_one_left (chQ_nonneg _ _ _ _) ?_).trans (chQ_le_one _ _ _ _)
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (by exact_mod_cast zStar_nonneg) (trCount_nonneg _ _ _)
  have hfin : ∑' a, ENNReal.ofReal (T a) ≠ ⊤ := by
    rw [hsplit]
    refine ne_top_of_le_ne_top ?_ hup
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ firstPassageLaw_nonneg _ _)
      (summable_firstPassageLaw_natCast g)]
    exact ENNReal.ofReal_ne_top
  have hTS : Summable T := by
    have := ENNReal.summable_toReal hfin
    simpa only [ENNReal.toReal_ofReal (hT0 _)] using this
  rw [← ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hT0), ENNReal.ofReal_tsum_of_nonneg hT0 hTS,
    hsplit]
  exact hlow

end CollatzPosDens
