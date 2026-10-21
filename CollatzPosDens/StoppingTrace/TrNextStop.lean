/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.BlackSet.BkColTop
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.RecipeMap
public import CollatzPosDens.Transfer.S02HDef
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.BlackSet.BkSourceMem
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrLive
public import CollatzPosDens.StoppingTrace.TrLow
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrOversizeHit
public import CollatzPosDens.StoppingTrace.TrClear
public import CollatzPosDens.StoppingTrace.TrWhiteCount
public import CollatzPosDens.StoppingTrace.TrCountWhites
public import CollatzPosDens.StoppingTrace.TrPathGrowth
public import CollatzPosDens.StoppingTrace.TrSurvivalDomain

/-!
# The next stop comes on schedule

Let `ι ∈ 𝔍` be a Fourier index, `J = ⌊n/2⌋`, let `ξ ∈ G_n` be a unit, and let black and white
refer to `(n, ξ, ε_*)`. Let `e ∈ 𝒫` and `m ∈ ℕ` with `j(e) + m = J`, assume `P_*(ι) ≤ J`, and let
`a = ((r, ℓ), β) ∈ 𝒜_n` with `β` live and `a ∈ Low^e(ι) \ (Bad^e_m(ι) ∪ Clr(ι))`. Write
`y_t = y^e_t(a)`. If `y_q` is black, `a` has no oversize hit at time `q` for `ι`, and
`𝔤_ι(q) ≤ P_*(ι) - 1`, then some `c` with `q < c ≤ 𝔤_ι(q)` and `c < J` has `y_c` black and
`l(y_c) > l_*(y_q)`.

With `h = h_*(ι, q)`, `β_*(q) = β_*(ι, q)`, `T_* = T_*(ι)`, `P_* = P_*(ι)` and `𝔤 = 𝔤_ι`, the
argument runs in three steps.

* The canonical triangle `Δ = Δ(y_q)` of the family `𝔗_{n,ξ,ε_*}` contains `y_q` and has corner
  height `l_Δ = l_*(y_q)`. As `a` has no oversize hit at time `q`, its size is `s_Δ < β_*(q)`,
  so membership gives
  `(l_*(y_q) - l(y_q)) log 2 ≤ s_Δ < β_*(q)`; with `log 2 > 9/13` this is
  `l_*(y_q) - l(y_q) < (13/9) β_*(q)`.
* As `a ∉ Clr`, the gain `l(y_{q+h}) - l(y_q)` over the window `{q + 1, …, q + h}` exceeds
  `(13/9) β_*(q)`, so `l(y_{q+h}) > l_*(y_q)`; since `β` is live the height never decreases, and
  `l(y_t) > l_*(y_q)` for every `t ≥ q + h`.
* The window `{q + h + 1, …, 𝔤(q)}` has `T_* + 1` elements, all at most `P_* - 1`; since the
  weighted white count `N^e_{P_*-1}(a)` bounds the number of white times and is at most `T_*`
  on `Low^e`, some `c` in it has `y_c` not white. Outside `Bad^e_m` the path stays at level at
  most `J`, so `y_c` is black.

## Main results

* `CollatzPosDens.exists_bkBlack_trFreshPath_bkColTop_lt`: after a black time `q` the path meets a
  black point `y_c` with `q < c ≤ 𝔤_ι(q)`, `c < J` and `l(y_c) > l_*(y_q)`.

## Implementation notes

The time `c` is a natural number: it exceeds `q ≥ 0`, so this is the same as asking for an
integer. The membership `a ∈ 𝒜_n` is part of `a ∈ Low^e`, and liveness of `β` is
`TrLive a.2`. The hypotheses `n ≥ 1` and `q ≤ p_{r_*(ι)}(ι)` are not used and are dropped,
which generalizes the source. The bound `log 2 > 693147180 / 10^9 > 9/13` is read off Mathlib's
`Real.log_two_gt_d9`.

## References

* [Mazur, *Collatz positive density*], §9.12.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `y^e_q(a)` is black and `a` has no oversize hit at time `q` for `ι`, then
`l_*(y^e_q(a)) - l(y^e_q(a)) < (13/9) β_*(ι, q)`. -/
theorem bkColTop_sub_bkL_lt_of_not_isTrOversizeHit {ι : FIndex} {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {e : ℤ × ℤ} (he : e ∈ bkPoints) {a : (ℕ × ℤ) × List (List ℤ × ℤ)}
    {q : ℕ} (hover : ¬IsTrOversizeHit ι n ξ (epsStar : ℝ) e a q)
    (hq : BkBlack n ξ (epsStar : ℝ) (trFreshPath e a q)) :
    ((bkColTop n ξ (epsStar : ℝ) (trFreshPath e a q) - bkL (trFreshPath e a q) : ℤ) : ℝ) <
      13 / 9 * (betaStar ι q : ℝ) := by
  have hε := epsStar_mem_bkRange (K := ℝ)
  have hyqP : trFreshPath e a q ∈ bkPoints := trFreshPath_mem_bkPoints he a q
  set Δ := bkCanonTriangle n ξ (epsStar : ℝ) (trFreshPath e a q) hyqP
  have hΔmem : trFreshPath e a q ∈ Δ := mem_bkCanonTriangle_self hξ hε.1 hε.2 hyqP hq
  have hΔfam : Δ ∈ bkFamily n ξ (epsStar : ℝ) := bkCanonTriangle_mem_bkFamily hyqP hq
  have hs : Δ.s < betaStar ι q := not_le.1 fun h => hover ⟨Δ, hΔfam, hΔmem, h⟩
  have hw := BkTriangle.weight_le_of_mem hΔmem
  have hj9 : (0 : ℝ) ≤ ((bkJ (trFreshPath e a q) - Δ.j : ℤ) : ℝ) * Real.log 9 :=
    mul_nonneg (by exact_mod_cast sub_nonneg.2 (BkTriangle.j_le_of_mem hΔmem))
      (Real.log_nonneg (by norm_num))
  have hlog : (693147180 : ℝ) / 10 ^ 9 < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hΔl : Δ.l = bkColTop n ξ (epsStar : ℝ) (trFreshPath e a q) := rfl
  rw [← hΔl]
  set d : ℝ := ((Δ.l - bkL (trFreshPath e a q) : ℤ) : ℝ)
  have hd : d * Real.log 2 < betaStar ι q := by linarith
  have hb0 : (0 : ℝ) < betaStar ι q := by exact_mod_cast betaStar_pos ι q
  clear_value d
  clear hw hj9 hs
  rcases le_or_gt d 0 with hd0 | hd0
  · linarith
  · have : d * (9 / 13) < d * Real.log 2 :=
      mul_lt_mul_of_pos_left (by linarith) hd0
    linarith

/-- Every closing value of an atom `a ∈ 𝒜_n` is at least `4`. -/
theorem four_le_of_mem_trAtoms {n : ℕ} {a : (ℕ × ℤ) × List (List ℤ × ℤ)}
    (ha : a ∈ trAtoms n) : ∀ b ∈ a.2, 4 ≤ b.2 := by
  intro b hb
  have := trAtoms_closing_mem ha hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  omega

/-- If `a ∉ Clr(ι)` has live `β` and `L - l(y^e_q(a)) < (13/9) β_*(ι, q)`, then
`L < l(y^e_t(a))` for every `t ≥ q + h_*(ι, q)`, provided
`q + h_*(ι, q) ≤ P_*(ι) - 1 ≤ ⌊n/2⌋`. -/
theorem lt_bkL_trFreshPath_of_notMem_trClear {ι : FIndex} {n : ℕ} {e : ℤ × ℤ}
    (hP : pStar ι ≤ n / 2) {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trAtoms n)
    (hlive : TrLive a.2) (hclr : a ∉ trClear ι n) {q : ℕ} (hqh : q + windowLength ι q ≤ pStar ι - 1)
    {L : ℤ} (hL : ((L - bkL (trFreshPath e a q) : ℤ) : ℝ) < 13 / 9 * (betaStar ι q : ℝ))
    {t : ℕ} (ht : q + windowLength ι q ≤ t) : L < bkL (trFreshPath e a t) := by
  have hlen : a.2.length = n / 2 := trAtoms_length ha
  set o : ℤ × ℤ := (bkJ e + a.1.1, bkL e + a.1.2)
  have hy : ∀ t, trFreshPath e a t = trPath o a.2 t := fun _ => rfl
  have hgain := lt_trClearGain_of_notMem_trClear ha hclr hqh
  rw [trClearGain_eq_chBlockPath _ _ _ (by omega)] at hgain
  have hgain' : (bkL (trFreshPath e a (q + windowLength ι q)) - bkL (trFreshPath e a q) : ℤ) =
      (chBlockPath a.2 (q + windowLength ι q)).2 - (chBlockPath a.2 q).2 := by
    rw [hy, hy, trPath_eq_add_chBlockPath, trPath_eq_add_chBlockPath]
    simp only [bkL, Prod.snd_add]
    ring
  have hclear : L < bkL (trFreshPath e a (q + windowLength ι q)) := by
    rw [← hgain'] at hgain
    have : (L : ℝ) < ((bkL (trFreshPath e a (q + windowLength ι q)) : ℤ) : ℝ) := by
      push_cast at hL hgain ⊢
      linarith
    exact_mod_cast this
  have := trPath_bkL_sub_ge o (four_le_of_mem_trAtoms ha) hlive ht
  rw [← hy, ← hy] at this
  have hmin : ((min (q + windowLength ι q) a.2.length : ℕ) : ℤ) ≤ (min t a.2.length : ℕ) :=
    Nat.cast_le.2 (min_le_min_right _ ht)
  omega

/-- If `a ∈ Low^e(ι)`, `P_*(ι) ≤ ⌊n/2⌋` and `𝔤_ι(q) ≤ P_*(ι) - 1`, then some `c` with
`q + h_*(ι, q) < c ≤ 𝔤_ι(q)` has `y^e_c(a)` not white. -/
theorem exists_not_isBkWhite_trFreshPath {ι : FIndex} {n : ℕ} {ξ : ResidueGroup n} {e : ℤ × ℤ}
    (hP : pStar ι ≤ n / 2) {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (hlow : a ∈ trLow ι n ξ e) {q : ℕ}
    (hg : recipeMap ι q ≤ pStar ι - 1) :
    ∃ c, q + windowLength ι q < c ∧ c ≤ recipeMap ι q ∧
      ¬IsBkWhite n ξ (epsStar : ℝ) (trFreshPath e a c) := by
  have hlen : a.2.length = n / 2 := trAtoms_length hlow.1
  have hgdef : recipeMap ι q = q + windowLength ι q + tStar ι + 1 := recipeMap_def ι q
  have hP1 := one_le_pStar ι
  by_contra! hall
  have hsub : Finset.Icc (q + windowLength ι q + 1) (recipeMap ι q) ⊆
      (Finset.Icc 1 (pStar ι - 1)).filter fun i =>
        IsBkWhite n ξ (epsStar : ℝ) (trPath (bkJ e + a.1.1, bkL e + a.1.2) a.2 i) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hall i (by omega) hi.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hcnt := card_white_le_trCount (n := n) (ξ := ξ) (bkJ e + a.1.1, bkL e + a.1.2) a.2
    (fun _ hb => trAtoms_closing_mem hlow.1 hb) (t := pStar ι - 1) (by omega)
  have hlow' := trWhiteCount_le_of_mem_trLow hlow
  rw [trWhiteCount_def] at hlow'
  have : recipeMap ι q + 1 - (q + windowLength ι q + 1) ≤ tStar ι := by
    exact_mod_cast (Nat.cast_le.2 hcard).trans (hcnt.trans hlow')
  omega

/-- **The next trace time comes on schedule.** Let `ι ∈ 𝔍`, `J = ⌊n/2⌋`, `ξ ∈ G_n` a unit,
`e ∈ 𝒫` and `m ∈ ℕ` with `j(e) + m = J`, `P_*(ι) ≤ J`, and `a = ((r, ℓ), β)` with `β` live and
`a ∈ Low^e(ι) \ (Bad^e_m(ι) ∪ Clr(ι))`. If `y^e_q(a)` is black, `a` has no oversize hit at time
`q` for `ι`, and `𝔤_ι(q) ≤ P_*(ι) - 1`, then some `c` with `q < c ≤ 𝔤_ι(q)` and `c < J` has
`y^e_c(a)` black and `l(y^e_c(a)) > l_*(y^e_q(a))`; black, white and `l_*` refer to
`(n, ξ, ε_*)`. -/
@[collatz_pos_dens "lem_tr_next_stop"]
theorem exists_bkBlack_trFreshPath_bkColTop_lt {ι : FIndex} {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {e : ℤ × ℤ} (he : e ∈ bkPoints) {m : ℕ}
    (hm : bkJ e + m = ((n / 2 : ℕ) : ℤ))
    (hP : pStar ι ≤ n / 2) {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (hlive : TrLive a.2)
    (hlow : a ∈ trLow ι n ξ e) (hbad : a ∉ trBad ι n e m)
    (hclr : a ∉ trClear ι n) {q : ℕ}
    (hq : BkBlack n ξ (epsStar : ℝ) (trFreshPath e a q))
    (hover : ¬IsTrOversizeHit ι n ξ (epsStar : ℝ) e a q) (hg : recipeMap ι q ≤ pStar ι - 1) :
    ∃ c : ℕ, q < c ∧ c ≤ recipeMap ι q ∧ c < n / 2 ∧
      BkBlack n ξ (epsStar : ℝ) (trFreshPath e a c) ∧
      bkColTop n ξ (epsStar : ℝ) (trFreshPath e a q) < bkL (trFreshPath e a c) := by
  have ha : a ∈ trAtoms n := hlow.1
  have hgdef : recipeMap ι q = q + windowLength ι q + tStar ι + 1 := recipeMap_def ι q
  obtain ⟨c, hqc, hcg, hcw⟩ := exists_not_isBkWhite_trFreshPath hP hlow hg
  have hjc : bkJ (trFreshPath e a c) ≤ ((n / 2 : ℕ) : ℤ) :=
    bkJ_trFreshPath_le_of_notMem_trBad hm ha hbad (by omega)
  refine ⟨c, by omega, hcg, by omega, ⟨hjc, not_lt.1 fun hlt => hcw ⟨hjc, hlt⟩⟩, ?_⟩
  exact lt_bkL_trFreshPath_of_notMem_trClear hP ha hlive hclr (by omega)
    (bkColTop_sub_bkL_lt_of_not_isTrOversizeHit hξ he hover hq) (by omega)

end CollatzPosDens
