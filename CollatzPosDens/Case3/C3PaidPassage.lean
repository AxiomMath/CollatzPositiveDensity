/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3HStep
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.CharSum.ChQRange
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPassage
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The paid passage decomposition of `Q`

Fix a level `n` and a residue `ξ ∈ G_n`, and let whiteness, the renewal function `Q`, the
penalty `H = Q / w` and the gap refer to `(n, ξ, ε_*)`. For a black point `e ∈ 𝒫` with gap
`ω = gap(e)` and a lattice point `x`, the *paid passage mass* is
```
F̃_e(x) = ∑_{π ∈ Π_ω, Bp_{|π|}(π) = x} bw^⊗(π) exp(-z_* N^*(e, π; |π|)) ∈ [0, ∞],
```
the total weight of the passage lists above level `ω` ending at `x`, each discounted by the
rewards collected along the way. The main result is the decomposition
`Q(e) = ∑_{x ∈ ℤ_{≥1} × ℤ} F̃_e(x) H(e + x)`.

It is proved by iterating the one-step identity
`H(v) = ∑_{b ∈ 𝔅} bw(b) exp(-z_* rw(v, b)) H(v + bpt(b))` until the block path first rises
above level `ω`. Every block of nonzero weight raises the level by at least `2`, so the
iteration stops after finitely many steps, and splitting off the first block of a passage list
identifies the result with the passage sum. Since `e` is black it is not white, so
`H(e) = Q(e)`.

## Main definitions

* `CollatzPosDens.c3PaidPassage n ξ e x`: the paid passage mass `F̃_e(x) ∈ [0, ∞]`.

## Main results

* `CollatzPosDens.cons_mem_trPassage_iff`: splitting off the first block of a passage list.
* `CollatzPosDens.ofReal_c3H_eq_tsum_trPassage`: for every `v ∈ 𝒫` and every level `s`,
  `H(v) = ∑_{π ∈ Π_s} bw^⊗(π) exp(-z_* N^*(v, π; |π|)) H(v + Bp_{|π|}(π))`.
* `CollatzPosDens.ofReal_chQ_eq_tsum_c3PaidPassage`: the decomposition
  `Q(e) = ∑_{x ∈ ℤ_{≥1} × ℤ} F̃_e(x) H(e + x)` for a black point `e ∈ 𝒫`.

## Implementation notes

The mass `F̃_e(x)` is a sum of nonnegative terms that need not be summable a priori, so it is an
`ℝ≥0∞`-valued `tsum`, and the decomposition of the real number `Q(e)` is stated after embedding
in `[0, ∞]` through `ENNReal.ofReal`. The gap is an integer, nonnegative by `trGap_nonneg`, and
the passage set is indexed by its `Int.toNat`. The definition makes sense for every `e : ℤ × ℤ`;
blackness of `e` is a hypothesis of the decomposition only.

The passage expansion is proved by induction on the level `s`, uniformly in the base point:
removing the first block `b` of a passage list in `Π_s` leaves either the empty list (when
`l(bpt(b)) > s`) or a passage list in `Π_{s - l(bpt(b))}` from the base point `v + bpt(b)`, and
`l(bpt(b)) ≥ 2` for a block of nonzero weight.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

/-- The paid passage mass of a point `e` at `x`:
`F̃_e(x) = ∑_{π ∈ Π_ω, Bp_{|π|}(π) = x} bw^⊗(π) exp(-z_* N^*(e, π; |π|))`, where
`ω = gap(e)` is the gap for `(n, ξ, ε_*)`. -/
@[collatz_pos_dens "def_c3_paid_passage"]
noncomputable def c3PaidPassage (n : ℕ) (ξ : ResidueGroup n) (e x : ℤ × ℤ) : ℝ≥0∞ :=
  ∑' π : trPassage (trGap n ξ (epsStar : ℝ) e).toNat,
    if chBlockPath π.1 π.1.length = x then
      ENNReal.ofReal (trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length))
    else 0

/-- A block of nonzero weight has level `l(bpt(b)) ≥ 2`. -/
theorem two_le_chBlockPoint_snd_of_chBlockWeight_ne_zero {b : List ℤ × ℤ}
    (hb : chBlockWeight b ≠ 0) : 2 ≤ (chBlockPoint b).2 := by
  rw [chBlockPoint_snd]
  have h1 := two_mul_length_le_sum_of_chBlockWeight_ne_zero hb
  have h2 := two_le_snd_of_chBlockWeight_ne_zero hb
  have : (0 : ℤ) ≤ b.1.length := by positivity
  linarith

/-- The endpoint of the block path of a nonempty list has first coordinate at least `1`. -/
theorem one_le_chBlockPath_length_fst {π : List (List ℤ × ℤ)} (hπ : π ≠ []) :
    1 ≤ (chBlockPath π π.length).1 := by
  rw [chBlockPath_fst, min_self]
  have h1 : (1 : ℤ) ≤ π.length := by exact_mod_cast List.length_pos_iff.mpr hπ
  have h2 : 0 ≤ ((π.take π.length).map fun b => (b.1.length : ℤ)).sum :=
    List.sum_nonneg fun y hy => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy
      positivity
  linarith

/-- **Splitting off the first block of a passage list.** The list `b :: π` lies in `Π_s` iff
`b ∈ 𝔅` has nonzero weight and either `π` is empty and `l(bpt(b)) > s`, or `l(bpt(b)) ≤ s` and
`π ∈ Π_{s - l(bpt(b))}`. -/
theorem cons_mem_trPassage_iff {s : ℕ} {b : List ℤ × ℤ} {π : List (List ℤ × ℤ)} :
    b :: π ∈ trPassage s ↔ b.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockWeight b ≠ 0 ∧
      ((π = [] ∧ (s : ℤ) < (chBlockPoint b).2) ∨
        ((chBlockPoint b).2 ≤ s ∧ π ∈ trPassage ((s : ℤ) - (chBlockPoint b).2).toNat)) := by
  have key : (∀ i < (b :: π).length, (chBlockPath (b :: π) i).2 ≤ s) ↔
      ∀ j < π.length, (chBlockPoint b).2 + (chBlockPath π j).2 ≤ s := by
    constructor
    · intro h j hj
      simpa using h (j + 1) (by simp; omega)
    · intro h i hi
      cases i with
      | zero => simp
      | succ j => simpa using h j (by simp at hi; omega)
  have hend : (chBlockPath (b :: π) (b :: π).length).2 =
      (chBlockPoint b).2 + (chBlockPath π π.length).2 := by simp
  rw [mem_trPassage, key, hend]
  simp only [List.mem_cons, forall_eq_or_imp, trLive_cons, ne_eq, reduceCtorEq,
    not_false_eq_true, true_and]
  constructor
  · rintro ⟨⟨hb4, hπ4⟩, ⟨hbw, hπl⟩, hlt, hfin⟩
    have hl := two_le_chBlockPoint_snd_of_chBlockWeight_ne_zero hbw
    refine ⟨hb4, hbw, ?_⟩
    rcases π with _ | ⟨c, π'⟩
    · left
      simpa using hfin
    · right
      have h0 := hlt 0 (by simp)
      simp only [chBlockPath_zero, Prod.snd_zero, add_zero] at h0
      have hs : ((((s : ℤ) - (chBlockPoint b).2).toNat : ℕ) : ℤ) = s - (chBlockPoint b).2 :=
        Int.toNat_of_nonneg (by omega)
      refine ⟨h0, hπ4, hπl, by simp, fun j hj => ?_, ?_⟩
      · rw [hs]
        have := hlt j hj
        omega
      · rw [hs]
        omega
  · rintro ⟨hb4, hbw, h | ⟨hle, hπ⟩⟩
    · obtain ⟨rfl, hlt⟩ := h
      refine ⟨⟨hb4, by simp⟩, ⟨hbw, trLive_nil⟩, fun j hj => by simp at hj, by simpa using hlt⟩
    · have hs : ((((s : ℤ) - (chBlockPoint b).2).toNat : ℕ) : ℤ) = s - (chBlockPoint b).2 :=
        Int.toNat_of_nonneg (by omega)
      obtain ⟨hπ4, hπl, -, hπle, hπlt⟩ := hπ
      refine ⟨⟨hb4, hπ4⟩, ⟨hbw, hπl⟩, fun j hj => ?_, ?_⟩
      · have := hπle j hj
        rw [hs] at this
        omega
      · rw [hs] at hπlt
        omega

/-- `H(v) ≤ e^{z_*}`: the penalty is bounded. -/
private theorem c3H_le_exp_zStar (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (v : ℤ × ℤ) :
    c3H n ξ ε v ≤ Real.exp (zStar : ℝ) := by
  have hQ := chQ_le_one n ξ ε v
  have h1 : 1 ≤ Real.exp (zStar : ℝ) := Real.one_le_exp (by exact_mod_cast zStar_nonneg)
  by_cases hw : IsBkWhite n ξ ε v
  · rw [c3H_of_isBkWhite hw]
    exact mul_le_of_le_one_right (Real.exp_pos _).le hQ
  · rw [c3H_of_not_isBkWhite hw]
    linarith

/-- The term `bw^⊗(π) exp(-z_* N^*(v, π; |π|)) H(v + Bp_{|π|}(π))` of a passage expansion
from `v`, in `[0, ∞]`. -/
private noncomputable def passageTerm (n : ℕ) (ξ : ResidueGroup n) (v : ℤ × ℤ)
    (π : List (List ℤ × ℤ)) : ℝ≥0∞ :=
  ENNReal.ofReal (trListWeight π * Real.exp (-(zStar : ℝ) * trCount n ξ v π π.length)) *
    ENNReal.ofReal (c3H n ξ (epsStar : ℝ) (v + chBlockPath π π.length))

private lemma passageTerm_cons (n : ℕ) (ξ : ResidueGroup n) (v : ℤ × ℤ) (b : List ℤ × ℤ)
    (π : List (List ℤ × ℤ)) :
    passageTerm n ξ v (b :: π) =
      ENNReal.ofReal (chBlockWeight b * Real.exp (-(zStar : ℝ) * trReward n ξ v b)) *
        passageTerm n ξ (v + chBlockPoint b) π := by
  have hr : trListWeight (b :: π) *
        Real.exp (-(zStar : ℝ) * trCount n ξ v (b :: π) (b :: π).length) =
      (chBlockWeight b * Real.exp (-(zStar : ℝ) * trReward n ξ v b)) *
        (trListWeight π *
          Real.exp (-(zStar : ℝ) * trCount n ξ (v + chBlockPoint b) π π.length)) := by
    rw [List.length_cons, trCount_cons_succ, trListWeight_cons, mul_add, Real.exp_add]
    ring
  rw [passageTerm, passageTerm, hr, ENNReal.ofReal_mul (mul_nonneg (chBlockWeight_nonneg _)
    (Real.exp_pos _).le), List.length_cons, chBlockPath_cons_succ, add_assoc, mul_assoc]

private lemma passageTerm_nil (n : ℕ) (ξ : ResidueGroup n) (v : ℤ × ℤ) :
    passageTerm n ξ v [] = ENNReal.ofReal (c3H n ξ (epsStar : ℝ) v) := by
  simp [passageTerm]

/-- The one-step identity for `H` in `[0, ∞]`. -/
private lemma ofReal_c3H_eq_tsum_block (n : ℕ) (ξ : ResidueGroup n) {v : ℤ × ℤ}
    (hv : v ∈ bkPoints) :
    ENNReal.ofReal (c3H n ξ (epsStar : ℝ) v) =
      ∑' β : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (chBlockWeight β * Real.exp (-(zStar : ℝ) * trReward n ξ v β)) *
          ENNReal.ofReal (c3H n ξ (epsStar : ℝ) (v + chBlockPoint β)) := by
  have hnn : ∀ β : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
      0 ≤ chBlockWeight β * Real.exp (-(zStar : ℝ) * trReward n ξ v β) :=
    fun β => mul_nonneg (chBlockWeight_nonneg _) (Real.exp_pos _).le
  have hsum : Summable fun β : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)} =>
      chBlockWeight β * Real.exp (-(zStar : ℝ) * trReward n ξ v β) *
        c3H n ξ (epsStar : ℝ) (v + chBlockPoint β) := by
    refine (hasSum_prod_chBlockWeight_single.summable.mul_right
      (Real.exp (zStar : ℝ))).of_nonneg_of_le
      (fun β => mul_nonneg (hnn β) (c3H_nonneg _ _ _ _)) fun β => ?_
    have he : Real.exp (-(zStar : ℝ) * trReward n ξ v β) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := trReward_nonneg (n := n) (ξ := ξ) v β.1
      have hz : (0 : ℝ) ≤ zStar := by exact_mod_cast zStar_nonneg
      nlinarith
    have hw := chBlockWeight_nonneg β.1
    calc chBlockWeight β * Real.exp (-(zStar : ℝ) * trReward n ξ v β) *
          c3H n ξ (epsStar : ℝ) (v + chBlockPoint β)
        ≤ chBlockWeight β * 1 * Real.exp (zStar : ℝ) := by
          gcongr
          all_goals first | exact c3H_le_exp_zStar _ _ _ _ | exact c3H_nonneg _ _ _ _
      _ = chBlockWeight β * Real.exp (zStar : ℝ) := by ring
  rw [c3H_eq_tsum n ξ hv, ENNReal.ofReal_tsum_of_nonneg
    (fun β => mul_nonneg (hnn β) (c3H_nonneg _ _ _ _)) hsum]
  exact tsum_congr fun β => ENNReal.ofReal_mul (hnn β)

/-- **Passage expansion of `H`.** For every `v ∈ 𝒫` and every level `s`,
`H(v) = ∑_{π ∈ Π_s} bw^⊗(π) exp(-z_* N^*(v, π; |π|)) H(v + Bp_{|π|}(π))` in `[0, ∞]`, all at
the threshold `ε_*`. -/
theorem ofReal_c3H_eq_tsum_trPassage (n : ℕ) (ξ : ResidueGroup n) (s : ℕ) {v : ℤ × ℤ}
    (hv : v ∈ bkPoints) :
    ENNReal.ofReal (c3H n ξ (epsStar : ℝ) v) =
      ∑' π : trPassage s,
        ENNReal.ofReal (trListWeight π.1 *
            Real.exp (-(zStar : ℝ) * trCount n ξ v π.1 π.1.length)) *
          ENNReal.ofReal (c3H n ξ (epsStar : ℝ) (v + chBlockPath π.1 π.1.length)) := by
  change _ = ∑' π : trPassage s, passageTerm n ξ v π.1
  induction s using Nat.strong_induction_on generalizing v with
  | _ s ih =>
  rw [tsum_subtype (trPassage s) (passageTerm n ξ v)]
  set B : Set (List ℤ × ℤ) := {b | b.2 ∈ ({4, 5} : Set ℤ)}
  -- the contribution of the passage lists starting with a given block
  have hblock : ∀ b : B,
      ENNReal.ofReal (chBlockWeight b * Real.exp (-(zStar : ℝ) * trReward n ξ v b)) *
          ENNReal.ofReal (c3H n ξ (epsStar : ℝ) (v + chBlockPoint b)) =
        ∑' π, (trPassage s).indicator (passageTerm n ξ v) (b.1 :: π) := by
    intro b
    by_cases hbw : chBlockWeight b = 0
    · rw [hbw, zero_mul, ENNReal.ofReal_zero, zero_mul]
      refine (ENNReal.tsum_eq_zero.mpr fun π => Set.indicator_of_notMem ?_ _).symm
      rw [cons_mem_trPassage_iff]
      exact fun h => h.2.1 hbw
    have hl := two_le_chBlockPoint_snd_of_chBlockWeight_ne_zero hbw
    by_cases hlt : (s : ℤ) < (chBlockPoint b).2
    · rw [tsum_eq_single [], Set.indicator_of_mem, passageTerm_cons, passageTerm_nil]
      · exact cons_mem_trPassage_iff.mpr ⟨b.2, hbw, Or.inl ⟨rfl, hlt⟩⟩
      · intro π hπ
        refine Set.indicator_of_notMem ?_ _
        rw [cons_mem_trPassage_iff]
        rintro ⟨-, -, h | h⟩
        · exact hπ h.1
        · omega
    · push Not at hlt
      set s' := ((s : ℤ) - (chBlockPoint b).2).toNat
      have hs' : s' < s := by omega
      have hv' : v + chBlockPoint b ∈ bkPoints := add_mem_bkPoints hv (chBlockPoint_mem_bkPoints _)
      have hterm : ∀ π, (trPassage s).indicator (passageTerm n ξ v) (b.1 :: π) =
          ENNReal.ofReal (chBlockWeight b * Real.exp (-(zStar : ℝ) * trReward n ξ v b)) *
            (trPassage s').indicator (passageTerm n ξ (v + chBlockPoint b)) π := by
        intro π
        have hiff : b.1 :: π ∈ trPassage s ↔ π ∈ trPassage s' := by
          rw [cons_mem_trPassage_iff]
          constructor
          · rintro ⟨-, -, h | h⟩
            · omega
            · exact h.2
          · exact fun h => ⟨b.2, hbw, Or.inr ⟨hlt, h⟩⟩
        by_cases hπ : π ∈ trPassage s'
        · rw [Set.indicator_of_mem (hiff.mpr hπ), Set.indicator_of_mem hπ, passageTerm_cons]
        · rw [Set.indicator_of_notMem (mt hiff.mp hπ), Set.indicator_of_notMem hπ, mul_zero]
      rw [tsum_congr hterm, ENNReal.tsum_mul_left, ih s' hs' hv',
        tsum_subtype (trPassage s') (passageTerm n ξ (v + chBlockPoint b))]
  have hsupp : Function.support ((trPassage s).indicator (passageTerm n ξ v)) ⊆
      Set.range fun p : (List ℤ × ℤ) × List (List ℤ × ℤ) => p.1 :: p.2 := by
    intro π hπ
    have hmem : π ∈ trPassage s := by
      by_contra h
      exact hπ (Set.indicator_of_notMem h _)
    obtain ⟨b, π', rfl⟩ := List.exists_cons_of_ne_nil (ne_nil_of_mem_trPassage hmem)
    exact ⟨(b, π'), rfl⟩
  have hinj : Function.Injective fun p : (List ℤ × ℤ) × List (List ℤ × ℤ) => p.1 :: p.2 :=
    fun p q h => Prod.ext (List.cons.inj h).1 (List.cons.inj h).2
  have hout : ∀ b : List ℤ × ℤ,
      ∑' π, (trPassage s).indicator (passageTerm n ξ v) (b :: π) =
        B.indicator (fun b => ∑' π, (trPassage s).indicator (passageTerm n ξ v) (b :: π)) b := by
    intro b
    by_cases hb : b ∈ B
    · rw [Set.indicator_of_mem hb]
    · rw [Set.indicator_of_notMem hb]
      refine ENNReal.tsum_eq_zero.mpr fun π => Set.indicator_of_notMem ?_ _
      rw [cons_mem_trPassage_iff]
      exact fun h => hb h.1
  have hprod : ∑' p : (List ℤ × ℤ) × List (List ℤ × ℤ),
        (trPassage s).indicator (passageTerm n ξ v) (p.1 :: p.2) =
      ∑' b, ∑' π, (trPassage s).indicator (passageTerm n ξ v) (b :: π) :=
    ENNReal.tsum_prod (f := fun b π => (trPassage s).indicator (passageTerm n ξ v) (b :: π))
  rw [← hinj.tsum_eq hsupp, hprod, tsum_congr hout, ← tsum_subtype B,
    ← tsum_congr hblock]
  exact ofReal_c3H_eq_tsum_block n ξ hv

/-- **Paid passage decomposition of `Q`.** Let `e ∈ 𝒫` be black for `(n, ξ, ε_*)`. Then
`Q(e) = ∑_{x ∈ ℤ_{≥1} × ℤ} F̃_e(x) H(e + x)`, in `[0, ∞]`. -/
@[collatz_pos_dens "lem_c3_paid_passage"]
theorem ofReal_chQ_eq_tsum_c3PaidPassage (n : ℕ) (ξ : ResidueGroup n) {e : ℤ × ℤ}
    (he : e ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) e) :
    ENNReal.ofReal (chQ n ξ (epsStar : ℝ) e) =
      ∑' x : {x : ℤ × ℤ // 1 ≤ x.1},
        c3PaidPassage n ξ e x * ENNReal.ofReal (c3H n ξ (epsStar : ℝ) (e + x)) := by
  have hw : ¬ IsBkWhite n ξ (epsStar : ℝ) e := fun hw => lt_irrefl _ (hb.2.trans_lt hw.2)
  set ω := (trGap n ξ (epsStar : ℝ) e).toNat
  -- the paid passage mass vanishes off `ℤ_{≥1} × ℤ`
  have hzero : ∀ x : ℤ × ℤ, ¬ 1 ≤ x.1 → c3PaidPassage n ξ e x = 0 := by
    intro x hx
    refine ENNReal.tsum_eq_zero.mpr fun π => ite_eq_right_iff.mpr fun h => absurd ?_ hx
    rw [← h]
    exact one_le_chBlockPath_length_fst (ne_nil_of_mem_trPassage π.2)
  have hsub : (∑' x : {x : ℤ × ℤ // 1 ≤ x.1},
        c3PaidPassage n ξ e x * ENNReal.ofReal (c3H n ξ (epsStar : ℝ) (e + x))) =
      ∑' x, c3PaidPassage n ξ e x * ENNReal.ofReal (c3H n ξ (epsStar : ℝ) (e + x)) := by
    set f : ℤ × ℤ → ℝ≥0∞ := fun x =>
      c3PaidPassage n ξ e x * ENNReal.ofReal (c3H n ξ (epsStar : ℝ) (e + x))
    have hind : {x : ℤ × ℤ | 1 ≤ x.1}.indicator f = f := by
      refine Set.indicator_eq_self.mpr fun x hx => ?_
      by_contra h
      exact hx (by simp only [f, hzero x h, zero_mul])
    calc _ = ∑' x, {x : ℤ × ℤ | 1 ≤ x.1}.indicator f x := tsum_subtype {x : ℤ × ℤ | 1 ≤ x.1} f
      _ = ∑' x, f x := by rw [hind]
  rw [← c3H_of_not_isBkWhite hw, ofReal_c3H_eq_tsum_trPassage n ξ ω he, hsub]
  simp only [c3PaidPassage, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun π => ?_
  rw [tsum_eq_single (chBlockPath π.1 π.1.length)]
  · simp
  · intro x hx
    simp [Ne.symm hx]

end CollatzPosDens
