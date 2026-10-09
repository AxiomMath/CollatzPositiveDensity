/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FcMinOvershoot
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.FirstCrossingFinite
public import CollatzPosDens.Seed.ConcatWord
public import CollatzPosDens.Seed.FirstScales
public import CollatzPosDens.Seed.RoundedOffset
public import CollatzPosDens.Seed.Selector
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.Seed.SelectedRatioCompute
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

/-!
# Mass retained by the selector

Let `𝔗₅` be the set of selected central tuples of length five: the tuples
`t = (w₀, …, w₄)` with `w_j ∈ 𝒞(b_j, K_j)` satisfying the five-block selector `Sel`. We prove
the lower bound
$$\sum_{t \in \mathfrak T_5} 2^{-A(\hat w(t))} >
  \frac12 \prod_{j<5} \mathbf p(\mathcal C(b_j, K_j)).$$

Since `(b_j, K_j) = (9 + j, 16)` for `j < 5`, the right-hand side is half the product of the
masses of the five finite families `𝒞(u, 16)`, `9 ≤ u ≤ 13`. The selector is the conjunction
of a condition `S₀₁` on the first two blocks and of caps on the rounded offsets of the last
three, so the left-hand side factors as `P₀₁ ν₂ ν₃ ν₄`. Each factor is evaluated exactly by
the backward dynamic programme of `CollatzPosDens.Seed.SelectedRatioCompute`;
here we prove that the programme computes the stated sums over the families, identify the
families with the central families, and compare.

## Main results

* `CollatzPosDens.half_mul_prod_geomMass_lt_tsum_selectedTuples_five`: the bound above.

## Implementation notes

The sum over `𝔗₅` is the unconditional sum in `ℝ≥0∞` of the weights `2⁻¹ ^ A(ŵ(t))`, and the
product is over `j ∈ Finset.range 5`. The inequality is proved through a lower bound for the
left-hand side: for the pair `(v₀, v₁)` we only retain the pairs whose rounded offsets satisfy
the integer form `192 · 2^A ≤ z₀ 2^A + 8 · 3^d z₁ ≤ 1216 · 2^A`, `z₁ ≤ 1024`, `z₀ ≤ 1216` of `S₀₁`
(with `z₀ = 2^9 rd₉(v₀)`, `z₁ = 2^6 rd₆(v₁)`, `(d, A) = (|v₀|, A(v₀))`), which is equivalent
to it; the resulting retained mass is exactly the value `P₀₁`.

The finite family `𝒞(u, 16)` is enumerated by the `Finset` of completions of the root state of
the programme; every sum over it is computed by the programme modulo a power `X^E` of a digit
base, and the base-`X` digits are read off modulo `X - 1`.

## References

* [Mazur, *Collatz positive density*], §17.6.
-/

@[expose] public section

namespace CollatzPosDens.SelectedRatio

/-! ### A generic backward dynamic programme over words -/

/-- The completions of a state `(d, A)` with fuel `n`. -/
private def Par.comp (P : Par) : ℕ → ℕ → ℕ → Finset Word
  | 0, _, _ => ∅
  | n + 1, d, A =>
    (if P.Fin d A then {[]} else ∅) ∪
      (if P.Alive d A then
        (Finset.range (P.top - A)).biUnion fun i =>
          (P.comp n (d + 1) (A + (i + 1))).map ⟨List.cons (Nat.succPNat i), List.cons_injective⟩
      else ∅)

/-- The weight of a completion. -/
private def Par.val (P : Par) (pw : ℕ → ℕ → ℕ) (F : ℕ → ℕ → ℕ) : ℕ → ℕ → Word → ℕ
  | d, A, [] => 2 ^ (P.top - A) * F d A
  | d, A, a :: w => pw d (A + a) * P.val pw F (d + 1) (A + a) w

private theorem Par.sum_comp_succ (P : Par) (pw : ℕ → ℕ → ℕ) (F : ℕ → ℕ → ℕ)
    (n d A : ℕ) :
    ∑ w ∈ P.comp (n + 1) d A, P.val pw F d A w =
      (if P.Fin d A then 2 ^ (P.top - A) * F d A else 0) +
      (if P.Alive d A then ∑ i ∈ Finset.range (P.top - A),
        pw d (A + (i + 1)) * ∑ w ∈ P.comp n (d + 1) (A + (i + 1)),
          P.val pw F (d + 1) (A + (i + 1)) w else 0) := by
  rw [Par.comp, Finset.sum_union]
  · congr 1
    · split_ifs <;> simp [Par.val]
    · split_ifs with h
      · rw [Finset.sum_biUnion]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_map, Finset.mul_sum]
          rfl
        · intro i _ j _ hij
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro w hw hw'
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hw hw'
          obtain ⟨u, -, rfl⟩ := hw
          obtain ⟨v, -, hv⟩ := hw'
          have := (List.cons_eq_cons.1 hv).1
          exact hij (by simpa using this.symm)
      · simp
  · rw [Finset.disjoint_left]
    intro w hw hw'
    have hw0 : w = [] := by split_ifs at hw <;> simp_all
    subst hw0
    split_ifs at hw' <;> simp at hw'

private theorem Par.goRow_spec (P : Par) (pw : ℕ → ℕ → ℕ) (M : ℕ) (F : ℕ → ℕ → ℕ)
    (d : ℕ) (g : ℕ → ℕ) : ∀ (m A0 : ℕ) (L : List ℕ),
    List.Forall₂ (fun x y => x ≡ y [MOD M]) L ((List.range' A0 m).map g) →
    (P.goRow pw M F d A0 L).1 ≡ ∑ j ∈ Finset.range m, pw d (A0 + j) * g (A0 + j) [MOD M] ∧
    List.Forall₂ (fun x y => x ≡ y [MOD M]) (P.goRow pw M F d A0 L).2
      ((List.range' A0 m).map fun A => (if P.Fin d A then 2 ^ (P.top - A) * F d A else 0) +
        (if P.Alive d A then ∑ j ∈ Finset.range (A0 + m - (A + 1)),
          pw d (A + 1 + j) * g (A + 1 + j) else 0))
  | 0, A0, L, hL => by
    simp only [List.range'_zero, List.map_nil, List.forall₂_nil_right_iff] at hL
    subst hL
    simp [Par.goRow, Nat.ModEq.refl]
  | m + 1, A0, L, hL => by
    rw [List.range'_succ, List.map_cons] at hL
    obtain ⟨x, L', hx, hL', rfl⟩ : ∃ x L', x ≡ g A0 [MOD M] ∧
        List.Forall₂ (fun x y => x ≡ y [MOD M]) L' ((List.range' (A0 + 1) m).map g) ∧
          L = x :: L' := by
      cases hL with
      | cons h1 h2 => exact ⟨_, _, h1, h2, rfl⟩
    obtain ⟨ih1, ih2⟩ := Par.goRow_spec P pw M F d g m (A0 + 1) L' hL'
    have hm : A0 + 1 + m = A0 + (m + 1) := by omega
    rw [hm] at ih2
    refine ⟨?_, ?_⟩
    · simp only [Par.goRow]
      refine (Nat.mod_modEq _ _).trans ?_
      rw [Finset.sum_range_succ', add_zero, add_comm (∑ j ∈ Finset.range m, _)]
      refine (hx.mul_left _).add ?_
      have : ∑ j ∈ Finset.range m, pw d (A0 + 1 + j) * g (A0 + 1 + j) =
          ∑ j ∈ Finset.range m, pw d (A0 + (j + 1)) * g (A0 + (j + 1)) :=
        Finset.sum_congr rfl fun j _ => by rw [show A0 + 1 + j = A0 + (j + 1) by omega]
      rwa [this] at ih1
    · simp only [Par.goRow, List.range'_succ, List.map_cons]
      refine List.Forall₂.cons ?_ ih2
      refine (Nat.mod_modEq _ _).trans (Nat.ModEq.add_left _ ?_)
      split_ifs
      · rwa [show A0 + (m + 1) - (A0 + 1) = m by omega]
      · exact Nat.ModEq.refl _

private theorem Par.table_spec (P : Par) (pw : ℕ → ℕ → ℕ) (M : ℕ) (F : ℕ → ℕ → ℕ) :
    ∀ k ≤ P.h + 1, List.Forall₂ (fun x y => x ≡ y [MOD M]) (P.table pw M F k)
      ((List.range' 0 (P.top + 1)).map fun A =>
        ∑ w ∈ P.comp k (P.h + 1 - k) A, P.val pw F (P.h + 1 - k) A w)
  | 0, _ => by
    simp only [Par.table, Par.comp, Finset.sum_empty]
    rw [List.map_const', List.length_range']
    exact List.forall₂_same.2 fun _ _ => Nat.ModEq.refl _
  | k + 1, hk => by
    have ih := Par.table_spec P pw M F k (by omega)
    obtain ⟨-, h2⟩ := P.goRow_spec pw M F (P.h - k) _ (P.top + 1) 0 _ ih
    simp only [Par.table]
    convert h2 using 1
    refine List.map_congr_left fun A _ => ?_
    rw [show P.h + 1 - (k + 1) = P.h - k by omega, Par.sum_comp_succ,
      show P.h + 1 - k = P.h - k + 1 by omega, show 0 + (P.top + 1) - (A + 1) = P.top - A by omega]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show A + 1 + j = A + (j + 1) by omega]

private theorem Par.dpRoot_modEq (P : Par) (pw : ℕ → ℕ → ℕ) (M : ℕ) (F : ℕ → ℕ → ℕ) :
    P.dpRoot pw M F ≡ ∑ w ∈ P.comp (P.h + 1) 0 0, P.val pw F 0 0 w [MOD M] := by
  have h := P.table_spec pw M F (P.h + 1) le_rfl
  rw [Nat.sub_self, show P.top + 1 = (P.top + 1 - 1) + 1 by omega, List.range'_succ,
    List.map_cons] at h
  unfold Par.dpRoot
  generalize P.table pw M F (P.h + 1) = L at h ⊢
  cases h with
  | cons h1 _ => simpa using h1

private theorem Par.nil_mem_comp (P : Par) (n d A : ℕ) :
    [] ∈ P.comp (n + 1) d A ↔ P.Fin d A := by
  simp only [Par.comp, Finset.mem_union]
  constructor
  · rintro (h | h)
    · split_ifs at h with hf
      · exact hf
      · simp at h
    · split_ifs at h <;> simp at h
  · intro hf
    left
    rw [ite_eq_left hf]
    exact Finset.mem_singleton_self _

private theorem Par.cons_mem_comp (P : Par) (n d A : ℕ) (a : ℕ+) (w : Word) :
    a :: w ∈ P.comp (n + 1) d A ↔
      P.Alive d A ∧ (a : ℕ) ≤ P.top - A ∧ w ∈ P.comp n (d + 1) (A + a) := by
  simp only [Par.comp, Finset.mem_union]
  have h1 : a :: w ∉ (if P.Fin d A then ({[]} : Finset Word) else ∅) := by
    split_ifs <;> simp
  simp only [h1, false_or]
  split_ifs with h
  · simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_map,
      Function.Embedding.coeFn_mk, List.cons.injEq]
    constructor
    · rintro ⟨i, hi, v, hv, rfl, rfl⟩
      refine ⟨h, by simp; omega, by simpa using hv⟩
    · rintro ⟨-, ha, hw⟩
      refine ⟨(a : ℕ) - 1, by have := a.pos; omega, w, ?_, ?_, rfl⟩
      · rwa [show (a : ℕ) - 1 + 1 = a by have := a.pos; omega]
      · apply PNat.eq
        have := a.pos
        simp
        omega
  · simp [h]

private theorem Par.le_top_of_mem_comp (P : Par) :
    ∀ (n d A : ℕ) (w : Word), w ∈ P.comp n d A → A + w.valSum ≤ P.top
  | 0, _, _, _, h => by simp [Par.comp] at h
  | n + 1, d, A, [], h => by
    rw [P.nil_mem_comp] at h
    simpa using h.2.2.2.2
  | n + 1, d, A, a :: w, h => by
    rw [P.cons_mem_comp] at h
    have := P.le_top_of_mem_comp n (d + 1) (A + a) w h.2.2
    simp only [Word.valSum_cons]
    omega

/-- The family described by the parameters. -/
private def Par.fam (P : Par) : Set Word :=
  {w | P.l < w.length ∧ w.length ≤ P.h ∧
    (∀ i, P.l ≤ i → i < w.length → (Word.valSum (w.take i) : ℤ) < P.H i) ∧
    P.lo w.length ≤ w.valSum ∧ (w.valSum : ℤ) ≤ P.hi w.length}

private theorem Par.mem_fam_iff_aux (P : Par) (htop : ∀ s ≤ P.h, P.hi s ≤ P.top) :
    ∀ (w u : Word) (n : ℕ), n + u.length = P.h + 1 →
      (∀ i, P.l ≤ i → i < u.length → (Word.valSum (u.take i) : ℤ) < P.H i) →
      (u ++ w ∈ P.fam ↔ w ∈ P.comp n u.length u.valSum)
  | [], u, 0, hn, _ => by
    simp only [Par.comp, Finset.notMem_empty, iff_false, List.append_nil]
    intro h; have := h.2.1; omega
  | [], u, n + 1, hn, hu => by
    rw [P.nil_mem_comp, List.append_nil]
    constructor
    · rintro ⟨h1, h2, -, h4, h5⟩
      refine ⟨h1, h2, h4, h5, ?_⟩
      have := htop _ h2
      omega
    · rintro ⟨h1, h2, h4, h5, -⟩
      exact ⟨h1, h2, hu, h4, h5⟩
  | a :: w, u, 0, hn, _ => by
    simp only [Par.comp, Finset.notMem_empty, iff_false]
    intro h; have := h.2.1; simp at this; omega
  | a :: w, u, n + 1, hn, hu => by
    rw [P.cons_mem_comp]
    have e : u ++ a :: w = (u ++ [a]) ++ w := by simp
    have hlen : (u ++ [a]).length = u.length + 1 := by simp
    have hval : (u ++ [a]).valSum = u.valSum + a := by simp
    have hu' : P.Alive u.length u.valSum → ∀ i, P.l ≤ i → i < (u ++ [a]).length →
        (Word.valSum ((u ++ [a]).take i) : ℤ) < P.H i := by
      intro halive i hi1 hi2
      rw [hlen] at hi2
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi2 with hi | rfl
      · rw [List.take_append_of_le_length hi.le]
        exact hu i hi1 hi
      · simpa using halive hi1
    constructor
    · intro h
      have halive : P.Alive u.length u.valSum := fun hl => by
        simpa using h.2.2.1 u.length hl (by simp)
      rw [e, P.mem_fam_iff_aux htop w (u ++ [a]) n (by rw [hlen]; omega) (hu' halive), hlen,
        hval] at h
      have := P.le_top_of_mem_comp n _ _ w h
      exact ⟨halive, by omega, h⟩
    · rintro ⟨halive, -, h⟩
      rwa [e, P.mem_fam_iff_aux htop w (u ++ [a]) n (by rw [hlen]; omega) (hu' halive), hlen,
        hval]

private theorem Par.coe_comp (P : Par) (htop : ∀ s ≤ P.h, P.hi s ≤ P.top) :
    (P.comp (P.h + 1) 0 0 : Set Word) = P.fam := by
  ext w
  simpa using (P.mem_fam_iff_aux htop w [] (P.h + 1) (by simp) (by simp)).symm

/-! ### Accumulated rounded offsets -/

/-- The accumulated increments `∑ inc (d + j) (A + A(w_{≤ j+1}))` of a completion `w`. -/
private def srZ (inc : ℕ → ℕ → ℕ) : ℕ → ℕ → Word → ℕ
  | _, _, [] => 0
  | d, A, a :: w => inc d (A + a) + srZ inc (d + 1) (A + a) w

private theorem srZ_eq_sum (inc : ℕ → ℕ → ℕ) : ∀ (d A : ℕ) (w : Word),
    srZ inc d A w = ∑ j ∈ Finset.range w.length, inc (d + j) (A + Word.valSum (w.take (j + 1)))
  | _, _, [] => by simp [srZ]
  | d, A, a :: w => by
    rw [srZ, srZ_eq_sum inc (d + 1) (A + a) w, List.length_cons, Finset.sum_range_succ']
    simp only [List.take_succ_cons, List.take_zero, Word.valSum_cons, Word.valSum_nil, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show d + 1 + j = d + (j + 1) by omega, add_assoc]

private theorem Par.val_modEq (P : Par) (pw : ℕ → ℕ → ℕ) (F : ℕ → ℕ → ℕ) (X M : ℕ)
    (inc : ℕ → ℕ → ℕ) (hpw : ∀ j a, pw j a ≡ X ^ inc j a [MOD M]) :
    ∀ (d A : ℕ) (w : Word), P.val pw F d A w ≡
      2 ^ (P.top - (A + Word.valSum w)) * X ^ srZ inc d A w *
        F (d + w.length) (A + Word.valSum w) [MOD M]
  | d, A, [] => by simp [Par.val, srZ, Nat.ModEq.refl]
  | d, A, a :: w => by
    rw [Par.val]
    refine ((hpw d (A + a)).mul (P.val_modEq pw F X M inc hpw (d + 1) (A + a) w)).trans ?_
    rw [srZ, Word.valSum_cons, List.length_cons, show A + a + Word.valSum w =
      A + (a + Word.valSum w) by ring, show d + 1 + w.length = d + (w.length + 1) by ring, pow_add]
    exact congrArg (· % M) (by ring)

/-! ### Reading base-`X` digits -/

private theorem srSplit {ι : Type*} (s : Finset ι) (c e : ι → ℕ) (X k : ℕ) :
    ∑ i ∈ s, c i * X ^ e i = ∑ i ∈ s with e i < k, c i * X ^ e i +
      X ^ k * ∑ i ∈ s with ¬ e i < k, c i * X ^ (e i - k) := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => e i < k), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_filter] at hi
  rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (not_lt.1 hi.2)]

private theorem srLow_lt {ι : Type*} (s : Finset ι) (c e : ι → ℕ) (X k : ℕ)
    (hX : ∑ i ∈ s, c i < X) : ∑ i ∈ s with e i < k, c i * X ^ e i < X ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hX1 : 1 ≤ X := by omega
  calc ∑ i ∈ s with e i < k, c i * X ^ e i ≤ ∑ i ∈ s with e i < k, c i * X ^ (k - 1) :=
        Finset.sum_le_sum fun i hi => by
          rw [Finset.mem_filter] at hi
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
    _ ≤ ∑ i ∈ s, c i * X ^ (k - 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Nat.zero_le _
    _ = (∑ i ∈ s, c i) * X ^ (k - 1) := by rw [Finset.sum_mul]
    _ < X * X ^ (k - 1) := Nat.mul_lt_mul_of_pos_right hX (by positivity)
    _ = X ^ k := by rw [← pow_succ', Nat.sub_add_cancel hk]

private theorem srDig_sum {ι : Type*} (s : Finset ι) (c e : ι → ℕ) (X lo hi : ℕ)
    (hX : ∑ i ∈ s, c i < X - 1) :
    dig X (∑ i ∈ s, c i * X ^ e i) lo hi = ∑ i ∈ s with lo ≤ e i ∧ e i ≤ hi, c i := by
  have hX' : ∑ i ∈ s, c i < X := by omega
  unfold dig
  rw [srSplit s c e X (hi + 1), Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (srLow_lt s c e X _ hX'), srSplit _ c e X lo]
  have hsub : ∑ i ∈ s with e i < hi + 1, c i < X :=
    lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => Nat.zero_le _) hX'
  rw [Nat.add_mul_div_left _ _ (pow_pos (by omega) _), Nat.div_eq_of_lt (srLow_lt _ c e X _ hsub),
    zero_add, Finset.filter_filter]
  have hcong : ∑ i ∈ s with e i < hi + 1 ∧ ¬ e i < lo, c i * X ^ (e i - lo) ≡
      ∑ i ∈ s with e i < hi + 1 ∧ ¬ e i < lo, c i [MOD X - 1] := by
    refine Nat.ModEq.sum fun i _ => ?_
    have h1 : X ≡ 1 [MOD X - 1] := Nat.modEq_sub (by omega)
    simpa using (h1.pow (e i - lo)).mul_left (c i)
  have hlt : ∑ i ∈ s with e i < hi + 1 ∧ ¬ e i < lo, c i < X - 1 :=
    lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => Nat.zero_le _) hX
  rw [hcong, Nat.mod_eq_of_lt hlt]
  refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
  omega

/-! ### The programme computes sums over the family -/

private theorem srPw_modEq (X : ℕ) (inc : ℕ → ℕ → ℕ) (E j a : ℕ) :
    pw X inc E j a ≡ X ^ inc j a [MOD X ^ E] := by
  unfold pw
  rcases le_total (inc j a) E with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    exact (Nat.modEq_zero_iff_dvd.2 dvd_rfl).trans
      (Nat.modEq_zero_iff_dvd.2 (pow_dvd_pow X h)).symm

private theorem Par.dpRoot_pow_modEq (P : Par) (X E : ℕ) (inc : ℕ → ℕ → ℕ)
    (F : ℕ → ℕ → ℕ) :
    P.dpRoot (pw X inc E) (X ^ E) F ≡ ∑ v ∈ P.comp (P.h + 1) 0 0,
      2 ^ (P.top - Word.valSum v) * X ^ srZ inc 0 0 v * F v.length (Word.valSum v) [MOD X ^ E] := by
  refine (P.dpRoot_modEq _ _ F).trans (Nat.ModEq.sum fun v _ => ?_)
  simpa using P.val_modEq (pw X inc E) F X (X ^ E) inc (srPw_modEq X inc E) 0 0 v

private theorem Par.dpRoot_one (P : Par) (F : ℕ → ℕ → ℕ) :
    P.dpRoot (fun _ _ => 1) 0 F = ∑ v ∈ P.comp (P.h + 1) 0 0,
      2 ^ (P.top - Word.valSum v) * F v.length (Word.valSum v) := by
  have h := (P.dpRoot_modEq (fun _ _ => 1) 0 F).trans (Nat.ModEq.sum fun v _ =>
    P.val_modEq (fun _ _ => 1) F 1 0 (fun _ _ => 0) (fun _ _ => by simp [Nat.ModEq.refl]) 0 0 v)
  simpa [Nat.modEq_zero_iff] using h

private theorem srDig_congr {X N S lo hi E : ℕ} (h : N ≡ S [MOD X ^ E]) (hE : hi + 1 ≤ E) :
    dig X N lo hi = dig X S lo hi := by
  unfold dig
  rw [Nat.ModEq.of_dvd (pow_dvd_pow X hE) h]

/-! ### Identifying the families -/

private theorem srMu_real_iff (u s k N : ℕ) (hN : barrierRb u s + k = N) :
    (16 * 3 ^ s * 2 ^ (3 * u) : ℝ) < (2 ^ (3 * u) - 1) * (2 : ℝ) ^ (barrier u (rb u) s + k) ↔
      16 * 3 ^ s * 2 ^ (3 * u) < (2 ^ (3 * u) - 1) * 2 ^ N := by
  rw [barrier_rb_eq_barrierRb, hN, zpow_natCast]
  have : ((2 ^ (3 * u) - 1 : ℕ) : ℝ) = 2 ^ (3 * u) - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; simp
  rw [← this]
  norm_cast

private theorem fcMinOvershoot_eq_srMu (u s : ℕ) (hu : 1 ≤ u) (h0 : 1 ≤ barrierRb u s)
    (h1 : 16 * 3 ^ s * 2 ^ (3 * u) < (2 ^ (3 * u) - 1) * 2 ^ ((barrierRb u s).toNat + mu u s))
    (h2 : mu u s = 0 ∨ ¬ 16 * 3 ^ s * 2 ^ (3 * u) <
      (2 ^ (3 * u) - 1) * 2 ^ ((barrierRb u s).toNat + (mu u s - 1))) :
    fcMinOvershoot u s = mu u s := by
  apply le_antisymm
  · apply fcMinOvershoot_le
    rw [srMu_real_iff u s _ ((barrierRb u s).toNat + mu u s) (by push_cast; omega)]
    exact h1
  · rcases h2 with h2 | h2
    · rw [h2]; exact Nat.zero_le _
    · by_contra hlt
      have hle : fcMinOvershoot u s ≤ mu u s - 1 := by omega
      rw [fcMinOvershoot_le_iff hu,
        srMu_real_iff u s _ ((barrierRb u s).toNat + (mu u s - 1)) (by push_cast; omega)] at hle
      exact h2 hle

private theorem srCentral (u : ℕ) (hu1 : 9 ≤ u) (hu2 : u ≤ 13)
    (hmu : u ≤ 11 → ∀ s, lb u < s → s ≤ hb u → fcMinOvershoot u s = mu u s) :
    centralFamily u 16 = (par u).fam := by
  ext w
  simp only [mem_centralFamily, mem_firstCrossing, Par.fam, par, barrier_rb_eq_barrierRb,
    Set.mem_ofPred_eq, Nat.cast_ofNat]
  have h256 : ¬ 256 ≤ u := by omega
  simp only [h256, false_imp_iff, and_true]
  by_cases h11 : u ≤ 11
  · have hmem : u ∈ ({9, 10, 11} : Finset ℕ) := by simp; omega
    simp only [hmem, forall_const, h11, ↓reduceIte]
    constructor
    · rintro ⟨⟨h1, h2, h3, -, h5⟩, h6⟩
      refine ⟨h1, h2, h3, ?_, h5⟩
      rw [← hmu h11 _ h1 h2]
      exact h6
    · rintro ⟨h1, h2, h3, h4, h5⟩
      rw [← hmu h11 _ h1 h2] at h4
      exact ⟨⟨h1, h2, h3, by omega, h5⟩, h4⟩
  · have hmem : u ∉ ({9, 10, 11} : Finset ℕ) := by simp; omega
    simp only [hmem, false_imp_iff, and_true, h11, ↓reduceIte, add_zero]

/-- The family `𝒞(u, 16)` as a `Finset`. -/
@[irreducible] private def srS (u : ℕ) : Finset Word := (par u).comp ((par u).h + 1) 0 0

private theorem coe_srS (u : ℕ) (hu1 : 9 ≤ u) (hu2 : u ≤ 13)
    (hmu : u ≤ 11 → ∀ s, lb u < s → s ≤ hb u → fcMinOvershoot u s = mu u s)
    (htop : ∀ s ≤ hb u, barrierRb u s + 16 ≤ ((barrierRb u (hb u) + 16).toNat : ℤ)) :
    (srS u : Set Word) = centralFamily u 16 := by
  rw [srS, Par.coe_comp _ htop, srCentral u hu1 hu2 hmu]

private theorem srMu_spec (u : ℕ) (hu : 9 ≤ u)
    (h : ∀ s ≤ hb u, lb u < s → 1 ≤ barrierRb u s ∧
      16 * 3 ^ s * 2 ^ (3 * u) < (2 ^ (3 * u) - 1) * 2 ^ ((barrierRb u s).toNat + mu u s) ∧
      (mu u s = 0 ∨ ¬ 16 * 3 ^ s * 2 ^ (3 * u) <
        (2 ^ (3 * u) - 1) * 2 ^ ((barrierRb u s).toNat + (mu u s - 1)))) :
    ∀ s, lb u < s → s ≤ hb u → fcMinOvershoot u s = mu u s := fun s h1 h2 =>
  fcMinOvershoot_eq_srMu u s (by omega) (h s h2 h1).1 (h s h2 h1).2.1 (h s h2 h1).2.2

private theorem coe_srS_nine : (srS 9 : Set Word) = centralFamily 9 16 :=
  coe_srS 9 le_rfl (by norm_num) (fun _ => srMu_spec 9 le_rfl (by decide +kernel))
    (by decide +kernel)

private theorem coe_srS_ten : (srS 10 : Set Word) = centralFamily 10 16 :=
  coe_srS 10 (by norm_num) (by norm_num) (fun _ => srMu_spec 10 (by norm_num) (by decide +kernel))
    (by decide +kernel)

private theorem coe_srS_eleven : (srS 11 : Set Word) = centralFamily 11 16 :=
  coe_srS 11 (by norm_num) (by norm_num) (fun _ => srMu_spec 11 (by norm_num) (by decide +kernel))
    (by decide +kernel)

private theorem coe_srS_twelve : (srS 12 : Set Word) = centralFamily 12 16 :=
  coe_srS 12 (by norm_num) (by norm_num) (fun h => absurd h (by norm_num)) (by decide +kernel)

private theorem coe_srS_thirteen : (srS 13 : Set Word) = centralFamily 13 16 :=
  coe_srS 13 (by norm_num) (by norm_num) (fun h => absurd h (by norm_num)) (by decide +kernel)

/-! ### Rounded offsets and the selector -/

private theorem srInc_ceil (pp q j A : ℕ) :
    (⌈(2 : ℚ) ^ ((pp : ℤ) - q) * 3 ^ j * ((2 : ℚ) ^ A)⁻¹⌉ : ℤ) = inc pp q j A := by
  have hx : (2 : ℚ) ^ ((pp : ℤ) - q) * 3 ^ j * ((2 : ℚ) ^ A)⁻¹ =
      ((2 ^ pp * 3 ^ j : ℕ) : ℚ) / ((2 ^ (A + q) : ℕ) : ℚ) := by
    rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast]
    push_cast
    rw [pow_add]
    field_simp
  rw [hx, Int.ceil_eq_iff]
  unfold inc
  generalize hn : 2 ^ pp * 3 ^ j = n
  generalize hD : 2 ^ (A + q) = D
  have hDpos : 0 < D := hD ▸ by positivity
  have h1 := Nat.div_add_mod (n + D - 1) D
  have h2 := Nat.mod_lt (n + D - 1) hDpos
  generalize (n + D - 1) / D = k at h1 h2 ⊢
  have hk1 : D * k < n + D := by omega
  have hk2 : n ≤ D * k := by omega
  have hDq : (0 : ℚ) < D := by exact_mod_cast hDpos
  push_cast
  constructor
  · rw [lt_div_iff₀ hDq]
    have : ((D * k : ℕ) : ℚ) < ((n + D : ℕ) : ℚ) := by exact_mod_cast hk1
    push_cast at this
    linarith
  · rw [div_le_iff₀ hDq]
    have : ((n : ℕ) : ℚ) ≤ ((D * k : ℕ) : ℚ) := by exact_mod_cast hk2
    push_cast at this
    linarith

private theorem roundedOffset_eq_srZ (p : ℤ) (pp q : ℕ) (hp : p = pp - q) (v : Word) :
    roundedOffset p v = (2 : ℚ) ^ (-p) * (srZ (inc pp q) 0 0 v : ℚ) := by
  rw [roundedOffset, srZ_eq_sum]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hp, zero_add, zero_add]
  exact_mod_cast srInc_ceil pp q j (Word.valSum (v.take (j + 1)))

private theorem srSel_upper (z0 z1 d A : ℕ) (h0 : z0 ≤ 1216) (hhi : z1 ≤ hi d A z0) :
    z0 * 2 ^ A + 8 * 3 ^ d * z1 ≤ 1216 * 2 ^ A ∧ z1 ≤ 1024 := by
  have hc : 0 < 8 * 3 ^ d := by positivity
  have hP : 0 < 2 ^ A := by positivity
  unfold hi at hhi
  rw [le_min_iff, Nat.le_div_iff_mul_le hc, Nat.sub_mul] at hhi
  have : z0 * 2 ^ A ≤ 1216 * 2 ^ A := Nat.mul_le_mul_right _ h0
  exact ⟨by rw [mul_comm (8 * 3 ^ d)]; omega, hhi.1⟩

private theorem srSel_lower (z0 z1 d A : ℕ) (hlo : lo d A z0 ≤ z1) :
    192 * 2 ^ A ≤ z0 * 2 ^ A + 8 * 3 ^ d * z1 := by
  have hc : 0 < 8 * 3 ^ d := by positivity
  have hP : 0 < 2 ^ A := by positivity
  unfold lo at hlo
  split_ifs at hlo with h
  · have := Nat.mul_le_mul_right (2 ^ A) h; omega
  · rw [Nat.div_le_iff_le_mul_add_pred hc, Nat.sub_mul] at hlo
    have : z0 * 2 ^ A ≤ 192 * 2 ^ A := Nat.mul_le_mul_right _ (by omega)
    omega

private theorem srSel (v0 v1 v2 v3 v4 : Word)
    (h0 : srZ (inc 9 0) 0 0 v0 ≤ 1216)
    (hlo : lo v0.length (Word.valSum v0) (srZ (inc 9 0) 0 0 v0) ≤ srZ (inc 6 0) 0 0 v1)
    (hhi : srZ (inc 6 0) 0 0 v1 ≤ hi v0.length (Word.valSum v0) (srZ (inc 9 0) 0 0 v0))
    (h2 : srZ (inc 3 0) 0 0 v2 ≤ 128) (h3 : srZ (inc 0 0) 0 0 v3 ≤ 64)
    (h4 : srZ (inc 0 3) 0 0 v4 ≤ 32) :
    fiveBlockSelector v0 v1 v2 v3 v4 := by
  rw [fiveBlockSelector_iff, roundedOffset_eq_srZ 9 9 0 (by norm_num),
    roundedOffset_eq_srZ 6 6 0 (by norm_num), roundedOffset_eq_srZ 3 3 0 (by norm_num),
    roundedOffset_eq_srZ 0 0 0 (by norm_num), roundedOffset_eq_srZ (-3) 0 3 (by norm_num),
    Word.weight]
  generalize srZ (inc 9 0) 0 0 v0 = z0 at h0 hlo hhi
  generalize srZ (inc 6 0) 0 0 v1 = z1 at hlo hhi
  generalize srZ (inc 3 0) 0 0 v2 = z2 at h2
  generalize srZ (inc 0 0) 0 0 v3 = z3 at h3
  generalize srZ (inc 0 3) 0 0 v4 = z4 at h4
  generalize v0.length = d at hlo hhi
  generalize Word.valSum v0 = A at hlo hhi
  have hU := srSel_upper z0 z1 d A h0 hhi
  have hL := srSel_lower z0 z1 d A hlo
  have key : (2 : ℚ) ^ (-(9 : ℤ)) * z0 + 3 ^ d / 2 ^ A * ((2 : ℚ) ^ (-(6 : ℤ)) * z1) =
      ((z0 * 2 ^ A + 8 * 3 ^ d * z1 : ℕ) : ℚ) / (512 * 2 ^ A) := by
    push_cast
    field_simp
    norm_num
    ring
  have hPq : (0 : ℚ) < 512 * 2 ^ A := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [key, le_div_iff₀ hPq]
    have : ((192 * 2 ^ A : ℕ) : ℚ) ≤ ((z0 * 2 ^ A + 8 * 3 ^ d * z1 : ℕ) : ℚ) := by
      exact_mod_cast hL
    push_cast at this ⊢
    linarith
  · rw [key, div_le_iff₀ hPq]
    have : ((z0 * 2 ^ A + 8 * 3 ^ d * z1 : ℕ) : ℚ) ≤ ((1216 * 2 ^ A : ℕ) : ℚ) := by
      exact_mod_cast hU.1
    push_cast at this ⊢
    linarith
  · have : (z1 : ℚ) ≤ 1024 := by exact_mod_cast hU.2
    norm_num
    linarith
  · have : (z2 : ℚ) ≤ 128 := by exact_mod_cast h2
    norm_num
    linarith
  · have : (z3 : ℚ) ≤ 64 := by exact_mod_cast h3
    norm_num
    linarith
  · have : (z4 : ℚ) ≤ 32 := by exact_mod_cast h4
    norm_num
    linarith

/-! ### The computed numbers as sums over the families -/

/-- Shorthand for the accumulated rounded offset `2^p rd_p(v)`, `p = pp - q`. -/
private abbrev srZp (pp q : ℕ) (v : Word) : ℕ := srZ (inc pp q) 0 0 v

private theorem srMass_eq (u : ℕ) :
    mass u = ∑ v ∈ srS u, 2 ^ ((par u).top - Word.valSum v) := by
  rw [mass, srS]
  simpa using (par u).dpRoot_one (fun _ _ => 1)

private theorem srNu_eq (u pp q cap : ℕ) (h : mass u < X0 - 1) :
    nu u pp q cap =
      ∑ v ∈ srS u with srZp pp q v ≤ cap, 2 ^ ((par u).top - Word.valSum v) := by
  unfold nu
  rw [srDig_congr ((par u).dpRoot_pow_modEq X0 (cap + 1) (inc pp q) _) le_rfl]
  simp only [mul_one]
  rw [srDig_sum _ _ _ _ _ _ (by rw [srMass_eq, srS] at h; exact h), srS]
  exact Finset.sum_congr (Finset.filter_congr fun v _ => by simp) fun _ _ => rfl

private theorem srMass_ten_lt : mass 10 < X1 - 1 := by decide +kernel

set_option linter.constructorNameAsVariable false in
private theorem srT_eq (d A z : ℕ) (hz : z ≤ 1216) :
    T d A z = ∑ v ∈ srS 10 with lo d A z ≤ srZp 6 0 v ∧ srZp 6 0 v ≤ hi d A z,
      2 ^ ((par 10).top - Word.valSum v) := by
  unfold T
  split_ifs with h
  · rcases h with h | h
    · omega
    · symm
      refine Finset.sum_eq_zero fun v hv => ?_
      rw [Finset.mem_filter] at hv
      omega
  · unfold NG
    rw [srDig_congr ((par 10).dpRoot_pow_modEq X1 1025 (inc 6 0) _)
      (by unfold hi; omega)]
    simp only [mul_one]
    rw [srDig_sum _ _ _ _ _ _ (by rw [← srS, ← srMass_eq]; exact srMass_ten_lt), srS]

private theorem srT_lt (d A z : ℕ) : T d A z ≤ X1 - 2 := by
  unfold T
  split_ifs
  · exact Nat.zero_le _
  · have := Nat.mod_lt (NG % X1 ^ (hi d A z + 1) / X1 ^ lo d A z)
      (show 0 < X1 - 1 by unfold X1; norm_num)
    unfold dig
    omega

private theorem skipSum_eq (f : ℕ → ℕ) (X : ℕ) :
    ∀ L : List ℕ, skipSum f X L = (L.map fun z => f z * X ^ (1216 - z)).sum
  | [] => rfl
  | z :: L => by
    rw [skipSum, List.map_cons, List.sum_cons, ← skipSum_eq f X L]
    split_ifs with h
    · rw [h, zero_mul, zero_add]
    · rfl

private theorem srSum_range' (g : ℕ → ℕ) : ∀ (a n : ℕ),
    ((List.range' a n).map g).sum = ∑ i ∈ Finset.range n, g (a + i)
  | a, 0 => by simp
  | a, n + 1 => by
    rw [List.range'_succ, List.map_cons, List.sum_cons, srSum_range' g (a + 1) n,
      Finset.sum_range_succ']
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [show a + 1 + i = a + (i + 1) by omega]

private theorem srGeo (X n : ℕ) (hX : 2 ≤ X) (hn : n ≤ 1025) :
    geo X n = ∑ i ∈ Finset.range n, X ^ (1024 - i) := by
  have h := Finset.sum_range_add (fun j => X ^ j) (1025 - n) n
  rw [show 1025 - n + n = 1025 by omega] at h
  have hr : ∑ i ∈ Finset.range n, X ^ (1025 - n + i) = ∑ i ∈ Finset.range n, X ^ (1024 - i) := by
    rw [← Finset.sum_range_reflect (fun i => X ^ (1025 - n + i)) n]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [show 1025 - n + (n - 1 - i) = 1024 - i by omega]
  rw [geo, ← Nat.geomSum_eq hX, ← Nat.geomSum_eq hX, h, ← hr]
  omega

private theorem srF9_eq (d A : ℕ) :
    F9 d A = ∑ z ∈ Finset.range 1217, T d A z * X2 ^ (1216 - z) := by
  have hst1 : 192 ≤ st d A := le_max_left _ _
  have hst2 : st d A ≤ 1217 := max_le (by norm_num) (Nat.sub_le _ _)
  rw [show 1217 = 192 + (st d A - 192) + (1217 - st d A) by omega, Finset.sum_range_add,
    Finset.sum_range_add, F9, skipSum_eq, skipSum_eq, srSum_range', srSum_range',
    srGeo X2 _ (by unfold X2; norm_num) (by omega), Finset.mul_sum]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · exact Finset.sum_congr rfl fun i _ => by rw [zero_add]
  · refine Finset.sum_congr rfl fun i hi' => ?_
    rw [Finset.mem_range] at hi'
    have hz1 : 192 ≤ 192 + i := by omega
    have hz2 : 192 + i < 1217 - m d A := by
      have := lt_max_iff.1 (show 192 + i < st d A by omega)
      omega
    have hmA : 1024 * (8 * 3 ^ d) ≤ m d A * 2 ^ A := by
      unfold m
      generalize 1024 * (8 * 3 ^ d) = N
      generalize hP : 2 ^ A = P
      have hP0 : 0 < P := hP ▸ by positivity
      have h1 := Nat.div_add_mod (N + P - 1) P
      have h2 := Nat.mod_lt (N + P - 1) hP0
      rw [mul_comm]
      omega
    have hhi : hi d A (192 + i) = 1024 := by
      unfold hi
      refine min_eq_left ?_
      rw [Nat.le_div_iff_mul_le (by positivity)]
      calc 1024 * (8 * 3 ^ d) ≤ m d A * 2 ^ A := hmA
        _ ≤ (1216 - (192 + i)) * 2 ^ A := Nat.mul_le_mul_right _ (by omega)
    have hlo : lo d A (192 + i) = 0 := by unfold lo; simp only [hz1, ↓reduceIte]
    have hT : T d A (192 + i) = dig X1 NG 0 1024 := by
      unfold T
      rw [hhi, hlo]
      simp only [show ¬(1216 < 192 + i ∨ 1024 < 0) by omega, ↓reduceIte]
    rw [hT, show 1216 - (192 + i) = 1024 - i by omega]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show 192 + (st d A - 192) + i = st d A + i by omega]


private theorem srSum_prod_le (u n K : ℕ) (f : Word → ℕ → ℕ) (hf : ∀ v z, f v z ≤ K) :
    ∑ x ∈ srS u ×ˢ Finset.range n, 2 ^ ((par u).top - Word.valSum x.1) * f x.1 x.2 ≤
      mass u * n * K := by
  rw [Finset.sum_product, srMass_eq, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun v _ => ?_
  calc ∑ y ∈ Finset.range n, 2 ^ ((par u).top - Word.valSum v) * f v y
      ≤ ∑ y ∈ Finset.range n, 2 ^ ((par u).top - Word.valSum v) * K :=
        Finset.sum_le_sum fun y _ => Nat.mul_le_mul_left _ (hf v y)
    _ = 2 ^ ((par u).top - Word.valSum v) * n * K := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        ring

private theorem srP01_bound : ∑ x ∈ srS 9 ×ˢ Finset.range 1217,
    2 ^ ((par 9).top - Word.valSum x.1) * T x.1.length (Word.valSum x.1) x.2 < X2 - 1 := by
  refine lt_of_le_of_lt (srSum_prod_le 9 1217 (X1 - 2) (fun v z => T v.length (Word.valSum v) z)
    fun v z => srT_lt _ _ _) ?_
  rw [mass_nine]
  unfold X1 X2
  norm_num

private theorem srFilter_diag (s : Finset Word) (z : Word → ℕ) (c : Word → ℕ → ℕ) :
    ∑ x ∈ s ×ˢ Finset.range 1217 with
        1216 ≤ z x.1 + (1216 - x.2) ∧ z x.1 + (1216 - x.2) ≤ 1216, c x.1 x.2 =
      ∑ v ∈ s with z v ≤ 1216, c v (z v) := by
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  have : ∀ y ∈ Finset.range 1217,
      (if 1216 ≤ z v + (1216 - y) ∧ z v + (1216 - y) ≤ 1216 then c v y else 0) =
        if z v = y then c v y else 0 := by
    intro y hy
    rw [Finset.mem_range] at hy
    split_ifs <;> first | rfl | omega
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  split_ifs with h1 h2 h2
  · rfl
  · rw [Finset.mem_range] at h1; omega
  · rw [Finset.mem_range] at h1; omega
  · rfl

private theorem srP01_eq :
    P01 = ∑ v ∈ srS 9 with srZp 9 0 v ≤ 1216,
      2 ^ ((par 9).top - Word.valSum v) * T v.length (Word.valSum v) (srZp 9 0 v) := by
  unfold P01 N9
  rw [srDig_congr ((par 9).dpRoot_pow_modEq X2 1217 (inc 9 0) _) le_rfl]
  have hS : ∑ v ∈ (par 9).comp ((par 9).h + 1) 0 0,
      2 ^ ((par 9).top - Word.valSum v) * X2 ^ srZ (inc 9 0) 0 0 v *
        F9 v.length (Word.valSum v) =
      ∑ x ∈ srS 9 ×ˢ Finset.range 1217,
        (2 ^ ((par 9).top - Word.valSum x.1) * T x.1.length (Word.valSum x.1) x.2) *
          X2 ^ (srZp 9 0 x.1 + (1216 - x.2)) := by
    rw [Finset.sum_product, srS]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [srF9_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [pow_add]
    ring
  rw [hS, srDig_sum _ _ _ _ _ _ srP01_bound]
  exact srFilter_diag (srS 9) (srZp 9 0)
    (fun v z => 2 ^ ((par 9).top - Word.valSum v) * T v.length (Word.valSum v) z)

open scoped ENNReal

private theorem srConcat_valSum (a b c d e : Word) :
    (concatWord ![a, b, c, d, e]).valSum =
      a.valSum + b.valSum + c.valSum + d.valSum + e.valSum := by
  simp [concatWord, List.ofFn_succ, Word.valSum_append]
  ring

private theorem srHalf_pow {A top : ℕ} (h : A ≤ top) :
    (2⁻¹ : ℝ≥0∞) ^ A = ((2 ^ (top - A) : ℕ) : ℝ≥0∞) * 2⁻¹ ^ top := by
  have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  rw [show top = (top - A) + A by omega, pow_add, Nat.add_sub_cancel]
  push_cast
  rw [← mul_assoc, ← mul_pow, h2, one_pow, one_mul]

private theorem srCast (S : Finset Word) (top : ℕ) (w : Word → ℕ)
    (hS : ∀ v ∈ S, Word.valSum v ≤ top) :
    ∑ v ∈ S, (w v : ℝ≥0∞) * 2⁻¹ ^ Word.valSum v =
      ((∑ v ∈ S, 2 ^ (top - Word.valSum v) * w v : ℕ) : ℝ≥0∞) * 2⁻¹ ^ top := by
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [srHalf_pow (hS v hv)]
  push_cast
  ring

private theorem srS_le_top (u : ℕ) : ∀ v ∈ srS u, Word.valSum v ≤ (par u).top := by
  intro v hv
  rw [srS] at hv
  simpa using (par u).le_top_of_mem_comp _ 0 0 v hv

private theorem srTuple_le (S0 S1 S2 S3 S4 : Finset Word)
    (Q : Word → Word → Word → Word → Word → Prop) [∀ a b c d e, Decidable (Q a b c d e)]
    (hQ : ∀ a ∈ S0, ∀ b ∈ S1, ∀ c ∈ S2, ∀ d ∈ S3, ∀ e ∈ S4, Q a b c d e →
      ![a, b, c, d, e] ∈ selectedTuples 5) :
    ∑ e ∈ S4, ∑ d ∈ S3, ∑ c ∈ S2, ∑ a ∈ S0, ∑ b ∈ S1,
      (if Q a b c d e then (2⁻¹ : ℝ≥0∞) ^ a.valSum * 2⁻¹ ^ b.valSum * 2⁻¹ ^ c.valSum *
        2⁻¹ ^ d.valSum * 2⁻¹ ^ e.valSum else 0) ≤
      ∑' t : selectedTuples 5, (2⁻¹ : ℝ≥0∞) ^ (concatWord (t : Fin 5 → Word)).valSum := by
  rw [tsum_subtype (selectedTuples 5) (fun t => (2⁻¹ : ℝ≥0∞) ^ (concatWord t).valSum)]
  set ind := (selectedTuples 5).indicator fun t => (2⁻¹ : ℝ≥0∞) ^ (concatWord t).valSum
  let φ : Word × Word × Word × Word × Word → (Fin 5 → Word) :=
    fun x => ![x.2.2.2.1, x.2.2.2.2, x.2.2.1, x.2.1, x.1]
  have hφ : Set.InjOn φ ↑(S4 ×ˢ S3 ×ˢ S2 ×ˢ S0 ×ˢ S1) := by
    rintro ⟨e, d, c, a, b⟩ _ ⟨e', d', c', a', b'⟩ _ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    simp [φ] at h0 h1 h2 h3 h4
    simp [h0, h1, h2, h3, h4]
  calc _ = ∑ x ∈ S4 ×ˢ S3 ×ˢ S2 ×ˢ S0 ×ˢ S1,
        (if Q x.2.2.2.1 x.2.2.2.2 x.2.2.1 x.2.1 x.1 then
          (2⁻¹ : ℝ≥0∞) ^ x.2.2.2.1.valSum * 2⁻¹ ^ x.2.2.2.2.valSum * 2⁻¹ ^ x.2.2.1.valSum *
            2⁻¹ ^ x.2.1.valSum * 2⁻¹ ^ x.1.valSum else 0) := by
        simp only [Finset.sum_product]
    _ ≤ ∑ x ∈ S4 ×ˢ S3 ×ˢ S2 ×ˢ S0 ×ˢ S1, ind (φ x) := by
        refine Finset.sum_le_sum fun x hx => ?_
        obtain ⟨e, d, c, a, b⟩ := x
        simp only [Finset.mem_product] at hx
        split_ifs with hq
        · have hmem := hQ a hx.2.2.2.1 b hx.2.2.2.2 c hx.2.2.1 d hx.2.1 e hx.1 hq
          simp only [ind, φ, Set.indicator_of_mem hmem, srConcat_valSum, pow_add]
          exact le_rfl
        · exact zero_le
    _ = ∑ t ∈ (S4 ×ˢ S3 ×ˢ S2 ×ˢ S0 ×ˢ S1).image φ, ind t := (Finset.sum_image hφ).symm
    _ ≤ ∑' t, ind t := ENNReal.sum_le_tsum _

private theorem srFactor (S0 S1 S2 S3 S4 : Finset Word) (x : Word → ℝ≥0∞)
    (C : Word → Word → Prop) [∀ a b, Decidable (C a b)]
    (p2 p3 p4 : Word → Prop) [DecidablePred p2] [DecidablePred p3] [DecidablePred p4] :
    (∑ a ∈ S0, ∑ b ∈ S1, if C a b then x a * x b else 0) *
        (∑ c ∈ S2, if p2 c then x c else 0) * (∑ d ∈ S3, if p3 d then x d else 0) *
        (∑ e ∈ S4, if p4 e then x e else 0) =
      ∑ e ∈ S4, ∑ d ∈ S3, ∑ c ∈ S2, ∑ a ∈ S0, ∑ b ∈ S1,
        (if C a b ∧ p2 c ∧ p3 d ∧ p4 e then x a * x b * x c * x d * x e else 0) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : C a b <;> by_cases h2 : p2 c <;> by_cases h3 : p3 d <;> by_cases h4 : p4 e <;>
    simp [h1, h2, h3, h4]

private theorem srSingle (u : ℕ) (p : Word → Prop) [DecidablePred p] :
    ∑ v ∈ srS u, (if p v then (2⁻¹ : ℝ≥0∞) ^ v.valSum else 0) =
      ((∑ v ∈ srS u with p v, 2 ^ ((par u).top - Word.valSum v) : ℕ) : ℝ≥0∞) *
        2⁻¹ ^ (par u).top := by
  rw [← Finset.sum_filter]
  simpa using srCast ((srS u).filter p) (par u).top (fun _ => 1)
    (fun v hv => srS_le_top u v (Finset.mem_of_mem_filter v hv))

private theorem srGeomMass (u : ℕ) :
    geomMass (srS u : Set Word) = (mass u : ℝ≥0∞) * 2⁻¹ ^ (par u).top := by
  rw [geomMass_coe_finset, srMass_eq]
  simpa using srCast (srS u) (par u).top (fun _ => 1) (srS_le_top u)

/-- The joint condition on the first two blocks. -/
private abbrev srC (v0 v1 : Word) : Prop :=
  srZp 9 0 v0 ≤ 1216 ∧ lo v0.length (Word.valSum v0) (srZp 9 0 v0) ≤ srZp 6 0 v1 ∧
    srZp 6 0 v1 ≤ hi v0.length (Word.valSum v0) (srZp 9 0 v0)

private theorem srPair :
    ∑ a ∈ srS 9, ∑ b ∈ srS 10,
      (if srC a b then (2⁻¹ : ℝ≥0∞) ^ a.valSum * 2⁻¹ ^ b.valSum else 0) =
      (P01 : ℝ≥0∞) * 2⁻¹ ^ (par 9).top * 2⁻¹ ^ (par 10).top := by
  have hN : ∀ a, ∑ b ∈ srS 10, (if srC a b then (2⁻¹ : ℝ≥0∞) ^ b.valSum else 0) =
      ((if srZp 9 0 a ≤ 1216 then T a.length (Word.valSum a) (srZp 9 0 a) else 0 : ℕ) :
        ℝ≥0∞) * 2⁻¹ ^ (par 10).top := by
    intro a
    rw [srSingle]
    congr 2
    split_ifs with h
    · rw [srT_eq _ _ _ h]
      exact Finset.sum_congr (Finset.filter_congr fun b _ => by simp [srC, h]) fun _ _ => rfl
    · exact Finset.sum_eq_zero fun b hb => absurd (Finset.mem_filter.1 hb).2.1 h
  have h1 : ∀ a, ∑ b ∈ srS 10,
      (if srC a b then (2⁻¹ : ℝ≥0∞) ^ a.valSum * 2⁻¹ ^ b.valSum else 0) =
      2⁻¹ ^ a.valSum * ∑ b ∈ srS 10, (if srC a b then (2⁻¹ : ℝ≥0∞) ^ b.valSum else 0) := by
    intro a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by split_ifs <;> simp
  simp only [h1, hN]
  have h2 := srCast (srS 9) (par 9).top
    (fun a => if srZp 9 0 a ≤ 1216 then T a.length (Word.valSum a) (srZp 9 0 a) else 0)
    (srS_le_top 9)
  have h3 : ∑ a ∈ srS 9, 2 ^ ((par 9).top - Word.valSum a) *
      (if srZp 9 0 a ≤ 1216 then T a.length (Word.valSum a) (srZp 9 0 a) else 0) = P01 := by
    rw [srP01_eq, Finset.sum_filter]
    exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
  rw [h3] at h2
  rw [← h2, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

private theorem srFinal (m9 m10 m11 m12 m13 P n11 n12 n13 : ℕ)
    (h : m9 * m10 * m11 * m12 * m13 < 2 * (P * n11 * n12 * n13)) :
    (2⁻¹ : ℝ≥0∞) * (1 * ((m9 : ℝ≥0∞) * 2⁻¹ ^ 42) * ((m10 : ℝ≥0∞) * 2⁻¹ ^ 46) *
      ((m11 : ℝ≥0∞) * 2⁻¹ ^ 48) * ((m12 : ℝ≥0∞) * 2⁻¹ ^ 52) * ((m13 : ℝ≥0∞) * 2⁻¹ ^ 54)) <
    (P : ℝ≥0∞) * 2⁻¹ ^ 42 * 2⁻¹ ^ 46 * ((n11 : ℝ≥0∞) * 2⁻¹ ^ 48) *
      ((n12 : ℝ≥0∞) * 2⁻¹ ^ 52) * ((n13 : ℝ≥0∞) * 2⁻¹ ^ 54) := by
  have hl : (2⁻¹ : ℝ≥0∞) * (1 * ((m9 : ℝ≥0∞) * 2⁻¹ ^ 42) * ((m10 : ℝ≥0∞) * 2⁻¹ ^ 46) *
      ((m11 : ℝ≥0∞) * 2⁻¹ ^ 48) * ((m12 : ℝ≥0∞) * 2⁻¹ ^ 52) * ((m13 : ℝ≥0∞) * 2⁻¹ ^ 54)) =
      (((m9 * m10 * m11 * m12 * m13 : ℕ) : ℝ≥0∞) * 2⁻¹) * 2⁻¹ ^ 242 := by
    push_cast
    ring
  have hr : (P : ℝ≥0∞) * 2⁻¹ ^ 42 * 2⁻¹ ^ 46 * ((n11 : ℝ≥0∞) * 2⁻¹ ^ 48) *
      ((n12 : ℝ≥0∞) * 2⁻¹ ^ 52) * ((n13 : ℝ≥0∞) * 2⁻¹ ^ 54) =
      ((P * n11 * n12 * n13 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 242 := by
    push_cast
    ring
  rw [hl, hr]
  refine (ENNReal.mul_lt_mul_iff_left (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))).2 ?_
  rw [← div_eq_mul_inv, ENNReal.div_lt_iff (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
  exact_mod_cast (by omega : m9 * m10 * m11 * m12 * m13 < P * n11 * n12 * n13 * 2)

private theorem srNuE (u pp q cap : ℕ) (h : mass u < X0 - 1) :
    ∑ v ∈ srS u, (if srZp pp q v ≤ cap then (2⁻¹ : ℝ≥0∞) ^ v.valSum else 0) =
      (nu u pp q cap : ℝ≥0∞) * 2⁻¹ ^ (par u).top := by
  rw [srSingle, srNu_eq u pp q cap h]

private theorem srMem (a b c d e : Word) (ha : a ∈ srS 9) (hb : b ∈ srS 10) (hc : c ∈ srS 11)
    (hd : d ∈ srS 12) (he : e ∈ srS 13)
    (hq : srC a b ∧ srZp 3 0 c ≤ 128 ∧ srZp 0 0 d ≤ 64 ∧ srZp 0 3 e ≤ 32) :
    ![a, b, c, d, e] ∈ selectedTuples 5 := by
  have hs := scale_first_six
  simp only [Prod.mk.injEq] at hs
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := hs
  rw [mem_selectedTuples]
  refine ⟨fun j => ?_, fun _ => srSel a b c d e hq.1.1 hq.1.2.1 hq.1.2.2 hq.2.1 hq.2.2.1 hq.2.2.2⟩
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, h0,
      cap_of_lt (show 0 < 32 by norm_num), ← coe_srS_nine, Finset.mem_coe]
    exact ha
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, h1,
      cap_of_lt (show 1 < 32 by norm_num), ← coe_srS_ten, Finset.mem_coe]
    exact hb
  · simp only [Fin.reduceFinMk, Fin.isValue, h2, cap_of_lt (show 2 < 32 by norm_num),
      ← coe_srS_eleven, Finset.mem_coe]
    exact hc
  · simp only [Fin.reduceFinMk, Fin.isValue, h3, cap_of_lt (show 3 < 32 by norm_num),
      ← coe_srS_twelve, Finset.mem_coe]
    exact hd
  · simp only [Fin.reduceFinMk, Fin.isValue, h4, cap_of_lt (show 4 < 32 by norm_num),
      ← coe_srS_thirteen, Finset.mem_coe]
    exact he

end CollatzPosDens.SelectedRatio

namespace CollatzPosDens

open SelectedRatio
open scoped ENNReal

/-- **Mass retained by the selector.** The selected central tuples of length five carry more
than half of the product of the masses of the first five central families:
`∑_{t ∈ 𝔗₅} 2^{-A(ŵ(t))} > ½ ∏_{j<5} 𝐩(𝒞(b_j, K_j))`. -/
@[collatz_pos_dens "lem_s05_selected_ratio"]
theorem half_mul_prod_geomMass_lt_tsum_selectedTuples_five :
    2⁻¹ * ∏ j ∈ Finset.range 5, geomMass (centralFamily (scale j) (cap j)) <
      ∑' t : selectedTuples 5, (2⁻¹ : ℝ≥0∞) ^ (concatWord (t : Fin 5 → Word)).valSum := by
  have hs := scale_first_six
  simp only [Prod.mk.injEq] at hs
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := hs
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, h0, h1, h2, h3, h4,
    cap_of_lt (show 0 < 32 by norm_num), cap_of_lt (show 1 < 32 by norm_num),
    cap_of_lt (show 2 < 32 by norm_num), cap_of_lt (show 3 < 32 by norm_num),
    cap_of_lt (show 4 < 32 by norm_num)]
  rw [← coe_srS_nine, ← coe_srS_ten, ← coe_srS_eleven, ← coe_srS_twelve, ← coe_srS_thirteen,
    srGeomMass, srGeomMass, srGeomMass, srGeomMass, srGeomMass]
  refine lt_of_lt_of_le ?_ (srTuple_le (srS 9) (srS 10) (srS 11) (srS 12) (srS 13)
    (fun a b c d e => srC a b ∧ srZp 3 0 c ≤ 128 ∧ srZp 0 0 d ≤ 64 ∧ srZp 0 3 e ≤ 32)
    fun a ha b hb c hc d hd e he hq => srMem a b c d e ha hb hc hd he hq)
  rw [← srFactor (srS 9) (srS 10) (srS 11) (srS 12) (srS 13) (fun v => 2⁻¹ ^ v.valSum) srC
    (fun v => srZp 3 0 v ≤ 128) (fun v => srZp 0 0 v ≤ 64) (fun v => srZp 0 3 v ≤ 32),
    srPair, srNuE 11 3 0 128 (by rw [mass_eleven]; unfold X0; norm_num),
    srNuE 12 0 0 64 (by rw [mass_twelve]; unfold X0; norm_num),
    srNuE 13 0 3 32 (by rw [mass_thirteen]; unfold X0; norm_num)]
  have t9 : (par 9).top = 42 := by decide +kernel
  have t10 : (par 10).top = 46 := by decide +kernel
  have t11 : (par 11).top = 48 := by decide +kernel
  have t12 : (par 12).top = 52 := by decide +kernel
  have t13 : (par 13).top = 54 := by decide +kernel
  rw [t9, t10, t11, t12, t13]
  refine srFinal _ _ _ _ _ _ _ _ _ ?_
  rw [mass_nine, mass_ten, mass_eleven, mass_twelve, mass_thirteen, P01_eq, nu_eleven,
    nu_twelve, nu_thirteen]
  norm_num

end CollatzPosDens
