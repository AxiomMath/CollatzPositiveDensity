/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHoldMass
public import CollatzPosDens.Renewal.RnListTiltSplit

/-!
# Affine barriers for hold lists

Let `X, y > 0` be real, `N ∈ ℕ`, `T > 0`, and let `Λ` be real with `𝖦(X, y) ≤ Λ`, where `𝖦` is
the joint generating function of a hold. Then the hold lists `h ∈ 𝒫^N` whose tilted partial
weight `X^{j(h_1 + ⋯ + h_u)} y^{l(h_1 + ⋯ + h_u)}` crosses the affine barrier `T Λ^u` at some
`1 ≤ u ≤ N` have total `η^{⊗N}`-mass at most `1 / T`.

This is a maximal inequality for the nonnegative supermartingale
`u ↦ X^{j(h_1 + ⋯ + h_u)} y^{l(h_1 + ⋯ + h_u)} / 𝖦(X, y)^u`. Write
`𝗐(x) = X^{j(x)} y^{l(x)}` and `G = 𝖦(X, y)`, which is positive and at most `Λ`. Splitting the
event according to the least crossing time `u`, the hold lists first crossing at `u` are those
whose prefix `(h_1, …, h_u)` lies in a set `E_u ⊆ 𝒫^u`, on which `1 ≤ 𝗐(g_1 + ⋯ + g_u) / (T G^u)`.
Marginalising the last `N - u` steps and splitting off the tail of the tilted sum, the mass
of the `u`-th piece is at most `(T G^N)⁻¹` times the tilted sum
`∑ η^{⊗N}(h) 𝗐(h_1 + ⋯ + h_N)` over the hold lists with prefix in `E_u`. These index sets are
disjoint, and the full tilted sum is `G^N`.

## Main results

* `CollatzPosDens.tsum_ofReal_holdListLaw_affine_barrier`: the bound in `[0, ∞]`.
* `CollatzPosDens.tsum_holdListLaw_affine_barrier`: the bound for the real series.

## Implementation notes

A hold list is a tuple `h : Fin N → ℕ × ℤ` with `1 ≤ j(h_i)` for every `i`, and the coordinates of
the partial sum `h_1 + ⋯ + h_u` are the sums of the coordinates of the `h_i` with `i < u` (indices
from `0`). The positivity of `𝖦(X, y)` is derived from the total mass `1` of `η` on `𝒫` rather
than from the single term `η(1, 4) X y^4`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The partial sums of a tuple over `i < k` agree for the tuple and for its prefix of length
`u ≥ k`. -/
private lemma sum_take_filter_lt {α M : Type*} [AddCommMonoid M] {u N k : ℕ} (hu : u ≤ N)
    (hk : k ≤ u) (f : Fin N → α) (c : α → M) :
    ∑ i : Fin u with i.val < k, c (Fin.take u hu f i) = ∑ i : Fin N with i.val < k, c (f i) := by
  refine Finset.sum_bij (fun i _ ↦ Fin.castLE hu i) (by simp) (fun a _ b _ h ↦ ?_)
    (fun b hb ↦ ?_) (fun i _ ↦ by simp [Fin.take])
  · exact Fin.castLE_injective hu h
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact ⟨⟨b, by omega⟩, by simpa using hb, rfl⟩

private lemma tsum_subtype_setOf {β : Type*} (p : β → Prop) (f : β → ℝ≥0∞) :
    ∑' x : {x // p x}, f x = ∑' x, {x | p x}.indicator f x :=
  tsum_subtype {x | p x} f

private lemma le_inv_of_mul_le_self {a G S : ℝ≥0∞} (hG0 : G ≠ 0) (hGtop : G ≠ ∞)
    (h : a * G * S ≤ G) : S ≤ a⁻¹ := by
  rw [ENNReal.le_inv_iff_mul_le, mul_comm]
  have h' : G * (a * S) ≤ G * 1 := by rw [mul_one, ← mul_assoc, mul_comm G]; exact h
  exact (ENNReal.mul_le_mul_iff_right hG0 hGtop).1 h'

private lemma sum_filter_lt_self {M : Type*} [AddCommMonoid M] {u : ℕ} (f : Fin u → M) :
    ∑ i : Fin u with i.val < u, f i = ∑ i, f i := by
  rw [Finset.filter_true_of_mem (fun i _ ↦ i.2)]

/-- The barrier `T Λ^k` is crossed at time `k` by the tuple `g`. -/
private def BarrierHit (X y T Λ : ℝ) {M : ℕ} (g : Fin M → ℕ × ℤ) (k : ℕ) : Prop :=
  T * Λ ^ k ≤ X ^ (∑ i : Fin M with i.val < k, (g i).1) *
    y ^ (∑ i : Fin M with i.val < k, (g i).2)

private lemma barrierHit_take {X y T Λ : ℝ} {u N k : ℕ} (hu : u ≤ N) (hk : k ≤ u)
    (h : Fin N → ℕ × ℤ) :
    BarrierHit X y T Λ (Fin.take u hu h) k ↔ BarrierHit X y T Λ h k := by
  unfold BarrierHit
  rw [sum_take_filter_lt hu hk h Prod.fst, sum_take_filter_lt hu hk h Prod.snd]

/-- The prefixes of length `u ≥ 1` that cross the barrier first at time `u`. -/
private def firstHit (X y T Λ : ℝ) (u : ℕ) : Set (Fin u → ℕ × ℤ) :=
  {g | 1 ≤ u ∧ BarrierHit X y T Λ g u ∧ ∀ k, 1 ≤ k → k < u → ¬ BarrierHit X y T Λ g k}

/-- The tilted weight `η^{⊗M}(g) X^{j(g_1 + ⋯ + g_M)} y^{l(g_1 + ⋯ + g_M)}` in `[0, ∞]`. -/
private noncomputable def tiltW (X y : ℝ) {M : ℕ} (g : Fin M → ℕ × ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (holdListLaw g * X ^ (∑ i, (g i).1) * y ^ (∑ i, (g i).2))

private lemma holdJointPgf_one_one : holdJointPgf 1 1 = 1 := by
  rw [holdJointPgf_eq_tsum_succ]
  simp only [one_pow, one_zpow, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ holdLaw_nonneg _ _)
    hasSum_holdLaw_bkPoints_succ.summable, hasSum_holdLaw_bkPoints_succ.tsum_eq,
    ENNReal.ofReal_one]

private lemma holdJointPgf_ne_zero {X y : ℝ} (hX : 0 < X) (hy : 0 < y) :
    holdJointPgf X y ≠ 0 := by
  intro h0
  rw [holdJointPgf_eq_tsum_succ, ENNReal.tsum_eq_zero] at h0
  have hz : ∀ x : ℕ × ℤ, holdLaw (x.1 + 1) x.2 = 0 := fun x ↦ by
    have h1 := ENNReal.ofReal_eq_zero.1 (h0 x)
    have hp : 0 < X ^ (x.1 + 1) * y ^ x.2 := mul_pos (pow_pos hX _) (zpow_pos hy _)
    rw [mul_assoc] at h1
    exact le_antisymm (nonpos_of_mul_nonpos_left h1 hp) (holdLaw_nonneg _ _)
  have h1 := hasSum_holdLaw_bkPoints_succ
  simp only [hz] at h1
  exact one_ne_zero (h1.unique hasSum_zero)

/-- The `η^{⊗N}`-mass of the hold lists with prefix in `E`, as a sum of `η^{⊗u}` over `E`. -/
private lemma tsum_ofReal_holdListLaw_take {u N : ℕ} (hu : u ≤ N) (E : Set (Fin u → ℕ × ℤ)) :
    ∑' h : {h : Fin N → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ Fin.take u hu h ∈ E},
      ENNReal.ofReal (holdListLaw h.1) =
      ∑' g : {g : Fin u → ℕ × ℤ // (∀ i, 1 ≤ (g i).1) ∧ g ∈ E},
        ENNReal.ofReal (holdListLaw g.1) := by
  have := tsum_holdListLaw_tilt_take hu zero_le_one one_pos E
  simpa only [one_pow, one_zpow, mul_one, one_mul, holdJointPgf_one_one] using this

/-- **Affine barriers for hold lists**, in `[0, ∞]`. Let `X, y > 0`, `N ∈ ℕ`, `T > 0`, and
`𝖦(X, y) ≤ Λ`. Then the `η^{⊗N}`-mass of the hold lists `h ∈ 𝒫^N` with
`X^{j(h_1 + ⋯ + h_u)} y^{l(h_1 + ⋯ + h_u)} ≥ T Λ^u` for some `1 ≤ u ≤ N` is at most `1 / T`. -/
@[collatz_pos_dens "lem_c3_affine_barrier"]
theorem tsum_ofReal_holdListLaw_affine_barrier {X y T Λ : ℝ} (hX : 0 < X) (hy : 0 < y)
    (N : ℕ) (hT : 0 < T) (hG : holdJointPgf X y ≤ ENNReal.ofReal Λ) :
    ∑' h : {h : Fin N → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ ∃ u ∈ Finset.Icc 1 N,
        T * Λ ^ u ≤ X ^ (∑ i : Fin N with i.val < u, (h i).1) *
          y ^ (∑ i : Fin N with i.val < u, (h i).2)},
      ENNReal.ofReal (holdListLaw h.1) ≤ ENNReal.ofReal (1 / T) := by
  set G := holdJointPgf X y with hGdef
  have hG0 : G ≠ 0 := holdJointPgf_ne_zero hX hy
  have hGtop : G ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hG
  have hΛ : 0 ≤ Λ := by
    by_contra hneg
    exact hG0 (le_antisymm (hG.trans (ENNReal.ofReal_of_nonpos (by linarith)).le) bot_le)
  let A : Fin (N + 1) → Set (Fin N → ℕ × ℤ) := fun u ↦
    {h | (∀ i, 1 ≤ (h i).1) ∧ Fin.take u (Nat.lt_succ_iff.1 u.2) h ∈ firstHit X y T Λ u}
  let η' : (Fin N → ℕ × ℤ) → ℝ≥0∞ := fun h ↦ ENNReal.ofReal (holdListLaw h)
  have hdisj : ∀ h u v, h ∈ A u → h ∈ A v → u = v := by
    intro h u v hu hv
    by_contra hne
    wlog hlt : u < v generalizing u v
    · exact this v u hv hu (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
    obtain ⟨-, hu1, hhu, -⟩ := hu
    obtain ⟨-, -, -, hnv⟩ := hv
    have hle : (u : ℕ) ≤ v := hlt.le
    refine hnv u hu1 hlt ?_
    rw [barrierHit_take _ hle]
    exact (barrierHit_take _ le_rfl h).1 hhu
  have hcover : ∀ h : Fin N → ℕ × ℤ, (∀ i, 1 ≤ (h i).1) → (∃ u ∈ Finset.Icc 1 N,
      BarrierHit X y T Λ h u) → ∃ u, h ∈ A u := by
    intro h hP hex
    classical
    have hex' : ∃ u, 1 ≤ u ∧ u ≤ N ∧ BarrierHit X y T Λ h u := by
      obtain ⟨u, hu, hh⟩ := hex
      exact ⟨u, (Finset.mem_Icc.1 hu).1, (Finset.mem_Icc.1 hu).2, hh⟩
    obtain ⟨h1, hN, hh⟩ := Nat.find_spec hex'
    refine ⟨⟨Nat.find hex', Nat.lt_succ_of_le hN⟩, hP, h1, ?_, fun k hk1 hk ↦ ?_⟩
    · exact (barrierHit_take _ le_rfl h).2 hh
    · rw [barrierHit_take _ hk.le]
      exact fun hk' ↦ Nat.find_min hex' hk ⟨hk1, by omega, hk'⟩
  have hpiece : ∀ u : Fin (N + 1), ENNReal.ofReal T * G ^ N * ∑' h, (A u).indicator η' h ≤
      ∑' h, (A u).indicator (tiltW X y) h := by
    intro u
    have hu := Nat.lt_succ_iff.1 u.2
    have hL := tsum_ofReal_holdListLaw_take hu (firstHit X y T Λ u)
    have hW := tsum_holdListLaw_tilt_take hu hX.le hy (firstHit X y T Λ u)
    have e1 : ∑' h, (A u).indicator η' h = ∑' h : {h : Fin N → ℕ × ℤ //
        (∀ i, 1 ≤ (h i).1) ∧ Fin.take u hu h ∈ firstHit X y T Λ u},
        ENNReal.ofReal (holdListLaw h.1) := (tsum_subtype_setOf _ η').symm
    have e2 : ∑' h, (A u).indicator (tiltW X y) h = ∑' h : {h : Fin N → ℕ × ℤ //
        (∀ i, 1 ≤ (h i).1) ∧ Fin.take u hu h ∈ firstHit X y T Λ u},
        tiltW X y h.1 := (tsum_subtype_setOf _ _).symm
    rw [e1, e2, hL, show ∑' h : {h : Fin N → ℕ × ℤ //
        (∀ i, 1 ≤ (h i).1) ∧ Fin.take u hu h ∈ firstHit X y T Λ u}, tiltW X y h.1 = _ from hW,
      ← hGdef,
      show G ^ N = G ^ (N - u) * G ^ (u : ℕ) by rw [← pow_add, Nat.sub_add_cancel hu]]
    calc ENNReal.ofReal T * (G ^ (N - u) * G ^ (u : ℕ)) *
          ∑' g : {g : Fin u → ℕ × ℤ // (∀ i, 1 ≤ (g i).1) ∧ g ∈ firstHit X y T Λ u},
            ENNReal.ofReal (holdListLaw g.1)
        = G ^ (N - u) * ∑' g : {g : Fin u → ℕ × ℤ //
            (∀ i, 1 ≤ (g i).1) ∧ g ∈ firstHit X y T Λ u},
            ENNReal.ofReal T * G ^ (u : ℕ) * ENNReal.ofReal (holdListLaw g.1) := by
          rw [ENNReal.tsum_mul_left]; ring
      _ ≤ _ := by
          gcongr with g
          obtain ⟨-, -, hhit, -⟩ := g.2
          unfold BarrierHit at hhit
          rw [sum_filter_lt_self, sum_filter_lt_self] at hhit
          have hw : 0 ≤ X ^ (∑ i, (g.1 i).1) * y ^ (∑ i, (g.1 i).2) :=
            mul_nonneg (pow_nonneg hX.le _) (zpow_nonneg hy.le _)
          calc ENNReal.ofReal T * G ^ (u : ℕ) * ENNReal.ofReal (holdListLaw g.1)
              ≤ ENNReal.ofReal T * ENNReal.ofReal Λ ^ (u : ℕ) *
                  ENNReal.ofReal (holdListLaw g.1) := by gcongr
            _ = ENNReal.ofReal (T * Λ ^ (u : ℕ)) * ENNReal.ofReal (holdListLaw g.1) := by
                rw [ENNReal.ofReal_mul hT.le, ENNReal.ofReal_pow hΛ]
            _ ≤ ENNReal.ofReal (X ^ (∑ i, (g.1 i).1) * y ^ (∑ i, (g.1 i).2)) *
                  ENNReal.ofReal (holdListLaw g.1) := by gcongr
            _ = tiltW X y g.1 := by
                rw [tiltW, ← ENNReal.ofReal_mul hw, mul_comm, mul_assoc]
  have htotal : ∑' h : Fin N → ℕ × ℤ, {h | ∀ i, 1 ≤ (h i).1}.indicator (tiltW X y) h = G ^ N := by
    have h0 := tsum_holdListLaw_tilt_take (Nat.zero_le N) hX.le hy Set.univ
    rw [Nat.sub_zero] at h0
    have e : ∑' h : {h : Fin N → ℕ × ℤ //
        (∀ i, 1 ≤ (h i).1) ∧ Fin.take 0 (Nat.zero_le N) h ∈ Set.univ}, tiltW X y h.1 =
        ∑' h : {h : Fin N → ℕ × ℤ // ∀ i, 1 ≤ (h i).1}, tiltW X y h.1 :=
      (Equiv.subtypeEquivRight (p := fun h : Fin N → ℕ × ℤ ↦
        (∀ i, 1 ≤ (h i).1) ∧ Fin.take 0 (Nat.zero_le N) h ∈ Set.univ)
        (q := fun h ↦ ∀ i, 1 ≤ (h i).1) (fun h ↦ by simp)).tsum_eq (fun h ↦ tiltW X y h.1)
    rw [← tsum_subtype_setOf (fun h : Fin N → ℕ × ℤ ↦ ∀ i, 1 ≤ (h i).1) (tiltW X y), ← e]
    refine h0.trans ?_
    rw [tsum_eq_single (⟨Fin.elim0, fun i ↦ i.elim0, Set.mem_univ _⟩ :
      {g : Fin 0 → ℕ × ℤ // (∀ i, 1 ≤ (g i).1) ∧ g ∈ Set.univ})
      (fun g hg ↦ (hg (Subsingleton.elim _ _)).elim)]
    simp [hGdef]
  have hmain : ENNReal.ofReal T * G ^ N *
      ∑' h : {h : Fin N → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ ∃ u ∈ Finset.Icc 1 N,
        T * Λ ^ u ≤ X ^ (∑ i : Fin N with i.val < u, (h i).1) *
          y ^ (∑ i : Fin N with i.val < u, (h i).2)},
      ENNReal.ofReal (holdListLaw h.1) ≤ G ^ N := by
    rw [tsum_subtype_setOf (fun h : Fin N → ℕ × ℤ ↦ (∀ i, 1 ≤ (h i).1) ∧ ∃ u ∈ Finset.Icc 1 N,
        T * Λ ^ u ≤ X ^ (∑ i : Fin N with i.val < u, (h i).1) *
          y ^ (∑ i : Fin N with i.val < u, (h i).2)) η']
    calc ENNReal.ofReal T * G ^ N * ∑' h, Set.indicator _ η' h
        ≤ ENNReal.ofReal T * G ^ N * ∑' h, ∑ u, (A u).indicator η' h := by
          gcongr with h
          by_cases hh : h ∈ {h : Fin N → ℕ × ℤ | (∀ i, 1 ≤ (h i).1) ∧ ∃ u ∈ Finset.Icc 1 N,
              T * Λ ^ u ≤ X ^ (∑ i : Fin N with i.val < u, (h i).1) *
                y ^ (∑ i : Fin N with i.val < u, (h i).2)}
          · obtain ⟨u, hu⟩ := hcover h hh.1 hh.2
            rw [Set.indicator_of_mem hh]
            calc η' h = (A u).indicator η' h := (Set.indicator_of_mem hu _).symm
              _ ≤ _ := Finset.single_le_sum (f := fun v ↦ (A v).indicator η' h)
                (fun _ _ ↦ zero_le) (Finset.mem_univ u)
          · rw [Set.indicator_of_notMem hh]
            exact zero_le
      _ = ∑ u, ENNReal.ofReal T * G ^ N * ∑' h, (A u).indicator η' h := by
          rw [Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable), Finset.mul_sum]
      _ ≤ ∑ u, ∑' h, (A u).indicator (tiltW X y) h := Finset.sum_le_sum fun u _ ↦ hpiece u
      _ = ∑' h, ∑ u, (A u).indicator (tiltW X y) h :=
          (Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)).symm
      _ ≤ ∑' h, {h : Fin N → ℕ × ℤ | ∀ i, 1 ≤ (h i).1}.indicator (tiltW X y) h := by
          gcongr with h
          by_cases hh : ∃ u, h ∈ A u
          · obtain ⟨u, hu⟩ := hh
            rw [Finset.sum_eq_single u (fun v _ hv ↦ Set.indicator_of_notMem
              (fun hv' ↦ hv (hdisj h v u hv' hu)) _) (by simp),
              Set.indicator_of_mem hu,
              Set.indicator_of_mem (show h ∈ {h : Fin N → ℕ × ℤ | ∀ i, 1 ≤ (h i).1} from hu.1)]
          · simp only [not_exists] at hh
            simp [Set.indicator_of_notMem (hh _)]
      _ = G ^ N := htotal
  rw [one_div, ENNReal.ofReal_inv_of_pos hT]
  exact le_inv_of_mul_le_self (pow_ne_zero _ hG0) (ENNReal.pow_ne_top hGtop) hmain

/-- **Affine barriers for hold lists.** Let `X, y > 0`, `N ∈ ℕ`, `T > 0`, and `𝖦(X, y) ≤ Λ`.
Then `∑ η^{⊗N}(h) ≤ 1 / T`, the sum running over the hold lists `h ∈ 𝒫^N` with
`X^{j(h_1 + ⋯ + h_u)} y^{l(h_1 + ⋯ + h_u)} ≥ T Λ^u` for some `1 ≤ u ≤ N`. -/
@[collatz_pos_dens "lem_c3_affine_barrier"]
theorem tsum_holdListLaw_affine_barrier {X y T Λ : ℝ} (hX : 0 < X) (hy : 0 < y)
    (N : ℕ) (hT : 0 < T) (hG : holdJointPgf X y ≤ ENNReal.ofReal Λ) :
    ∑' h : {h : Fin N → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ ∃ u ∈ Finset.Icc 1 N,
        T * Λ ^ u ≤ X ^ (∑ i : Fin N with i.val < u, (h i).1) *
          y ^ (∑ i : Fin N with i.val < u, (h i).2)},
      holdListLaw h.1 ≤ 1 / T := by
  have h := tsum_ofReal_holdListLaw_affine_barrier hX hy N hT hG
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (by positivity)] at this
  simpa only [ENNReal.toReal_ofReal (holdListLaw_nonneg _)] using this

end CollatzPosDens
