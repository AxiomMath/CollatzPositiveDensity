/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3Eprime
public import CollatzPosDens.Case3.C3Exc
public import CollatzPosDens.Case3.C3HorSmall
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.Renewal.RnListHorTail
public import CollatzPosDens.Renewal.RnListMarginal
public import CollatzPosDens.Renewal.RnListVerTail
public import CollatzPosDens.Renewal.RnOvershootTail
public import CollatzPosDens.Renewal.RnThreefifthsTail
public import CollatzPosDens.StoppingTrace.TrFreshMarginal

/-!
# Mass of the exceptional event

Let `J = ⌊n/2⌋`, `G ∈ ℕ` with `G ≥ 2^160`, `v ≤ J`, `X = 136 (v + 1)` and let `s` be a real
number with `4096 X ≤ s` and `s^2 < 2G`. Then the exceptional event of the fresh law has mass
`μ_{e,G}(Ex_{e,G,v,X}) ≤ 1/s + Exc(v)`.

The event `Ex_{e,G,v,X}` is the union of four events, each depending either on the displacement
`x = (r, ℓ)` of the first passage alone, or on the block points `h = (bpt(β¹), …, bpt(βᵛ))` of
the first `v` blocks alone. By the displacement marginal of the fresh law, the mass of an event
`{(x, h) ∈ S}` is `∑_x F_G(x) ∑_{h ∈ 𝒫^v} η^{⊗v}(h) 1_S(x, h)`. As `F_G` and `η^{⊗v}` have total
mass at most `1`, the four masses are bounded by
* (i) `ℓ - G ≥ X`: the overshoot tail, `9 (25/27)^X`;
* (ii) `∑_{k ≤ v} l(βᵏ) ≥ X`: the vertical tail of `η^{⊗v}`, `8^v (25/27)^X` (and `0` if `v = 0`);
* (iii) `|r - G/4| ≥ G^{3/5}`: the `G^{3/5}`-tail of `F_G`, `2^55 exp(-G^{1/5}/65536)`, which is
  less than `(2G)^{-1/2} < 1/s`;
* (iv) `∑_{k ≤ v} j(βᵏ) ≥ G^{3/5}`: the horizontal tail of `η^{⊗v}`, `exp(v/2 - G^{3/5}/16)`,
  which is at most `e^{-14(v+1)}` since `G^{3/5} > s/2 ≥ 2048 X` (and `0` if `v = 0`).
Adding up gives `1/s + Exc(v)`.

## Main results

* `CollatzPosDens.tsum_trFreshLaw_c3Exceptional_le`: the mass bound, as a sum in `[0, ∞]`.
* `CollatzPosDens.summable_trFreshLaw_c3Exceptional`: the fresh law is summable on
  the exceptional event.
* `CollatzPosDens.tsum_trFreshLaw_c3Exceptional_le_real`: the mass bound, as a real sum.

## Implementation notes

The mass `μ_{e,G}(Ex_{e,G,v,X})` is the unconditional sum over the subtype of the event of
`ENNReal.ofReal (trFreshLaw n e G a)`, as in the displacement marginal of the fresh law; this
form makes no summability assumption, and the real-valued form follows. The statements take
`X = 136 (v + 1)` explicitly, and they hold without the hypothesis `e ∈ 𝒫`. In event (iv) the
horizontal tail is applied with the real threshold `10 G^{3/5}`, with no integer ceiling.

## References

* [Mazur, *Collatz positive density*], §10.3.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal
open Real

/-- The sum over the first `v` entries of a list, as a sum over `Fin v`. -/
private lemma c3EprimeMass_sum_take {α : Type*} (f : α → ℤ) (β : List α) {v : ℕ}
    (hv : v ≤ β.length) :
    ((β.take v).map f).sum = ∑ i : Fin v, f (β[(i : ℕ)]'(lt_of_lt_of_le i.2 hv)) := by
  have h : β.take v = List.ofFn fun i : Fin v ↦ β[(i : ℕ)]'(lt_of_lt_of_le i.2 hv) := by
    apply List.ext_getElem
    · simp [hv]
    · intro i h1 h2
      simp
  rw [h, List.map_ofFn, List.sum_ofFn]
  rfl

/-- Event (i): the overshoot `ℓ - G ≥ X` has `F_G`-mass less than `9 (25/27)^X`. -/
private lemma c3EprimeMass_overshoot {G X : ℕ} (hG : 64 ≤ G) (hX : 1 ≤ X) :
    ∑' x : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw G ((x.1 : ℤ), x.2)) *
        {x : ℕ × ℤ | (X : ℝ) ≤ (x.2 : ℝ) - G}.indicator 1 x ≤
      ENNReal.ofReal (9 * (25 / 27) ^ X) := by
  rw [ENNReal.tsum_prod (f := fun (r : ℕ) (ℓ : ℤ) ↦ ENNReal.ofReal (firstPassageLaw G (r, ℓ)) *
    {x : ℕ × ℤ | (X : ℝ) ≤ (x.2 : ℝ) - G}.indicator 1 (r, ℓ))]
  have h : ∀ r : ℕ, ∑' ℓ : ℤ, ENNReal.ofReal (firstPassageLaw G (r, ℓ)) *
      {x : ℕ × ℤ | (X : ℝ) ≤ (x.2 : ℝ) - G}.indicator 1 (r, ℓ) =
      ∑' ℓ : {ℓ : ℤ // (G : ℤ) + X ≤ ℓ}, ENNReal.ofReal (firstPassageLaw G (((r : ℕ) : ℤ), ℓ)) := by
    intro r
    refine Eq.trans (tsum_congr fun ℓ ↦ ?_) (tsum_subtype {ℓ : ℤ | (G : ℤ) + X ≤ ℓ}
      (fun ℓ ↦ ENNReal.ofReal (firstPassageLaw G (((r : ℕ) : ℤ), ℓ)))).symm
    have hiff : (X : ℝ) ≤ (ℓ : ℝ) - G ↔ (G : ℤ) + X ≤ ℓ := by
      rw [← Int.cast_le (R := ℝ)]
      push_cast
      constructor <;> intro <;> linarith
    by_cases hℓ : (G : ℤ) + X ≤ ℓ
    · rw [Set.indicator_of_mem (show ((r, ℓ) : ℕ × ℤ) ∈ {x : ℕ × ℤ | (X : ℝ) ≤ (x.2 : ℝ) - G}
        from hiff.2 hℓ), Set.indicator_of_mem (show ℓ ∈ {ℓ : ℤ | (G : ℤ) + X ≤ ℓ} from hℓ),
        Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem (show ((r, ℓ) : ℕ × ℤ) ∉ {x : ℕ × ℤ | (X : ℝ) ≤ (x.2 : ℝ) - G}
        from fun h1 ↦ hℓ (hiff.1 h1)),
        Set.indicator_of_notMem (show ℓ ∉ {ℓ : ℤ | (G : ℤ) + X ≤ ℓ} from hℓ), mul_zero]
  simp_rw [h]
  calc _ ≤ ∑' r : ℤ, ∑' ℓ : {ℓ : ℤ // (G : ℤ) + X ≤ ℓ},
        ENNReal.ofReal (firstPassageLaw G (r, ℓ)) :=
        ENNReal.tsum_comp_le_tsum_of_injective Nat.cast_injective
          (fun r : ℤ ↦ ∑' ℓ : {ℓ : ℤ // (G : ℤ) + X ≤ ℓ}, ENNReal.ofReal (firstPassageLaw G (r, ℓ)))
    _ ≤ _ := (tsum_firstPassageLaw_overshoot_lt G X hG hX).le

/-- Event (iii): `|r - G/4| ≥ G^{3/5}` has `F_G`-mass at most `2^55 exp(-G^{1/5}/65536)`. -/
private lemma c3EprimeMass_threeFifths {G : ℕ} (hG : 1 ≤ G) :
    ∑' x : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw G ((x.1 : ℤ), x.2)) *
        {x : ℕ × ℤ | (G : ℝ) ^ ((3 : ℝ) / 5) ≤ |(x.1 : ℝ) - (G : ℝ) / 4|}.indicator 1 x ≤
      ENNReal.ofReal (2 ^ 55 * exp (-((G : ℝ) ^ (1 / 5 : ℝ) / 65536))) := by
  set S : Set ℤ := {r : ℤ | (G : ℝ) ^ ((3 : ℝ) / 5) ≤ |(r : ℝ) - (G : ℝ) / 4|} with hS
  set f : ℤ → ℝ≥0∞ := fun r ↦ ∑' ℓ : ℤ, ENNReal.ofReal (firstPassageLaw G (r, ℓ)) with hf
  rw [ENNReal.tsum_prod (f := fun (r : ℕ) (ℓ : ℤ) ↦ ENNReal.ofReal (firstPassageLaw G (r, ℓ)) *
    {x : ℕ × ℤ | (G : ℝ) ^ ((3 : ℝ) / 5) ≤ |(x.1 : ℝ) - (G : ℝ) / 4|}.indicator 1 (r, ℓ))]
  have h : ∀ r : ℕ, ∑' ℓ : ℤ, ENNReal.ofReal (firstPassageLaw G (r, ℓ)) *
      {x : ℕ × ℤ | (G : ℝ) ^ ((3 : ℝ) / 5) ≤ |(x.1 : ℝ) - (G : ℝ) / 4|}.indicator 1 (r, ℓ) =
      S.indicator f ((r : ℕ) : ℤ) := by
    intro r
    by_cases hr : (G : ℝ) ^ ((3 : ℝ) / 5) ≤ |(r : ℝ) - (G : ℝ) / 4|
    · have hr' : ((r : ℕ) : ℤ) ∈ S := by
        simpa only [hS, Set.mem_ofPred_eq, Int.cast_natCast] using hr
      rw [Set.indicator_of_mem hr', hf]
      refine tsum_congr fun ℓ ↦ ?_
      rw [Set.indicator_of_mem (show ((r, ℓ) : ℕ × ℤ) ∈ {x : ℕ × ℤ | (G : ℝ) ^ ((3 : ℝ) / 5) ≤
        |(x.1 : ℝ) - (G : ℝ) / 4|} from hr), Pi.one_apply, mul_one]
    · have hr' : ((r : ℕ) : ℤ) ∉ S := by
        simpa only [hS, Set.mem_ofPred_eq, Int.cast_natCast] using hr
      rw [Set.indicator_of_notMem hr']
      refine ENNReal.tsum_eq_zero.2 fun ℓ ↦ ?_
      rw [Set.indicator_of_notMem (show ((r, ℓ) : ℕ × ℤ) ∉ {x : ℕ × ℤ | (G : ℝ) ^ ((3 : ℝ) / 5) ≤
        |(x.1 : ℝ) - (G : ℝ) / 4|} from hr), mul_zero]
  simp_rw [h]
  have hF := summable_firstPassageLaw G
  calc _ ≤ ∑' r : ℤ, S.indicator f r :=
        ENNReal.tsum_comp_le_tsum_of_injective Nat.cast_injective (S.indicator f)
    _ = ∑' r : S, f r := (tsum_subtype S f).symm
    _ = ∑' r : S, ENNReal.ofReal (∑' ℓ : ℤ, firstPassageLaw G (r, ℓ)) := by
        refine tsum_congr fun r ↦ ?_
        rw [hf, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ firstPassageLaw_nonneg _ _)
          (hF.prod_factor r.1)]
    _ = ENNReal.ofReal (∑' r : S, ∑' ℓ : ℤ, firstPassageLaw G (r, ℓ)) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun _ ↦ tsum_nonneg fun _ ↦ firstPassageLaw_nonneg _ _) (hF.prod.subtype S)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (tsum_firstPassageLaw_threeFifths_tail_le G hG)

/-- If `1 ≤ G` and `s^2 < 2G`, then `s / 2 < G^{3/5}`. -/
private lemma c3EprimeMass_half_lt {G : ℕ} (hG : 1 ≤ G) {s : ℝ} (hsG : s ^ 2 < 2 * G) :
    s / 2 < (G : ℝ) ^ ((3 : ℝ) / 5) := by
  have htsq : (G : ℝ) ≤ ((G : ℝ) ^ ((3 : ℝ) / 5)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg G)]
    exact (Real.rpow_one _).symm.le.trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hG) (by norm_num))
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  rw [show (s / 2) ^ 2 = s ^ 2 / 4 by ring]
  linarith [(Nat.cast_nonneg G : (0 : ℝ) ≤ G)]

/-- For `G ≥ 2^160` and `0 < s` with `s^2 < 2G`, `2^55 exp(-G^{1/5}/65536) ≤ 1/s`. -/
private lemma c3EprimeMass_threeFifths_le_inv {G : ℕ} (hG : 2 ^ 160 ≤ G) {s : ℝ} (hs0 : 0 < s)
    (hsG : s ^ 2 < 2 * G) : 2 ^ 55 * exp (-((G : ℝ) ^ (1 / 5 : ℝ) / 65536)) ≤ 1 / s := by
  have h1 := c3HorSmall (G := (G : ℝ)) (by exact_mod_cast hG)
  rw [neg_div] at h1
  refine h1.le.trans ?_
  have h2G : (0 : ℝ) ≤ 2 * G := by positivity
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg h2G, ← Real.sqrt_eq_rpow, one_div]
  exact inv_anti₀ hs0 ((Real.lt_sqrt hs0.le).2 hsG).le

/-- Every atom of the exceptional event lies in one of its four constituent events. -/
private lemma c3EprimeMass_one_le_indicator {n : ℕ} {e : ℤ × ℤ} {G v X : ℕ}
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (hex : a ∈ c3Exceptional n e G v X)
    (hlen : v ≤ a.2.length) :
    (1 : ℝ≥0∞) ≤ {x : ℕ × ℤ | (X : ℝ) ≤ (x.2 : ℝ) - G}.indicator 1 a.1 +
      {x : ℕ × ℤ | (G : ℝ) ^ ((3 : ℝ) / 5) ≤ |(x.1 : ℝ) - (G : ℝ) / 4|}.indicator 1 a.1 +
      ({h : Fin v → ℤ × ℤ | (X : ℝ) ≤ ∑ i, ((h i).2 : ℝ)}.indicator 1
          (fun i : Fin v ↦ chBlockPoint (a.2[(i : ℕ)]'(lt_of_lt_of_le i.2 hlen))) +
        {h : Fin v → ℤ × ℤ | (G : ℝ) ^ ((3 : ℝ) / 5) ≤ ∑ i, ((h i).1 : ℝ)}.indicator 1
          (fun i : Fin v ↦ chBlockPoint (a.2[(i : ℕ)]'(lt_of_lt_of_le i.2 hlen)))) := by
  obtain ⟨-, h1 | h2 | h3 | h4⟩ := hex
  · refine le_add_right (le_add_right ?_)
    rw [Set.indicator_of_mem]
    · rfl
    · exact h1
  · refine le_add_left (le_add_right ?_)
    rw [Set.indicator_of_mem]
    · rfl
    · simp only [Set.mem_ofPred_eq]
      rw [c3EprimeMass_sum_take (fun b ↦ bkL (chBlockPoint b)) a.2 hlen] at h2
      exact_mod_cast h2
  · refine le_add_right (le_add_left ?_)
    rw [Set.indicator_of_mem]
    · rfl
    · exact h3
  · refine le_add_left (le_add_left ?_)
    rw [Set.indicator_of_mem]
    · rfl
    · simp only [Set.mem_ofPred_eq]
      rw [c3EprimeMass_sum_take (fun b ↦ bkJ (chBlockPoint b)) a.2 hlen] at h4
      exact_mod_cast h4

/-- Against weights `F` and `η` of total mass at most `1`, the double sum of
`p x + q x + (u h + w h)` is at most the sum of the four separate masses. -/
private lemma c3EprimeMass_tsum_mul_le {α β : Type*} (F : α → ℝ≥0∞) (η : β → ℝ≥0∞)
    (hF : ∑' x, F x ≤ 1) (hη : ∑' h, η h ≤ 1) (p q : α → ℝ≥0∞) (u w : β → ℝ≥0∞) :
    ∑' x, F x * ∑' h, η h * (p x + q x + (u h + w h)) ≤
      ∑' x, F x * p x + ∑' x, F x * q x + (∑' h, η h * u h + ∑' h, η h * w h) := by
  have hinner : ∀ x, ∑' h, η h * (p x + q x + (u h + w h)) ≤
      p x + q x + (∑' h, η h * u h + ∑' h, η h * w h) := by
    intro x
    calc ∑' h, η h * (p x + q x + (u h + w h)) =
          ∑' h, (η h * (p x + q x) + (η h * u h + η h * w h)) :=
          tsum_congr fun h ↦ by ring
      _ = (∑' h, η h) * (p x + q x) + (∑' h, η h * u h + ∑' h, η h * w h) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      _ ≤ 1 * (p x + q x) + (∑' h, η h * u h + ∑' h, η h * w h) := by
          gcongr
      _ = _ := by rw [one_mul]
  calc _ ≤ ∑' x, F x * (p x + q x + (∑' h, η h * u h + ∑' h, η h * w h)) :=
        ENNReal.tsum_le_tsum fun x ↦ mul_le_mul_right (hinner x) _
    _ = ∑' x, (F x * p x + F x * q x + F x * (∑' h, η h * u h + ∑' h, η h * w h)) :=
        tsum_congr fun x ↦ by ring
    _ = ∑' x, F x * p x + ∑' x, F x * q x +
          (∑' x, F x) * (∑' h, η h * u h + ∑' h, η h * w h) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ ∑' x, F x * p x + ∑' x, F x * q x + 1 * (∑' h, η h * u h + ∑' h, η h * w h) := by
        gcongr
    _ = _ := by rw [one_mul]

/-- Event (ii): `∑_{k ≤ v} l(βᵏ) ≥ X` has `η^{⊗v}`-mass at most `8^v (25/27)^X`, and `0`
if `v = 0`. -/
private lemma c3EprimeMass_verTail (v X : ℕ) (hX : 1 ≤ X) :
    ∑' h : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) *
          {h : Fin v → ℤ × ℤ | (X : ℝ) ≤ ∑ i, ((h i).2 : ℝ)}.indicator 1 h.1 ≤
      ENNReal.ofReal (if 1 ≤ v then 8 ^ v * (25 / 27 : ℝ) ^ X else 0) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · refine (ENNReal.tsum_eq_zero.2 fun h ↦ ?_).le.trans zero_le
    have : h.1 ∉ {h : Fin 0 → ℤ × ℤ | (X : ℝ) ≤ ∑ i, ((h i).2 : ℝ)} := by
      simp only [Set.mem_ofPred_eq, not_le, Finset.univ_eq_empty, Finset.sum_empty]
      exact_mod_cast hX
    rw [Set.indicator_of_notMem this, mul_zero]
  · simp only [show 1 ≤ v from hv0, ↓reduceIte]
    refine (tsum_holdListLaw_bkPoints_mul_indicator_le (fun h ↦ (X : ℝ) ≤ ∑ i, ((h i).2 : ℝ))
      (fun u ↦ (X : ℝ) ≤ ∑ i, ((u i).2 : ℝ)) (fun h _ hh ↦ hh)).trans ?_
    refine (tsum_holdListLaw_verTail_le v X).trans (le_of_eq ?_)
    rw [Real.rpow_natCast]

/-- Event (iv): for `t > 2048 · 136 (v + 1)`, `∑_{k ≤ v} j(βᵏ) ≥ t` has `η^{⊗v}`-mass at most
`e^{-14(v+1)}`, and `0` if `v = 0`. -/
private lemma c3EprimeMass_horTail (v : ℕ) {t : ℝ} (ht : 2048 * (136 * ((v : ℝ) + 1)) < t) :
    ∑' h : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) *
          {h : Fin v → ℤ × ℤ | t ≤ ∑ i, ((h i).1 : ℝ)}.indicator 1 h.1 ≤
      ENNReal.ofReal (if 1 ≤ v then exp (-14 * ((v : ℝ) + 1)) else 0) := by
  have hv : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · refine (ENNReal.tsum_eq_zero.2 fun h ↦ ?_).le.trans zero_le
    have : h.1 ∉ {h : Fin 0 → ℤ × ℤ | t ≤ ∑ i, ((h i).1 : ℝ)} := by
      simp only [Set.mem_ofPred_eq, not_le, Finset.univ_eq_empty, Finset.sum_empty]
      exact ht0
    rw [Set.indicator_of_notMem this, mul_zero]
  · simp only [show 1 ≤ v from hv0, ↓reduceIte]
    refine (tsum_holdListLaw_bkPoints_mul_indicator_le (fun h ↦ t ≤ ∑ i, ((h i).1 : ℝ))
      (fun u ↦ 10 * t ≤ 10 * ∑ i, ((u i).1 : ℝ)) (fun h hP hh ↦ ?_)).trans ?_
    · have hsum : ∑ i, (((h i).1.toNat : ℕ) : ℝ) = ∑ i, ((h i).1 : ℝ) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have := hP i
        simp only [mem_bkPoints, bkJ] at this
        have h0 : (((h i).1.toNat : ℕ) : ℤ) = (h i).1 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast h0
      change 10 * t ≤ 10 * ∑ i, (((h i).1.toNat : ℕ) : ℝ)
      rw [hsum]
      linarith
    · refine (tsum_holdListLaw_horTail_le v (10 * t)).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [exp_le_exp]
      linarith

/-- The four bounds add up to `1/s + Exc(v)`. -/
private lemma c3EprimeMass_ofReal_add_le {G v X : ℕ} (hX : X = 136 * (v + 1)) {s : ℝ}
    (hBs : 2 ^ 55 * exp (-((G : ℝ) ^ (1 / 5 : ℝ) / 65536)) ≤ 1 / s) :
    ENNReal.ofReal (9 * (25 / 27) ^ X) +
        ENNReal.ofReal (2 ^ 55 * exp (-((G : ℝ) ^ (1 / 5 : ℝ) / 65536))) +
        (ENNReal.ofReal (if 1 ≤ v then 8 ^ v * (25 / 27 : ℝ) ^ X else 0) +
          ENNReal.ofReal (if 1 ≤ v then exp (-14 * ((v : ℝ) + 1)) else 0)) ≤
      ENNReal.ofReal (1 / s + c3Exc v) := by
  have hi1 : (0 : ℝ) ≤ if 1 ≤ v then 8 ^ v * (25 / 27 : ℝ) ^ X else 0 := by
    split_ifs <;> positivity
  have hi2 : (0 : ℝ) ≤ if 1 ≤ v then exp (-14 * ((v : ℝ) + 1)) else 0 := by
    split_ifs <;> positivity
  calc _ = ENNReal.ofReal (9 * (25 / 27) ^ X +
          2 ^ 55 * exp (-((G : ℝ) ^ (1 / 5 : ℝ) / 65536)) +
          ((if 1 ≤ v then 8 ^ v * (25 / 27 : ℝ) ^ X else 0) +
            (if 1 ≤ v then exp (-14 * ((v : ℝ) + 1)) else 0))) := by
        rw [ENNReal.ofReal_add (by positivity) (add_nonneg hi1 hi2),
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add hi1 hi2]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [c3Exc, hX]
        split_ifs <;> linarith

/-- **Mass of the exceptional event.** For `G ≥ 2^160`, `v ≤ ⌊n/2⌋` and a real `s` with
`4096 · 136 (v + 1) ≤ s` and `s^2 < 2G`, `μ_{e,G}(Ex_{e,G,v,136(v+1)}) ≤ 1/s + Exc(v)`. -/
@[collatz_pos_dens "lem_c3_eprime_mass"]
theorem tsum_trFreshLaw_c3Exceptional_le {n : ℕ} (e : ℤ × ℤ) {G v : ℕ} (hG : 2 ^ 160 ≤ G)
    (hv : v ≤ n / 2) {s : ℝ} (hs : 4096 * (136 * ((v : ℝ) + 1)) ≤ s)
    (hsG : s ^ 2 < 2 * G) :
    ∑' a : c3Exceptional n e G v (136 * ((v : ℝ) + 1)), ENNReal.ofReal (trFreshLaw n e G a) ≤
      ENNReal.ofReal (1 / s + c3Exc v) := by
  set X : ℕ := 136 * (v + 1) with hXdef
  have hXr : (136 * ((v : ℝ) + 1)) = (X : ℝ) := by
    push_cast [hXdef]
    ring
  rw [hXr]
  have hX1 : 1 ≤ X := by omega
  have hG1 : 1 ≤ G := Nat.one_le_two_pow.trans hG
  have hG64 : 64 ≤ G := le_trans (by norm_num) hG
  have hs0 : 0 < s := by linarith [(Nat.cast_nonneg v : (0 : ℝ) ≤ v)]
  set t : ℝ := (G : ℝ) ^ ((3 : ℝ) / 5)
  have ht : s / 2 < t := c3EprimeMass_half_lt hG1 hsG
  set SA : Set (ℕ × ℤ) := {x : ℕ × ℤ | (X : ℝ) ≤ (x.2 : ℝ) - G}
  set SB : Set (ℕ × ℤ) := {x : ℕ × ℤ | t ≤ |(x.1 : ℝ) - (G : ℝ) / 4|}
  set SC : Set (Fin v → ℤ × ℤ) := {h | (X : ℝ) ≤ ∑ i, ((h i).2 : ℝ)}
  set SD : Set (Fin v → ℤ × ℤ) := {h | t ≤ ∑ i, ((h i).1 : ℝ)}
  set T : ℕ × ℤ → (Fin v → ℤ × ℤ) → ℝ≥0∞ := fun x h ↦
    SA.indicator 1 x + SB.indicator 1 x + (SC.indicator 1 h + SD.indicator 1 h)
  set η : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints} → ℝ≥0∞ :=
    fun h ↦ ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2))
  set F : ℕ × ℤ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (firstPassageLaw G ((x.1 : ℤ), x.2))
  have hcover : ∀ a ∈ c3Exceptional n e G v X, (ha : a ∈ trAtoms n) →
      1 ≤ T a.1 (fun i : Fin v ↦ chBlockPoint (a.2[(i : ℕ)]'(by
          have := (mem_trAtoms.1 ha).1; omega))) :=
    fun a hex ha ↦ c3EprimeMass_one_le_indicator hex (by have := (mem_trAtoms.1 ha).1; omega)
  have step1 : ∑' a : c3Exceptional n e G v X, ENNReal.ofReal (trFreshLaw n e G a) ≤
      ∑' x : ℕ × ℤ, F x * ∑' h, η h * T x h.1 := by
    rw [← tsum_trFreshLaw_mul_chBlockPoint n e G v hv T]
    calc _ ≤ ∑' a : c3Exceptional n e G v X,
          (fun b : trAtoms n ↦ ENNReal.ofReal (trFreshLaw n e G b) *
            T b.1.1 (fun i ↦ chBlockPoint (b.1.2[(i : ℕ)]'(by
              have := (mem_trAtoms.1 b.2).1; omega))))
            (Set.inclusion (c3Exceptional_subset_trAtoms n e G v X) a) :=
          ENNReal.tsum_le_tsum fun a ↦ le_mul_of_one_le_right'
            (hcover a.1 a.2 (c3Exceptional_subset_trAtoms n e G v X a.2))
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective
          (Set.inclusion_injective (c3Exceptional_subset_trAtoms n e G v X))
          (fun b : trAtoms n ↦ ENNReal.ofReal (trFreshLaw n e G b) *
            T b.1.1 (fun i ↦ chBlockPoint (b.1.2[(i : ℕ)]'(by
              have := (mem_trAtoms.1 b.2).1; omega))))
  calc _ ≤ _ := step1
    _ ≤ _ := c3EprimeMass_tsum_mul_le F η (tsum_ofReal_firstPassageLaw_natCast_le_one G)
        (tsum_ofReal_holdListLaw_bkPoints_le_one v) (SA.indicator 1) (SB.indicator 1)
        (fun h ↦ SC.indicator 1 h.1) (fun h ↦ SD.indicator 1 h.1)
    _ ≤ _ := add_le_add
        (add_le_add (c3EprimeMass_overshoot hG64 hX1) (c3EprimeMass_threeFifths hG1))
        (add_le_add (c3EprimeMass_verTail v X hX1) (c3EprimeMass_horTail v (t := t) (by linarith)))
    _ ≤ _ := c3EprimeMass_ofReal_add_le hXdef (c3EprimeMass_threeFifths_le_inv hG hs0 hsG)

/-- The fresh law is summable on the exceptional event, under the hypotheses of
`tsum_trFreshLaw_c3Exceptional_le`. -/
theorem summable_trFreshLaw_c3Exceptional {n : ℕ} (e : ℤ × ℤ) {G v : ℕ}
    (hG : 2 ^ 160 ≤ G) (hv : v ≤ n / 2) {s : ℝ} (hs : 4096 * (136 * ((v : ℝ) + 1)) ≤ s)
    (hsG : s ^ 2 < 2 * G) :
    Summable fun a : c3Exceptional n e G v (136 * ((v : ℝ) + 1)) ↦ trFreshLaw n e G a :=
  summable_trFreshLaw_of_tsum_ofReal_ne_top
    ((tsum_trFreshLaw_c3Exceptional_le e hG hv hs hsG).trans_lt ENNReal.ofReal_lt_top).ne

/-- **Mass of the exceptional event**, as a real sum:
`μ_{e,G}(Ex_{e,G,v,136(v+1)}) ≤ 1/s + Exc(v)`. -/
theorem tsum_trFreshLaw_c3Exceptional_le_real {n : ℕ} (e : ℤ × ℤ) {G v : ℕ}
    (hG : 2 ^ 160 ≤ G) (hv : v ≤ n / 2) {s : ℝ} (hs : 4096 * (136 * ((v : ℝ) + 1)) ≤ s)
    (hsG : s ^ 2 < 2 * G) :
    ∑' a : c3Exceptional n e G v (136 * ((v : ℝ) + 1)), trFreshLaw n e G a ≤ 1 / s + c3Exc v := by
  have hs0 : 0 < s := by
    have : (0 : ℝ) ≤ v := by positivity
    linarith
  have h := tsum_trFreshLaw_c3Exceptional_le e hG hv hs hsG
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ trFreshLaw_nonneg _ _ _ _)
    (summable_trFreshLaw_c3Exceptional e hG hv hs hsG)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by have := c3Exc_pos v; positivity)).1 h

end CollatzPosDens
