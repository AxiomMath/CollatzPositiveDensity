/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.Lb
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.BarrierMono
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal

/-!
# Overshoot loss

Let `b ≥ 1`, `u` and `K ≥ 0` be integers. The words `v ∈ ℤ_{≥1}^{h_b}` whose prefix
valuation sums `A_i(v) = A(v_{≤ i})` stay strictly below the barrier `H_{b,u}(i)` for
`ℓ_b ≤ i < s` and then overshoot it by more than `K` at some time `ℓ_b < s ≤ h_b`,
`A_s(v) > H_{b,u}(s) + K`, have geometric mass at most `2^{-(K+1)}`.

The time `s` is a *first crossing* of `v`: `A_i(v) < H_{b,u}(i)` for `ℓ_b ≤ i < s` and
`A_s(v) ≥ H_{b,u}(s)`, and a word has at most one first crossing. Since
`A_{s-1}(v) < H_{b,u}(s-1) ≤ H_{b,u}(s)`, the `s`-th letter of an overshooting word exceeds
`K + 1`; lowering it by `K + 1` gives a word of length `h_b` that still has first crossing `s`.
This map is injective (the first crossing of the image recovers `s`) and multiplies the weight
`2^{-A(v)}` by `2^{K+1}`, so the mass of the overshooting words is at most `2^{-(K+1)}` times
`𝐩(ℤ_{≥1}^{h_b}) = 1`.

## Main results

* `CollatzPosDens.geomMass_overshoot_le_of_monotone`: the bound for an arbitrary monotone
  barrier `H : ℕ → ℤ` and arbitrary length window `lo < s ≤ n`.
* `CollatzPosDens.geomMass_overshoot_le`: the overshoot loss bound for the barrier `H_{b,u}`.

## Implementation notes

Here `b` and `K` are natural numbers, with `b = 0` allowed. The prefix `v_{≤ i}` is `v.take i`, and
the weight `2^{-(K+1)}` is `2⁻¹ ^ (K + 1)` in `ℝ≥0∞`. Rather than decomposing the overshooting
words by their first crossing and prefix and summing geometric series, the bound is obtained from
the weight-scaling injection described above, which needs only the monotonicity of the barrier
(`CollatzPosDens.barrier_le_barrier_succ`) and the total mass `𝐩(ℤ_{≥1}^{h_b}) = 1`
(`CollatzPosDens.geomMass_setOf_length_eq`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- Lower the letter of index `j` (the `(j+1)`-st letter) of `v` by `k`, in `ℕ+`. -/
private def overshootShift (k : ℕ+) (j : ℕ) (v : Word) : Word :=
  v.take j ++ (v.getD j 1 - k) :: v.drop (j + 1)

private theorem overshootShift_decomp {j : ℕ} {v : Word} (hj : j < v.length) :
    v = v.take j ++ v[j] :: v.drop (j + 1) := by
  rw [List.getElem_cons_drop, List.take_append_drop]

private theorem overshootShift_getD {j : ℕ} {v : Word} (hj : j < v.length) :
    v.getD j 1 = v[j] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

private theorem length_overshootShift (k : ℕ+) {j : ℕ} {v : Word} (hj : j < v.length) :
    (overshootShift k j v).length = v.length := by
  simp only [overshootShift, List.length_append, List.length_take, List.length_cons,
    List.length_drop]
  omega

private theorem take_overshootShift (k : ℕ+) {i j : ℕ} {v : Word} (hj : j < v.length)
    (hi : i ≤ j) : (overshootShift k j v).take i = v.take i := by
  rw [overshootShift, List.take_append_of_le_length (by simp; omega), List.take_take,
    Nat.min_eq_left hi]

private theorem valSum_take_overshootShift (k : ℕ+) {j : ℕ} {v : Word} (hj : j < v.length)
    (hk : k < v[j]) :
    Word.valSum ((overshootShift k j v).take (j + 1)) + k = Word.valSum (v.take (j + 1)) := by
  have hlen : (v.take j).length = j := by simp; omega
  rw [overshootShift, overshootShift_getD hj, List.take_add_one (l := v),
    List.getElem?_eq_getElem hj]
  rw [List.take_append, List.take_take, hlen, Nat.min_eq_right (Nat.le_succ j),
    Nat.add_sub_cancel_left]
  simp only [List.take_succ_cons, List.take_zero, Word.valSum_append, Word.valSum_singleton,
    Option.toList_some, PNat.sub_coe, hk, ↓reduceIte]
  have : (k : ℕ) < v[j] := hk
  omega

private theorem valSum_overshootShift (k : ℕ+) {j : ℕ} {v : Word} (hj : j < v.length)
    (hk : k < v[j]) : (overshootShift k j v).valSum + k = v.valSum := by
  conv_rhs => rw [overshootShift_decomp hj]
  rw [overshootShift, overshootShift_getD hj]
  simp only [Word.valSum_append, Word.valSum_cons, PNat.sub_coe, hk, ↓reduceIte]
  have : (k : ℕ) < v[j] := hk
  omega

private theorem overshootShift_inj (k : ℕ+) {j : ℕ} {v v' : Word} (hj : j < v.length)
    (hj' : j < v'.length) (hk : k < v[j]) (hk' : k < v'[j])
    (h : overshootShift k j v = overshootShift k j v') : v = v' := by
  rw [overshootShift, overshootShift, overshootShift_getD hj, overshootShift_getD hj'] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp; omega)
  obtain ⟨h3, h4⟩ := List.cons_eq_cons.1 h2
  have h5 : v[j] = v'[j] := by
    have := congrArg ((↑) : ℕ+ → ℕ) h3
    simp only [PNat.sub_coe, hk, hk', ↓reduceIte] at this
    have : (k : ℕ) < v[j] := hk
    have : (k : ℕ) < v'[j] := hk'
    exact PNat.coe_injective (by omega)
  rw [overshootShift_decomp hj, overshootShift_decomp hj', h1, h4, h5]

/-- A word has at most one first crossing of a barrier `H` after time `lo`. -/
private theorem overshoot_crossing_unique {H : ℕ → ℤ} {lo s t : ℕ} {x : Word}
    (hs : lo < s) (ht : lo < t)
    (hbs : ∀ i, lo ≤ i → i < s → (Word.valSum (x.take i) : ℤ) < H i)
    (hxs : H s ≤ (Word.valSum (x.take s) : ℤ))
    (hbt : ∀ i, lo ≤ i → i < t → (Word.valSum (x.take i) : ℤ) < H i)
    (hxt : H t ≤ (Word.valSum (x.take t) : ℤ)) : s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact absurd (hbt s hs.le h) (not_lt.2 hxs)
  · exact h
  · exact absurd (hbs t ht.le h) (not_lt.2 hxt)

/-- **Overshoot loss, for a general monotone barrier.** For a monotone `H : ℕ → ℤ`, the words
`v` of length `n` whose prefix sums stay below `H` on `[lo, s)` and overshoot `H(s)` by more
than `K` at some `lo < s ≤ n` have geometric mass at most `2^{-(K+1)}`. -/
theorem geomMass_overshoot_le_of_monotone {H : ℕ → ℤ} (hH : Monotone H) (lo n K : ℕ) :
    geomMass {v : Word | v.length = n ∧ ∃ s, lo < s ∧ s ≤ n ∧
      (∀ i, lo ≤ i → i < s → (Word.valSum (v.take i) : ℤ) < H i) ∧
      H s + K < (Word.valSum (v.take s) : ℤ)} ≤ 2⁻¹ ^ (K + 1) := by
  set O := {v : Word | v.length = n ∧ ∃ s, lo < s ∧ s ≤ n ∧
      (∀ i, lo ≤ i → i < s → (Word.valSum (v.take i) : ℤ) < H i) ∧
      H s + K < (Word.valSum (v.take s) : ℤ)} with hO
  set k : ℕ+ := K.succPNat with hk
  have key : ∀ v ∈ O, ∃ s, lo < s ∧ s ≤ n ∧ ∃ hj : s - 1 < v.length, k < v[s - 1] ∧
      (∀ i, lo ≤ i → i < s →
        (Word.valSum ((overshootShift k (s - 1) v).take i) : ℤ) < H i) ∧
      H s ≤ (Word.valSum ((overshootShift k (s - 1) v).take s) : ℤ) := by
    rintro v ⟨hlen, s, hlo, hsn, hbelow, hover⟩
    have hj : s - 1 < v.length := by omega
    have hs1 : s - 1 + 1 = s := by omega
    have hA : (Word.valSum (v.take s) : ℤ) =
        Word.valSum (v.take (s - 1)) + (v[s - 1] : ℕ) := by
      have e := List.take_add_one (l := v) (i := s - 1)
      rw [hs1, List.getElem?_eq_getElem hj] at e
      rw [e, Option.toList_some, Word.valSum_append, Word.valSum_singleton]
      push_cast; rfl
    have hprev := hbelow (s - 1) (by omega) (by omega)
    have hmono : H (s - 1) ≤ H s := hH (by omega)
    have hkv : k < v[s - 1] := by
      have : (K : ℤ) + 1 < (v[s - 1] : ℕ) := by omega
      change (k : ℕ) < (v[s - 1] : ℕ)
      rw [hk, Nat.succPNat_coe]
      omega
    refine ⟨s, hlo, hsn, hj, hkv, fun i hi his => ?_, ?_⟩
    · rw [take_overshootShift k hj (by omega)]
      exact hbelow i hi his
    · have := valSum_take_overshootShift k hj hkv
      rw [hs1] at this
      have hk' : ((k : ℕ) : ℤ) = K + 1 := by rw [hk, Nat.succPNat_coe]; push_cast; rfl
      have : (Word.valSum ((overshootShift k (s - 1) v).take s) : ℤ) + (k : ℕ) =
          Word.valSum (v.take s) := by exact_mod_cast this
      omega
  choose sOf hlo hsn hj hkv hbelow hcross using key
  let φ : O → {w : Word | w.length = n} := fun v =>
    ⟨overshootShift k (sOf v v.2 - 1) v, by
      simp only [Set.mem_ofPred_eq]
      rw [length_overshootShift k (hj v v.2)]
      exact v.2.1⟩
  have hφ : Function.Injective φ := by
    rintro ⟨v, hv⟩ ⟨v', hv'⟩ h
    have h' : overshootShift k (sOf v hv - 1) v = overshootShift k (sOf v' hv' - 1) v' :=
      congrArg Subtype.val h
    have hs : sOf v hv = sOf v' hv' := by
      refine overshoot_crossing_unique (x := overshootShift k (sOf v hv - 1) v)
        (hlo v hv) (hlo v' hv') (hbelow v hv) (hcross v hv) ?_ ?_
      · rw [h']; exact hbelow v' hv'
      · rw [h']; exact hcross v' hv'
    rw [← hs] at h'
    have hj' := hj v' hv'
    have hkv' := hkv v' hv'
    simp only [← hs] at hj' hkv'
    exact Subtype.ext (overshootShift_inj k (hj v hv) hj' (hkv v hv) hkv' h')
  have hweight : ∀ v : O, (v : Word).massWeight =
      2⁻¹ ^ (K + 1) * ((φ v : {w : Word | w.length = n}) : Word).massWeight := by
    intro v
    have := valSum_overshootShift k (hj v v.2) (hkv v v.2)
    rw [hk, Nat.succPNat_coe] at this
    simp only [Word.massWeight, φ, ← pow_add]
    rw [← this, add_comm]
  calc geomMass O = ∑' v : O, 2⁻¹ ^ (K + 1) *
        ((φ v : {w : Word | w.length = n}) : Word).massWeight := by
        rw [geomMass_def]; exact tsum_congr hweight
    _ = 2⁻¹ ^ (K + 1) * ∑' v : O, ((φ v : {w : Word | w.length = n}) : Word).massWeight :=
        ENNReal.tsum_mul_left
    _ ≤ 2⁻¹ ^ (K + 1) * ∑' w : {w : Word | w.length = n}, (w : Word).massWeight := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hφ fun w => (w : Word).massWeight
    _ = 2⁻¹ ^ (K + 1) := by
        rw [← geomMass_def, geomMass_setOf_length_eq, mul_one]

/-- **Overshoot loss.** For `b`, `u` and `K ≥ 0`, the words `v ∈ ℤ_{≥1}^{h_b}` with some
`ℓ_b < s ≤ h_b` such that `A_i(v) < H_{b,u}(i)` for `ℓ_b ≤ i < s` and
`A_s(v) > H_{b,u}(s) + K` have geometric mass at most `2^{-(K+1)}`. -/
@[collatz_pos_dens "lem_overshoot"]
theorem geomMass_overshoot_le (b : ℕ) (u : ℤ) (K : ℕ) :
    geomMass {v : Word | v.length = hb b ∧ ∃ s, lb b < s ∧ s ≤ hb b ∧
      (∀ i, lb b ≤ i → i < s → (Word.valSum (v.take i) : ℤ) < barrier b u i) ∧
      barrier b u s + K < (Word.valSum (v.take s) : ℤ)} ≤ 2⁻¹ ^ (K + 1) :=
  geomMass_overshoot_le_of_monotone (monotone_barrier b u) (lb b) (hb b) K

end CollatzPosDens
