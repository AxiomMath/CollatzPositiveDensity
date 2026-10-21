/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.FirstCrossing.FcComplement
public import CollatzPosDens.FirstCrossing.Overshoot

/-!
# Covering the complement of a first-crossing window

Let `ℓ_b < d' ≤ d'' ≤ h_b`, and let `𝒱` be the set of words of the first-crossing family
`𝒲(b, u, K)` whose length lies in `[d', d'']`. Then
$$1-\mathbf p(\mathcal V)\le\mathbf p(E_1)+\mathbf p(E_2)+2^{-(K+1)},$$
where `E₁` is the set of `v ∈ ℤ_{≥1}^{h_b}` crossing the barrier early,
`A_i(v) ≥ H_{b,u}(i)` for some `ℓ_b ≤ i < d'`, and `E₂` the set of those still below the
barrier at time `d''`, `A_{d''}(v) < H_{b,u}(d'')`.

The family `𝒱` is prefix-disjoint with lengths at most `h_b`, so `1 - 𝐩(𝒱) = 𝐩(Y)`, where `Y`
is the set of `v ∈ ℤ_{≥1}^{h_b}` with no prefix in `𝒱`. A word outside `E₁`, `E₂` and the
overshoot set `O` has a least crossing time `s ∈ [d', d'']` with overshoot at most `K`, so its
prefix `v_{≤ s}` lies in `𝒱`. Hence `Y ⊆ E₁ ∪ E₂ ∪ O`, and the bound follows from
subadditivity of `𝐩` and `𝐩(O) ≤ 2^{-(K+1)}`.

## Main results

* `CollatzPosDens.one_sub_geomMass_firstCrossing_window_le`: the covering bound above.

## Implementation notes

The parameters `b` and `K` are natural numbers, and the hypothesis `b ≥ 1` is not needed. The
lengths `d', d''` are natural numbers, which loses nothing since `ℓ_b < d'`. The prefix `v_{≤ i}`
is `v.take i`, the set `ℤ_{≥1}^{h_b}` is the set of words of length `h_b`, and `2^{-(K+1)}` is
`2⁻¹ ^ (K + 1)` in `ℝ≥0∞`, where subtraction is truncated.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- **Covering the complement of a first-crossing window.** For `ℓ_b < d' ≤ d'' ≤ h_b`,
`1 - 𝐩({w ∈ 𝒲(b, u, K) : d' ≤ |w| ≤ d''})` is at most the mass of the words of length `h_b`
crossing the barrier at some time `ℓ_b ≤ i < d'`, plus the mass of those below the barrier at
time `d''`, plus `2^{-(K+1)}`. -/
@[collatz_pos_dens "lem_fc_cover"]
theorem one_sub_geomMass_firstCrossing_window_le (b : ℕ) (u : ℤ) (K : ℕ) {d' d'' : ℕ}
    (hd' : lb b < d') (hd : d' ≤ d'') (hd'' : d'' ≤ hb b) :
    1 - geomMass {w | w ∈ firstCrossing b u K ∧ d' ≤ w.length ∧ w.length ≤ d''} ≤
      geomMass {v : Word | v.length = hb b ∧
          ∃ i, lb b ≤ i ∧ i < d' ∧ barrier b u i ≤ (Word.valSum (v.take i) : ℤ)} +
        geomMass {v : Word | v.length = hb b ∧
          (Word.valSum (v.take d'') : ℤ) < barrier b u d''} +
        2⁻¹ ^ (K + 1) := by
  set V := {w | w ∈ firstCrossing b u K ∧ d' ≤ w.length ∧ w.length ≤ d''}
  have hV : InformationTheory.IsPrefixFree V := fun w hw w' hw' =>
    isPrefixFree_firstCrossing b u K w hw.1 w' hw'.1
  have hlen : ∀ w ∈ V, w.length ≤ hb b := fun w hw => hw.2.2.trans hd''
  rw [one_sub_geomMass_eq_geomMass_setOf_not_prefix_mem hV hlen]
  set E₁ := {v : Word | v.length = hb b ∧
    ∃ i, lb b ≤ i ∧ i < d' ∧ barrier b u i ≤ (Word.valSum (v.take i) : ℤ)}
  set E₂ := {v : Word | v.length = hb b ∧ (Word.valSum (v.take d'') : ℤ) < barrier b u d''}
  set O := {v : Word | v.length = hb b ∧ ∃ s, lb b < s ∧ s ≤ hb b ∧
    (∀ i, lb b ≤ i → i < s → (Word.valSum (v.take i) : ℤ) < barrier b u i) ∧
    barrier b u s + K < (Word.valSum (v.take s) : ℤ)}
  suffices hsub : {v : Word | v.length = hb b ∧ ¬ ∃ w ∈ V, w <+: v} ⊆ E₁ ∪ E₂ ∪ O by
    calc _ ≤ geomMass (E₁ ∪ E₂ ∪ O) := geomMass_mono hsub
      _ ≤ geomMass (E₁ ∪ E₂) + geomMass O := geomMass_union_le _ _
      _ ≤ geomMass E₁ + geomMass E₂ + 2⁻¹ ^ (K + 1) :=
        add_le_add (geomMass_union_le _ _) (geomMass_overshoot_le b u K)
  rintro v ⟨hv, hY⟩
  by_contra hcon
  have hE₁ : ∀ i, lb b ≤ i → i < d' → (Word.valSum (v.take i) : ℤ) < barrier b u i :=
    fun i hi hid => not_le.1 fun h => hcon (Or.inl (Or.inl ⟨hv, i, hi, hid, h⟩))
  have hE₂ : barrier b u d'' ≤ (Word.valSum (v.take d'') : ℤ) :=
    not_lt.1 fun h => hcon (Or.inl (Or.inr ⟨hv, h⟩))
  have hO : ∀ s, lb b < s → s ≤ hb b →
      (∀ i, lb b ≤ i → i < s → (Word.valSum (v.take i) : ℤ) < barrier b u i) →
      (Word.valSum (v.take s) : ℤ) ≤ barrier b u s + K :=
    fun s h₁ h₂ h₃ => not_lt.1 fun h => hcon (Or.inr ⟨hv, s, h₁, h₂, h₃, h⟩)
  have hex : ∃ s, lb b < s ∧ barrier b u s ≤ (Word.valSum (v.take s) : ℤ) :=
    ⟨d'', hd'.trans_le hd, hE₂⟩
  classical
  set s := Nat.find hex
  obtain ⟨hls, hs⟩ := Nat.find_spec hex
  have hsd'' : s ≤ d'' := Nat.find_min' hex ⟨hd'.trans_le hd, hE₂⟩
  have hbelow : ∀ i, lb b ≤ i → i < s → (Word.valSum (v.take i) : ℤ) < barrier b u i := by
    intro i hi his
    rcases hi.eq_or_lt with rfl | hi
    · exact hE₁ _ le_rfl hd'
    · exact not_le.1 fun h => Nat.find_min hex his ⟨hi, h⟩
  have hsd' : d' ≤ s := not_lt.1 fun h => (hE₁ s hls.le h).not_ge hs
  have hsh : s ≤ hb b := hsd''.trans hd''
  have hcross : (Word.valSum (v.take s) : ℤ) ≤ barrier b u s + K :=
    hO s hls hsh hbelow
  have hlen_s : (v.take s).length = s := by simp [hv, hsh]
  refine hY ⟨v.take s, ⟨?_, by rw [hlen_s]; exact hsd', by rw [hlen_s]; exact hsd''⟩,
    List.take_prefix _ _⟩
  refine ⟨by rw [hlen_s]; exact hls, by rw [hlen_s]; exact hsh, ?_, by rw [hlen_s]; exact hs,
    by rw [hlen_s]; exact hcross⟩
  intro i hi his
  rw [hlen_s] at his
  rw [List.take_take, min_eq_left his.le]
  exact hbelow i hi his

end CollatzPosDens
