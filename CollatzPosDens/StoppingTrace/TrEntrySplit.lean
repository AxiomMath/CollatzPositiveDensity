/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.StoppingTrace.TrEntryWord
public import CollatzPosDens.StoppingTrace.TrFirstStopSet
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrSublist
public import CollatzPosDens.StoppingTrace.TrConcat
public import CollatzPosDens.StoppingTrace.TrConcatShift
public import CollatzPosDens.StoppingTrace.TrPathGrowth

/-!
# An entry list is a passage followed by a first stop

Fix a level `n`, a residue `ξ ∈ G_n`, a colour scale `ε` and a point `v`, and put
`s = gap(v)`. Since `l_*(v) = l(v) + s`, the path `x_t(v, u) = v + Bp_t(u)` of a list `u` lies
strictly above the column top of `v` exactly when `l(Bp_t(u)) > s`. An entry list `u ∈ 𝓔(v)`
therefore splits uniquely as `u = π b`, where `π = u_{[1,k]}` is cut at the least time `k ≥ 1` with
`l(Bp_k(u)) > s`, so that `π ∈ Π_s`, and `b = u_{[k+1,|u|]}` is a first-stop list from
`x_k(v, π)`: the path of a live list never descends, so after time `k` it stays above the column
top, and the entry condition reduces to the first-stop condition. Conversely every such
concatenation `π b` is an entry list.

## Main results

* `CollatzPosDens.trEntryWords_bijOn_append`: the map `(π, b) ↦ π b` is a bijection from
  the pairs with `π ∈ Π_s` and `b ∈ 𝒰(x_{|π|}(v, π))` onto `𝓔(v)`.
* `CollatzPosDens.bkColTop_lt_trPath_iff`: `l(x_t(v, u)) > l_*(v)` iff `l(Bp_t(u)) > gap(v)`.

## Implementation notes

In [mazur2026] the splitting is stated for `n ≥ 1`, a unit `ξ` and a black point `v`. None of
these hypotheses enters the argument, so `CollatzPosDens.trEntryWords_bijOn_append` is stated for
every `n`, `ξ`, `ε` and every point `v ∈ ℤ × ℤ`. A bijection between sets is expressed as
`Set.BijOn` on the set of pairs `(π, b)` of block lists.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}

/-- The path of `u` from `v` is strictly above the column top of `v` at time `t` iff
`l(Bp_t(u)) > gap(v)`. -/
lemma bkColTop_lt_trPath_iff (v : ℤ × ℤ) (u : List (List ℤ × ℤ)) (t : ℕ) :
    bkColTop n ξ ε v < bkL (trPath v u t) ↔ (trGap n ξ ε v : ℤ) < (chBlockPath u t).2 := by
  rw [bkColTop_eq_add_trGap, trPath_eq_add_chBlockPath]
  simp only [bkL, Prod.snd_add]
  omega

/-- Along a list whose closing letters lie in `{4, 5}` and which is live, the height of the path
does not decrease. -/
private lemma bkL_trPath_mono (o : ℤ × ℤ) {u : List (List ℤ × ℤ)}
    (hc : ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)) (hl : TrLive u) {k t : ℕ} (hkt : k ≤ t) :
    bkL (trPath o u k) ≤ bkL (trPath o u t) := by
  have h4 : ∀ b ∈ u, 4 ≤ b.2 := fun b hb ↦ by
    rcases hc b hb with h | h <;> simp_all
  have := trPath_bkL_sub_ge o h4 hl hkt
  have : (min k u.length : ℕ) ≤ min t u.length := min_le_min_right _ hkt
  omega

/-- **Entry lists split as a passage followed by a first stop.** For `s = gap(v)`, the map
`(π, b) ↦ π b` is a bijection from the pairs with `π ∈ Π_s` and `b ∈ 𝒰(x_{|π|}(v, π))` onto
the set `𝓔(v)` of entry lists. -/
@[collatz_pos_dens "lem_tr_entry_split"]
theorem trEntryWords_bijOn_append (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (v : ℤ × ℤ) :
    Set.BijOn (fun p : List (List ℤ × ℤ) × List (List ℤ × ℤ) ↦ p.1 ++ p.2)
      {p | p.1 ∈ trPassage (trGap n ξ ε v) ∧
        p.2 ∈ trFirstStopSet n ξ ε (trPath v p.1 p.1.length)}
      (trEntryWords n ξ ε v) := by
  set s := trGap n ξ ε v with hs
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨π, b⟩ ⟨hπ, hb⟩
    dsimp only at hπ hb ⊢
    set k := π.length with hk
    have hc : ∀ x ∈ π ++ b, x.2 ∈ ({4, 5} : Set ℤ) := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact trPassage_closing_mem hπ h
      · exact trFirstStopSet_closing_mem hb h
    have hl : TrLive (π ++ b) :=
      trLive_append.mpr ⟨trLive_of_mem_trPassage hπ, trFirstStopSet_trLive hb⟩
    have hk1 : 1 ≤ k := length_pos_of_mem_trPassage hπ
    have habove : ∀ t, k ≤ t → bkColTop n ξ ε v < bkL (trPath v (π ++ b) t) := by
      intro t ht
      refine lt_of_lt_of_le ?_ (bkL_trPath_mono v hc hl ht)
      rw [trPath_concat v π b le_rfl, bkColTop_lt_trPath_iff]
      exact lt_chBlockPath_snd_of_mem_trPassage hπ
    have hshift : ∀ t', trPath v (π ++ b) (k + t') = trPath (trPath v π k) b t' :=
      fun t' ↦ trPath_append_add v π b rfl t'
    have hlen : (π ++ b).length = k + b.length := by simp [hk]
    refine ⟨hc, hl, by omega, ⟨?_, habove _ (by omega)⟩, ?_⟩
    · rw [hlen, hshift]
      exact trFirstStopSet_bkBlack hb
    · intro t ht1 ht ⟨hbl, hab⟩
      rcases lt_or_ge t k with htk | htk
      · rw [trPath_concat v π b htk.le, bkColTop_lt_trPath_iff] at hab
        exact absurd (chBlockPath_snd_le_of_mem_trPassage hπ htk) (not_le.mpr hab)
      · obtain ⟨t', rfl⟩ := Nat.exists_eq_add_of_le htk
        rw [hshift] at hbl
        exact trFirstStopSet_not_bkBlack hb (by omega) hbl
  · rintro ⟨π, b⟩ ⟨hπ, -⟩ ⟨π', b'⟩ ⟨hπ', -⟩ h
    dsimp only at hπ hπ' h
    rcases List.append_eq_append_iff.mp h with ⟨c, rfl, rfl⟩ | ⟨c, rfl, rfl⟩
    · obtain rfl := trPassage_eq_of_prefix hπ hπ'
      simp
    · obtain rfl := trPassage_eq_of_prefix hπ' hπ
      simp
  · intro u hu
    obtain ⟨hc, hl, hq1, ⟨hbl, hab⟩, hnot⟩ := hu
    have hP : ∃ k, (s : ℤ) < (chBlockPath u k).2 :=
      ⟨u.length, (bkColTop_lt_trPath_iff v u _).mp hab⟩
    classical
    set k := Nat.find hP with hkdef
    have hkP : (s : ℤ) < (chBlockPath u k).2 := Nat.find_spec hP
    have hkmin : ∀ i < k, (chBlockPath u i).2 ≤ s := fun i hi ↦
      not_lt.mp (Nat.find_min hP hi)
    have hkq : k ≤ u.length := Nat.find_min' hP ((bkColTop_lt_trPath_iff v u _).mp hab)
    have hk1 : 1 ≤ k := by
      by_contra h0
      have : k = 0 := by omega
      rw [this, chBlockPath_zero] at hkP
      exact absurd hkP (by simp)
    have hsplit : u.take k ++ u.drop k = u := List.take_append_drop k u
    have hlenπ : (u.take k).length = k := by simp [hkq]
    have hpath : ∀ i ≤ k, chBlockPath (u.take k) i = chBlockPath u i := fun i hi ↦ by
      conv_rhs => rw [← hsplit]
      exact (chBlockPath_append_of_le _ _ (by omega)).symm
    have hmono : ∀ t, k ≤ t → bkColTop n ξ ε v < bkL (trPath v u t) := fun t ht ↦
      lt_of_lt_of_le ((bkColTop_lt_trPath_iff v u k).mpr hkP) (bkL_trPath_mono v hc hl ht)
    have hshift : ∀ t', trPath v u (k + t') = trPath (trPath v (u.take k) k) (u.drop k) t' := by
      intro t'
      conv_lhs => rw [← hsplit]
      exact trPath_append_add v _ _ hlenπ t'
    refine ⟨(u.take k, u.drop k), ⟨?_, ?_⟩, hsplit⟩
    · refine ⟨fun x hx ↦ hc x (List.mem_of_mem_take hx), hl.take k, ?_, ?_, ?_⟩
      · rw [← List.length_pos_iff, hlenπ]
        omega
      · intro i hi
        rw [hlenπ] at hi
        rw [hpath i hi.le]
        exact hkmin i hi
      · rw [hlenπ, hpath k le_rfl]
        exact hkP
    · dsimp only
      rw [hlenπ]
      have hlend : (u.drop k).length = u.length - k := List.length_drop
      refine ⟨fun x hx ↦ hc x (List.mem_of_mem_drop hx), hl.drop k, ?_, ?_⟩
      · rw [← hshift, hlend, Nat.add_sub_cancel' hkq]
        exact hbl
      · intro t' ht' hb'
        rw [← hshift] at hb'
        rw [hlend] at ht'
        exact hnot (k + t') (by omega) (by omega) ⟨hb', hmono _ (by omega)⟩

end CollatzPosDens
