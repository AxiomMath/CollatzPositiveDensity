/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrSublist
public import CollatzPosDens.StoppingTrace.TrTrace
public import CollatzPosDens.StoppingTrace.TrConcat
public import CollatzPosDens.StoppingTrace.TrConcatShift
public import CollatzPosDens.StoppingTrace.TrNoLateHit

/-!
# Restarting the stopping sequence at a stop

Fix a level `n`, a residue `ξ ∈ G_n` and a colour scale `ε`, and put `J = ⌊n/2⌋`. Let `o ∈ 𝒫`,
`β ∈ 𝔅^N` with `j(o) + N > J`, and `x = (x_t(o, β))_t`. If `q = τ_i(x)` is the `i`-th stop of `x`
and `x' = (x_u(x_q(o, β), β_{[q+1,N]}))_u` is the path restarted at time `q`, then the stopping
sequence of `x` is `(τ_1(x), …, τ_{i-1}(x), q + τ_1(x'), …, q + τ_{ν(x')}(x'))`.

The restarted path is the shift `x' = x(q + ·)` (by concatenation of paths), and `x` has no hit at
a time `≥ J` (a hit `t` has `j(x_t) ≤ J`, hence `j(o) + t ≤ J` with `j(o) ≥ 1`). For such a
sequence the next stop after `q + u` is `q` plus the next stop of the shift after `u`, and an
induction on the index gives the decomposition.

## Main results

* `CollatzPosDens.trNextStop_restart_add`: for a sequence without hits at times `≥ ⌊n/2⌋`,
  the next stop of `x` after `q + u` is `q` plus the next stop of `x(q + ·)` after `u`.
* `CollatzPosDens.trStopTime_restart_of_noLateHit`: the restart decomposition for any
  sequence without hits at times `≥ ⌊n/2⌋`.
* `CollatzPosDens.trStopTime_trPath_restart`: the restart decomposition for a path
  `x_t = x_t(o, β)`.

## Implementation notes

The stopping sequence of `x` being `(τ_1(x), …, τ_{i-1}(x), q + τ_1(x'), …, q + τ_{ν(x')}(x'))`
is stated as `τ_{i+k}(x) = q + τ_{k+1}(x')` for every `k` (as partially defined values in
`Option ℕ`, so that one side is defined iff the other is) together with
`ν(x) = (i - 1) + ν(x')`; the first `i - 1` terms are unchanged by construction. The hypotheses
`i ≥ 1`, `ν(x) ≥ i` and `q = τ_i(x)` are together the single hypothesis `τ_i(x) = some q`. The
hypothesis `q ≤ N` of the source is not needed: it follows from `q` being a hit. The length `N`
is `β.length`, and the closing letters of the blocks of `β` are unrestricted, since the
decomposition does not use them.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {x : ℕ → ℤ × ℤ}

/-- If `x` has no hit at a time `≥ ⌊n/2⌋`, then the next stop of `x` after `q + u` is `q` plus
the next stop of the shifted sequence `x(q + ·)` after `u`. -/
theorem trNextStop_restart_add (hlate : ∀ t, IsTrHit n ξ ε x t → t < n / 2) (q u : ℕ) :
    trNextStop n ξ ε x (q + u) =
      (trNextStop n ξ ε (fun v => x (q + v)) u).map (q + ·) := by
  have key : ∀ v, IsTrHitAfter n ξ ε x (q + u) (q + v) ↔
      IsTrHitAfter n ξ ε (fun v => x (q + v)) u v := fun v => Iff.rfl
  refine Option.ext fun t => ?_
  rw [trNextStop_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨-, ⟨hlt, hh⟩, hmin⟩
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hh' := (key (u + v + 1)).1 (by rwa [show q + (u + v + 1) = q + u + v + 1 by omega])
    have := hlate _ hh'.isTrHit
    refine ⟨u + v + 1, trNextStop_eq_some_iff.2 ⟨by omega, ⟨by omega, hh'⟩,
      fun s hs hs' => hmin (q + s) (by omega) ⟨by omega, (key s).2 hs'.2⟩⟩, by omega⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨-, ⟨hlt, hh⟩, hmin⟩ := trNextStop_eq_some_iff.1 hv
    have hh' := (key v).2 hh
    refine ⟨hlate _ hh'.isTrHit, ⟨by omega, hh'⟩, fun s hs hs' => ?_⟩
    obtain ⟨hlt', hs₂⟩ := hs'
    obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_lt hlt'
    exact hmin (u + w + 1) (by omega)
      ⟨by omega, (key (u + w + 1)).1 (by rwa [show q + (u + w + 1) = q + u + w + 1 by omega])⟩

/-- **Restart of the stopping sequence**, for any sequence `x` without hits at times
`≥ ⌊n/2⌋`. If `τ_i(x) = q`, then with `x' = x(q + ·)` one has `τ_{i+k}(x) = q + τ_{k+1}(x')`
for every `k` and `ν(x) = (i - 1) + ν(x')`. -/
theorem trStopTime_restart_of_noLateHit (hlate : ∀ t, IsTrHit n ξ ε x t → t < n / 2) {i q : ℕ}
    (hq : trStopTime n ξ ε x i = some q) :
    (∀ k, trStopTime n ξ ε x (i + k) =
        (trStopTime n ξ ε (fun u => x (q + u)) (k + 1)).map (q + ·)) ∧
      trNu n ξ ε x = (i - 1) + trNu n ξ ε (fun u => x (q + u)) := by
  set x' : ℕ → ℤ × ℤ := fun u => x (q + u)
  obtain _ | i := i
  · simp at hq
  have hq' : trStopTime n ξ ε x' 1 = some 0 := by
    rw [trStopTime_one_eq_some_iff]
    refine ⟨?_, ?_, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
    · have := trStopTime_lt hq
      omega
    · simpa [x', IsTrHit] using isTrHit_of_trStopTime_eq_some hq
  have hshift : ∀ k, trStopTime n ξ ε x (i + 1 + k) =
      (trStopTime n ξ ε x' (k + 1)).map (q + ·) := fun k => by
    induction k with
    | zero => simp [hq, hq']
    | succ k ih =>
      rw [show i + 1 + (k + 1) = (i + k) + 2 by omega, trStopTime_succ_succ,
        show i + k + 1 = i + 1 + k by omega, ih, trStopTime_succ_succ (i := k), Option.bind_map,
        Option.map_bind]
      congr 1
      funext u
      exact trNextStop_restart_add hlate q u
  refine ⟨hshift, ?_⟩
  have hiff : ∀ k, i + 1 + k ≤ trNu n ξ ε x ↔ k + 1 ≤ trNu n ξ ε x' := fun k => by
    have h := congrArg Option.isSome (hshift k)
    rw [Option.isSome_map] at h
    have h' := (isSome_trStopTime_iff (n := n) (ξ := ξ) (ε := ε) (x := x)
      (i := i + 1 + k)).symm.trans
      ((Bool.eq_iff_iff.1 h).trans isSome_trStopTime_iff)
    omega
  have h₁ := (hiff (trNu n ξ ε x')).not.2 (by omega)
  have h₂ := (hiff (trNu n ξ ε x - (i + 1))).1
  have h₃ := (isSome_trStopTime_iff.1 (by simp [hq] : (trStopTime n ξ ε x (i + 1)).isSome)).2
  have h₄ := (isSome_trStopTime_iff.1 (by simp [hq'] : (trStopTime n ξ ε x' 1).isSome)).2
  have h₅ := (hiff (trNu n ξ ε x' - 1)).2 (by omega)
  simp only [add_tsub_cancel_right]
  omega

/-- **Restarting the stopping sequence at a stop**. Let `o ∈ 𝒫`, `β` a list of `N` blocks with
`j(o) + N > J = ⌊n/2⌋`, and `x = (x_t(o, β))_t`. If `q = τ_i(x)` (so `i ≥ 1` and `ν(x) ≥ i`) and
`x' = (x_u(x_q(o, β), β_{[q+1,N]}))_u`, then the stopping sequence of `x` is
`(τ_1(x), …, τ_{i-1}(x), q + τ_1(x'), …, q + τ_{ν(x')}(x'))`: that is,
`τ_{i+k}(x) = q + τ_{k+1}(x')` for every `k` (one side being defined iff the other is), and
`ν(x) = (i - 1) + ν(x')`. -/
@[collatz_pos_dens "lem_tr_restart"]
theorem trStopTime_trPath_restart {o : ℤ × ℤ} (ho : o ∈ bkPoints) {β : List (List ℤ × ℤ)}
    (hN : ((n / 2 : ℕ) : ℤ) < bkJ o + β.length) {i q : ℕ}
    (hq : trStopTime n ξ ε (trPath o β) i = some q) :
    (∀ k, trStopTime n ξ ε (trPath o β) (i + k) =
        (trStopTime n ξ ε (trPath (trPath o β q) (trSublist β (q + 1) β.length)) (k + 1)).map
          (q + ·)) ∧
      trNu n ξ ε (trPath o β) =
        (i - 1) + trNu n ξ ε (trPath (trPath o β q) (trSublist β (q + 1) β.length)) := by
  have ho' : 1 ≤ bkJ o := ho
  have hlate : ∀ t, IsTrHit n ξ ε (trPath o β) t → t < n / 2 := fun t ht => by
    have := bkJ_add_le_of_bkJ_trPath_le o β hN ht.bkJ_le
    omega
  have hqN : q ≤ β.length := by
    have := bkJ_add_le_of_bkJ_trPath_le o β hN (isTrHit_of_trStopTime_eq_some hq).bkJ_le
    omega
  have hx' : trPath (trPath o β q) (trSublist β (q + 1) β.length) =
      fun u => trPath o β (q + u) := by
    funext u
    have hsub : trSublist β (q + 1) β.length = β.drop q := by
      rw [trSublist_def, show q + 1 - 1 = q by omega, List.take_of_length_le (by simp)]
    have hlen : (β.take q).length = q := by simp [hqN]
    conv_rhs => rw [← List.take_append_drop q β]
    rw [trPath_append_add o _ _ hlen, hsub]
    congr 1
    conv_lhs => rw [← List.take_append_drop q β]
    rw [trPath_concat o _ _ hlen.ge]
  rw [hx']
  exact trStopTime_restart_of_noLateHit hlate hq

end CollatzPosDens
