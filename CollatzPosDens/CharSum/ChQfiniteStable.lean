/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChInternalWeight
public import CollatzPosDens.CharSum.ChQfinite
public import CollatzPosDens.CharSum.ChRaw3Factor
public import CollatzPosDens.CharSum.ChWhiteFactor

/-!
# Stabilisation of the finite-horizon products

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`, and let `J = ⌊n/2⌋`. If
`J ≤ j(p) + K`, then `Q^{(K + D)}(p) = Q^{(K)}(p)` for every `D ∈ ℕ`.

Write `β ∈ 𝔅^{K + D}` as `β = uv` with `u ∈ 𝔅^K` and `v ∈ 𝔅^D`. Every block point has first
coordinate at least `1`, so `j(Bp_i(β)) ≥ i` for `i ≤ K + D`, and `Bp_i(β) = Bp_i(u)` for
`i ≤ K`. For `K < i ≤ K + D` the point `p + Bp_i(β)` has first coordinate `> J`, and for the
blocks `βᵏ` with `K < k ≤ K + D` every argument of a factor of `I(p + Bp_{k-1}(β); βᵏ)` has
first coordinate `> J`. Such points are not white, so the corresponding factors are `1`, and the
term of `Q^{(K + D)}(p)` at `uv` is the term of `Q^{(K)}(p)` at `u` times `∏_k bw(vᵏ)`. Summing
over `v` first, using `∑_{v ∈ 𝔅^D} ∏_k bw(vᵏ) = 1`, gives `Q^{(K)}(p)`.

## Main results

* `CollatzPosDens.chQFinite_add_of_le`: if `⌊n/2⌋ ≤ j(p) + K` then
  `Q^{(K + D)}(p) = Q^{(K)}(p)`.

## Implementation notes

The base point `p` ranges over all of `ℤ × ℤ` and the threshold `ε` is arbitrary; no hypothesis
`p ∈ 𝒫` is needed. The splitting `β = uv` is the equivalence `Fin.appendEquiv` between
`𝔅^K × 𝔅^D` and `𝔅^{K + D}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The first coordinate of the block path is at least the number of blocks read:
`j(Bp_i(β)) ≥ min(i, K)`. -/
private lemma chBlockPath_fst_ge (β : List (List ℤ × ℤ)) (i : ℕ) :
    ((min i β.length : ℕ) : ℤ) ≤ (chBlockPath β i).1 := by
  rw [chBlockPath_fst]
  refine le_add_of_nonneg_right (List.sum_nonneg ?_)
  simp only [List.mem_map]
  rintro _ ⟨b, -, rfl⟩
  positivity

/-- The internal weight of a block started at a point `x` with `⌊n/2⌋ ≤ j(x)` is `1`: every
argument of its factors has first coordinate `> ⌊n/2⌋`, hence is not white. -/
private lemma chInternalWeight_eq_one_of_le {n : ℕ} (ξ : ResidueGroup n) (ε : ℝ) {x : ℤ × ℤ}
    (hx : ((n / 2 : ℕ) : ℤ) ≤ bkJ x) (b : List ℤ × ℤ) :
    chInternalWeight n ξ ε x b = 1 := by
  refine Finset.prod_eq_one fun i _ ↦ chRaw3Factor_of_not_isBkWhite fun hw ↦ ?_
  have := hw.bkJ_le
  simp only [bkJ, Prod.fst_add] at this hx
  omega

/-- Reading the blocks of a concatenation `Fin.append u v` gives the concatenated block lists. -/
private lemma ofFn_val_fin_append {α : Type*} {P : α → Prop} {K D : ℕ}
    (u : Fin K → Subtype P) (v : Fin D → Subtype P) :
    (List.ofFn fun k ↦ (Fin.append u v k).1) =
      (List.ofFn fun k ↦ (u k).1) ++ List.ofFn fun k ↦ (v k).1 := by
  rw [← List.ofFn_fin_append]
  congr 1
  funext k
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) k <;> simp

/-- Past the stabilisation horizon, the extra internal weights of a concatenation are `1`. -/
private lemma prod_chInternalWeight_fin_append (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {K D : ℕ}
    {p : ℤ × ℤ} (hK : ((n / 2 : ℕ) : ℤ) ≤ bkJ p + K)
    (u : Fin K → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)})
    (v : Fin D → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) :
    ∏ k : Fin (K + D), chInternalWeight n ξ ε
        (p + chBlockPath (List.ofFn fun k ↦ (Fin.append u v k).1) k) (Fin.append u v k).1 =
      ∏ k : Fin K, chInternalWeight n ξ ε
        (p + chBlockPath (List.ofFn fun k ↦ (u k).1) k) (u k).1 := by
  have hlen : (List.ofFn fun k ↦ (Fin.append u v k).1).length = K + D := by simp
  rw [Fin.prod_univ_add]
  have h2 : ∀ k : Fin D, chInternalWeight n ξ ε
      (p + chBlockPath (List.ofFn fun k ↦ (Fin.append u v k).1) (Fin.natAdd K k))
      (Fin.append u v (Fin.natAdd K k)).1 = 1 := by
    intro k
    refine chInternalWeight_eq_one_of_le ξ ε ?_ _
    have hg := chBlockPath_fst_ge (List.ofFn fun k ↦ (Fin.append u v k).1) (Fin.natAdd K k)
    rw [hlen, show min (↑(Fin.natAdd K k) : ℕ) (K + D) = K + k by simp] at hg
    simp only [bkJ, Prod.fst_add] at hK ⊢
    push_cast at hg
    omega
  rw [Finset.prod_congr rfl fun k _ ↦ h2 k, Finset.prod_const_one, mul_one]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [Fin.append_left, ofFn_val_fin_append, chBlockPath_append_of_le _ _ (by simp)]
  simp

/-- The term at a concatenation `uv` factors as the term at `u` times the block weights of `v`. -/
private lemma chQFiniteTerm_fin_append (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {K D : ℕ}
    {p : ℤ × ℤ} (hK : ((n / 2 : ℕ) : ℤ) ≤ bkJ p + K)
    (u : Fin K → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)})
    (v : Fin D → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) :
    chQFiniteTerm n ξ ε (K + D) p (Fin.append u v) =
      chQFiniteTerm n ξ ε K p u * ∏ k, chBlockWeight (v k) := by
  have hlen : (List.ofFn fun k ↦ (Fin.append u v k).1).length = K + D := by simp
  unfold chQFiniteTerm
  rw [Fin.prod_univ_add (f := fun k ↦ chBlockWeight (Fin.append u v k).1)]
  simp only [Fin.append_left, Fin.append_right]
  have hW : ∏ i ∈ Finset.range (K + D + 1),
      chWhiteFactor n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (Fin.append u v k).1) i) =
      ∏ i ∈ Finset.range (K + 1),
        chWhiteFactor n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (u k).1) i) := by
    rw [show K + D + 1 = (K + 1) + D by omega, Finset.prod_range_add]
    have h2 : ∀ x ∈ Finset.range D, chWhiteFactor n ξ ε (p + chBlockPath
        (List.ofFn fun k ↦ (Fin.append u v k).1) (K + 1 + x)) = 1 := by
      intro x hx
      refine chWhiteFactor_of_not_isBkWhite fun hwh ↦ ?_
      have hg := chBlockPath_fst_ge (List.ofFn fun k ↦ (Fin.append u v k).1) (K + 1 + x)
      have := hwh.bkJ_le
      simp only [Finset.mem_range] at hx
      simp only [bkJ, Prod.fst_add] at this hK
      rw [hlen, show min (K + 1 + x) (K + D) = K + 1 + x by omega] at hg
      push_cast at hg
      omega
    rw [Finset.prod_congr rfl h2, Finset.prod_const_one, mul_one]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    simp only [Finset.mem_range] at hi
    rw [ofFn_val_fin_append, chBlockPath_append_of_le _ _ (by simp; omega)]
  rw [hW, prod_chInternalWeight_fin_append n ξ ε hK u v]
  ring

/-- **Stabilisation of the finite-horizon products.** If `⌊n/2⌋ ≤ j(p) + K`, then
`Q^{(K + D)}(p) = Q^{(K)}(p)` for every `D ∈ ℕ`. -/
@[collatz_pos_dens "lem_ch_Qfinite_stable"]
theorem chQFinite_add_of_le (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {K : ℕ} {p : ℤ × ℤ}
    (hK : ((n / 2 : ℕ) : ℤ) ≤ bkJ p + K) (D : ℕ) :
    chQFinite n ξ ε (K + D) p = chQFinite n ξ ε K p := by
  let F := chQFiniteTerm n ξ ε (K + D) p
  let f : (Fin K → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) ×
      (Fin D → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) → ℝ :=
    fun x ↦ chQFiniteTerm n ξ ε K p x.1 * ∏ k, chBlockWeight (x.2 k)
  have hFf : F ∘ Fin.appendEquiv K D = f :=
    funext fun x ↦ chQFiniteTerm_fin_append n ξ ε hK x.1 x.2
  have hfsum : Summable f :=
    hFf ▸ (Equiv.summable_iff _).mpr (summable_chQFiniteTerm n ξ ε (K + D) p)
  have key := hfsum.hasSum.prod_fiberwise
    fun u ↦ (hasSum_prod_chBlockWeight D).mul_left (chQFiniteTerm n ξ ε K p u)
  rw [show ∑' x, f x = ∑' β, F β from hFf ▸ (Fin.appendEquiv K D).tsum_eq F] at key
  simp only [mul_one] at key
  rw [chQFinite_eq_tsum, chQFinite_eq_tsum]
  exact key.tsum_eq.symm

end CollatzPosDens
