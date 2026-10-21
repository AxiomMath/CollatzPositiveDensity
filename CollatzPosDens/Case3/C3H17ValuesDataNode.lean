/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataU
public import CollatzPosDens.Case3.C3H17ValuesDataNodeTabA
public import CollatzPosDens.Case3.C3H17ValuesDataNodeTabB
public import CollatzPosDens.Case3.C3H17Node

/-!
# Certifying the rounded future costs

For `1 ≤ h ≤ 14` the rounded future cost at `z = ± 3^J` is
`10^8 cf⁺_h(z) = ⌈(2^{16} 10^{24} - 10^8 ∑_{d=2}^{17-h} (d - 1) 2^{16-d} (10^{16} - u_d g_d)) /
(2^{16} 10^{16})⌉`, where `u_d = 10^8 Ū_d(z / 2^{h+d})` and `g_d = 10^8 cf⁺_{h+d}(9 z)` when
`d ∉ {4, 5}` and `h + d ≤ 14`, `g_d = 10^8` otherwise; here `z / 2^{h+d} = ± 2^{17-h-d} 3^J / 2^17`
and `9 z = ± 3^{J+2}`.

The values `10^8 cf⁺_h(3^J)`, `J < 2^15`, are recorded in a table. A check of `n` consecutive
points `J = a, …, a + n - 1` of level `h` recomputes the right side above from the table at the
higher levels and the majorants `u_d`, and compares. Once the checks of level `h` cover
`J < 2^15` and the higher levels are certified, the table at level `h` is certified at every
point `± 3^J`, since `3^{2^15} ≡ 1 (mod 2^17)` and `cf⁺_h` has period `2^17`.

## Main definitions

* `CollatzPosDens.C3H17Values.nodeVal`: the recorded value at level `h` and index `J`.
* `CollatzPosDens.C3H17Values.nodeCheck`: the check of `n` consecutive points of level `h`.

## Main results

* `CollatzPosDens.C3H17Values.c3H17Node_eq_ceil`: the rounded future cost as an exact natural
  ceiling division.
* `CollatzPosDens.C3H17Values.nodeVal_of_nodeCheck`: a passing check certifies its points.
* `CollatzPosDens.C3H17Values.nodeVal_spec_of_checks`: the checks of a level certify it.
-/

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

open Finset

/-! ### The table -/

/-- The packed values of the `14` levels, preceded by an empty level `0`. -/
def nodeLevels : List (List ℕ) :=
  [[], nodeLevel1, nodeLevel2, nodeLevel3, nodeLevel4, nodeLevel5, nodeLevel6, nodeLevel7,
    nodeLevel8, nodeLevel9, nodeLevel10, nodeLevel11, nodeLevel12, nodeLevel13, nodeLevel14]

/-- The packed number of index `q` of level `h`. -/
def nodeChunk (h q : ℕ) : ℕ := (nodeLevels.getD h []).getD q 0

/-- The recorded value at level `h` and index `J < 2^15`: lane `J mod 256` of the packed number
of index `⌊J / 256⌋`. -/
def nodeVal (h J : ℕ) : ℕ := lane 32 (nodeChunk h (J / 256)) (J % 256)

/-- The values of level `h` as one packed number of width `32`, `1 ≤ h ≤ 14`: lane `J` is
`nodeVal h J`. Each level is a separate constant, so that the kernel packs it once per
declaration. -/
noncomputable def nodeBig1 : ℕ := packR (32 * 256) nodeLevel1
@[inherit_doc nodeBig1]
noncomputable def nodeBig2 : ℕ := packR (32 * 256) nodeLevel2
@[inherit_doc nodeBig1]
noncomputable def nodeBig3 : ℕ := packR (32 * 256) nodeLevel3
@[inherit_doc nodeBig1]
noncomputable def nodeBig4 : ℕ := packR (32 * 256) nodeLevel4
@[inherit_doc nodeBig1]
noncomputable def nodeBig5 : ℕ := packR (32 * 256) nodeLevel5
@[inherit_doc nodeBig1]
noncomputable def nodeBig6 : ℕ := packR (32 * 256) nodeLevel6
@[inherit_doc nodeBig1]
noncomputable def nodeBig7 : ℕ := packR (32 * 256) nodeLevel7
@[inherit_doc nodeBig1]
noncomputable def nodeBig8 : ℕ := packR (32 * 256) nodeLevel8
@[inherit_doc nodeBig1]
noncomputable def nodeBig9 : ℕ := packR (32 * 256) nodeLevel9
@[inherit_doc nodeBig1]
noncomputable def nodeBig10 : ℕ := packR (32 * 256) nodeLevel10
@[inherit_doc nodeBig1]
noncomputable def nodeBig11 : ℕ := packR (32 * 256) nodeLevel11
@[inherit_doc nodeBig1]
noncomputable def nodeBig12 : ℕ := packR (32 * 256) nodeLevel12
@[inherit_doc nodeBig1]
noncomputable def nodeBig13 : ℕ := packR (32 * 256) nodeLevel13
@[inherit_doc nodeBig1]
noncomputable def nodeBig14 : ℕ := packR (32 * 256) nodeLevel14

/-- The packed levels `nodeBig1, …, nodeBig14`, preceded by an empty level `0`. -/
noncomputable def nodeBigs : List ℕ :=
  [0, nodeBig1, nodeBig2, nodeBig3, nodeBig4, nodeBig5, nodeBig6, nodeBig7, nodeBig8, nodeBig9,
    nodeBig10, nodeBig11, nodeBig12, nodeBig13, nodeBig14]

/-- Entry `h` of `nodeBigs` is level `h` of the table packed at width `32 * 256`. -/
theorem getR_nodeBigs (h : ℕ) : getR 0 nodeBigs h = packR (32 * 256) (nodeLevels.getD h []) := by
  by_cases hh : h ≤ 14
  · interval_cases h <;> rfl
  · rw [getR_eq, List.getD_eq_default _ _ (by simp [nodeBigs]; omega),
      List.getD_eq_default _ _ (by simp [nodeLevels]; omega)]
    rfl

/-- Every level of the table has at most `128` packed numbers, each below `2^8192`. -/
theorem nodeLevels_ok : ∀ h ∈ List.range 15, (Nat.ble (nodeLevels.getD h []).length 128 &&
    (nodeLevels.getD h []).all (fun x => Nat.blt x (2 ^ (32 * 256)))) = true := by
  decide +kernel

/-- Every packed number of level `h` of the table is below `2^8192`. -/
theorem nodeLevels_lt (h : ℕ) {x : ℕ} (hx : x ∈ nodeLevels.getD h []) : x < 2 ^ (32 * 256) := by
  by_cases hh : h ≤ 14
  · have := nodeLevels_ok h (List.mem_range.2 (by omega))
    rw [Bool.and_eq_true, List.all_eq_true] at this
    have h' := this.2 x hx
    rwa [Nat.blt_eq] at h'
  · rw [List.getD_eq_default _ _ (by simp [nodeLevels]; omega)] at hx
    simp at hx

/-- Every level of the table has at most `128` packed numbers. -/
theorem length_nodeLevels (h : ℕ) : (nodeLevels.getD h []).length ≤ 128 := by
  by_cases hh : h ≤ 14
  · have := nodeLevels_ok h (List.mem_range.2 (by omega))
    rw [Bool.and_eq_true, Nat.ble_eq] at this
    exact this.1
  · rw [List.getD_eq_default _ _ (by simp [nodeLevels]; omega)]
    simp

/-- Lane `J` of entry `h` of `nodeBigs` is `nodeVal h J`. -/
theorem lane_getR_nodeBigs (h J : ℕ) : lane 32 (getR 0 nodeBigs h) J = nodeVal h J := by
  have e := lane_lane (w := 32) (packR (32 * 256) (nodeLevels.getD h [])) (J / 256)
    (Nat.mod_lt J (show 0 < 256 by norm_num))
  rw [Nat.div_add_mod] at e
  rw [getR_nodeBigs, ← e, lane_packR]
  · rfl
  · intro i _
    rw [List.getD_eq_getElem?_getD]
    rcases hx : (nodeLevels.getD h [])[i]? with _ | x
    · rw [Option.getD_none]
      positivity
    · rw [Option.getD_some]
      exact nodeLevels_lt h (List.mem_of_getElem? hx)

/-- Level `h` packed twice: lanes `J` and `2^15 + J` both hold `nodeVal h J`, `J < 2^15`. -/
noncomputable def nodeDbl (h : ℕ) : ℕ :=
  getR 0 nodeBigs h + getR 0 nodeBigs h <<< (32 * 32768)

/-- For `J < 2^16`, lane `J` of `nodeDbl h` is `nodeVal h (J mod 2^15)`. -/
theorem lane_nodeDbl (h : ℕ) {J : ℕ} (hJ : J < 2 ^ 16) :
    lane 32 (nodeDbl h) J = nodeVal h (J % 2 ^ 15) := by
  have hX : getR 0 nodeBigs h < 2 ^ (32 * 32768) := by
    have h1 := packR_lt (w := 32 * 256) (l := nodeLevels.getD h []) fun x hx => nodeLevels_lt h hx
    have h3 : 32 * 256 * (nodeLevels.getD h []).length ≤ 32 * 32768 := by
      have := length_nodeLevels h; omega
    exact (getR_nodeBigs h).trans_lt (lt_of_lt_of_le h1 (pow_le_pow_right₀ (by norm_num) h3))
  unfold nodeDbl
  rw [add_shiftLeft_eq, lane_add_mul hX]
  split_ifs with hlt
  · rw [lane_getR_nodeBigs, Nat.mod_eq_of_lt (by omega : J < 2 ^ 15)]
  · rw [lane_getR_nodeBigs, show J - 32768 = J % 2 ^ 15 by omega]

/-- The recorded values at level `h` and indices `(s + k) mod 2^15`, `k < n`, for `n ≤ 2^15`: the
lanes `s mod 2^15, …` of the doubled level, unpacked `256` at a time. -/
noncomputable def nodeSeg (h s n : ℕ) : List ℕ :=
  chunksR (n / 256) (n % 256) (Nat.shiftRight (nodeDbl h) (Nat.mul 32 (Nat.mod s 32768)))

/-- The segment `nodeSeg h s n` has length `n`. -/
theorem length_nodeSeg (h s n : ℕ) : (nodeSeg h s n).length = n := by
  rw [nodeSeg, chunksR_eq (Nat.mod_lt _ (by norm_num)).le, List.length_map, List.length_range]
  omega

/-- For `n ≤ 2^15` and `k < n`, entry `k` of `nodeSeg h s n` is `nodeVal h ((s + k) mod 2^15)`. -/
theorem nodeSeg_getD {h s n k : ℕ} (hn : n ≤ 2 ^ 15) (hk : k < n) :
    (nodeSeg h s n).getD k 0 = nodeVal h ((s + k) % 2 ^ 15) := by
  rw [nodeSeg, chunksR_eq (Nat.mod_lt _ (by norm_num)).le, getD_map_range _ (by omega)]
  change lane 32 (nodeDbl h >>> (32 * (s % 32768))) k = _
  rw [Nat.shiftRight_eq_div_pow, lane_div,
    lane_nodeDbl h (by have := Nat.mod_lt s (show 0 < 32768 by norm_num); omega)]
  congr 1
  omega

/-! ### The rounded future cost as a natural ceiling division -/

/-- The weight `(d - 1) 2^{16 - d}`, that is `2^{16} ϖ(d)`. -/
def nodeW (d : ℕ) : ℕ := (d - 1) * 2 ^ (16 - d)

/-- The constant `2^{16} 10^{24}`. -/
def nodeA : ℕ := 2 ^ 16 * 10 ^ 24

/-- The constant `2^{16} 10^{16}`. -/
def nodeK : ℕ := 2 ^ 16 * 10 ^ 16

/-- The sum of `f` over the list `s, …, s + n - 1` is `∑_{i < n} f (s + i)`. -/
theorem sum_range'_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (s n : ℕ) :
    ((List.range' s n).map f).sum = ∑ i ∈ range n, f (s + i) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, List.sum_cons, ih, sum_range_succ',
      add_comm (∑ i ∈ range n, f (s + (i + 1))), add_zero]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [Nat.add_assoc, Nat.add_comm 1 i]

/-- For `h ≤ 15`, the sum of `f` over the integers `2 ≤ d ≤ 17 - h` is its sum over the list
`2, …, 17 - h` of naturals. -/
theorem sum_Icc_two_eq {M : Type*} [AddCommMonoid M] (f : ℤ → M) {h : ℕ} (hh : h ≤ 15) :
    ∑ d ∈ Icc (2 : ℤ) (17 - h), f d = ((List.range' 2 (16 - h)).map fun d : ℕ => f d).sum := by
  rw [Int.Icc_eq_finset_map, sum_map, sum_range'_eq_sum_range,
    show ((17 - h : ℤ) + 1 - 2).toNat = 16 - h by omega]
  refine sum_congr rfl fun i _ => ?_
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  push_cast
  ring_nf

/-- For `1 ≤ h ≤ 14`, if `uu d = 10^8 Ū_d(z / 2^{h+d})` and `gg d = 10^8 G_d` are at most `10^8`
for `2 ≤ d ≤ 17 - h`, and `S = ∑_d nodeW d (10^{16} - uu d gg d)` satisfies `10^8 S ≤ nodeA`, then
`10^8 cf⁺_h(z) = ⌊(nodeA - 10^8 S + nodeK - 1) / nodeK⌋`. -/
theorem c3H17Node_eq_ceil {h : ℕ} (h1 : 1 ≤ h) (h14 : h ≤ 14) (z : ℤ) (uu gg : ℕ → ℕ)
    (hu : ∀ d ∈ List.range' 2 (16 - h),
      (uu d : ℚ) = 10 ^ 8 * c3H17CapUp d ((z : ℚ) / 2 ^ ((h : ℤ) + d)))
    (hg : ∀ d ∈ List.range' 2 (16 - h), (gg d : ℚ) = 10 ^ 8 *
      (if (d : ℤ) ∉ ({4, 5} : Finset ℤ) ∧ (h : ℤ) + d ≤ 15 then c3H17Node ((h : ℤ) + d) (9 * z)
        else 1))
    (hub : ∀ d ∈ List.range' 2 (16 - h), uu d ≤ 10 ^ 8)
    (hgb : ∀ d ∈ List.range' 2 (16 - h), gg d ≤ 10 ^ 8)
    (hA : 10 ^ 8 * ((List.range' 2 (16 - h)).map fun d => nodeW d * (10 ^ 16 - uu d * gg d)).sum ≤
      nodeA) :
    (10 ^ 8 : ℚ) * c3H17Node h z =
      ((nodeA - 10 ^ 8 * ((List.range' 2 (16 - h)).map fun d =>
        nodeW d * (10 ^ 16 - uu d * gg d)).sum + nodeK - 1) / nodeK : ℕ) := by
  set S := ((List.range' 2 (16 - h)).map fun d => nodeW d * (10 ^ 16 - uu d * gg d)).sum with hS
  rw [c3H17Node_of_lt (by omega), sum_Icc_two_eq _ (by omega)]
  have hterm : ∀ d ∈ List.range' 2 (16 - h),
      (((d : ℤ) : ℚ) - 1) * (2 : ℚ) ^ (-(d : ℤ)) *
        (1 - c3H17CapUp d ((z : ℚ) / 2 ^ ((h : ℤ) + d)) *
          (if (d : ℤ) ∉ ({4, 5} : Finset ℤ) ∧ (h : ℤ) + d ≤ 15 then c3H17Node ((h : ℤ) + d) (9 * z)
            else 1)) =
      ((nodeW d * (10 ^ 16 - uu d * gg d) : ℕ) : ℚ) / (2 ^ 16 * 10 ^ 16) := by
    intro d hd
    rw [List.mem_range'_1] at hd
    have hug : uu d * gg d ≤ 10 ^ 16 := by
      calc uu d * gg d ≤ 10 ^ 8 * 10 ^ 8 :=
            Nat.mul_le_mul (hub d (List.mem_range'_1.2 hd)) (hgb d (List.mem_range'_1.2 hd))
        _ = 10 ^ 16 := by norm_num
    have hU : c3H17CapUp d ((z : ℚ) / 2 ^ ((h : ℤ) + d)) = (uu d : ℚ) / 10 ^ 8 := by
      rw [hu d (List.mem_range'_1.2 hd)]; ring
    have hG : (if (d : ℤ) ∉ ({4, 5} : Finset ℤ) ∧ (h : ℤ) + d ≤ 15 then
        c3H17Node ((h : ℤ) + d) (9 * z) else 1) = (gg d : ℚ) / 10 ^ 8 := by
      rw [hg d (List.mem_range'_1.2 hd)]; ring
    have h2 : (2 : ℚ) ^ (-(d : ℤ)) = 2 ^ (16 - d) / 2 ^ 16 := by
      rw [zpow_neg, zpow_natCast, show (2 : ℚ) ^ 16 = 2 ^ (16 - d) * 2 ^ d by
        rw [← pow_add]; congr 1; omega]
      field_simp
    have hcast : ((nodeW d * (10 ^ 16 - uu d * gg d) : ℕ) : ℚ) =
        ((d : ℚ) - 1) * 2 ^ (16 - d) * (10 ^ 16 - (uu d : ℚ) * gg d) := by
      rw [nodeW, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hug, Nat.cast_sub (show 1 ≤ d by omega)]
      push_cast
      ring
    rw [hU, hG, h2, hcast]
    push_cast
    field_simp
  have hsum : ((List.range' 2 (16 - h)).map fun d : ℕ =>
      (((d : ℤ) : ℚ) - 1) * (2 : ℚ) ^ (-(d : ℤ)) *
        (1 - c3H17CapUp d ((z : ℚ) / 2 ^ ((h : ℤ) + d)) *
          (if (d : ℤ) ∉ ({4, 5} : Finset ℤ) ∧ (h : ℤ) + d ≤ 15 then c3H17Node ((h : ℤ) + d) (9 * z)
            else 1))).sum = (S : ℚ) / (2 ^ 16 * 10 ^ 16) := by
    rw [List.map_congr_left hterm, hS, Nat.cast_list_sum, List.map_map]
    have hdiv : ∀ (l : List ℕ) (f : ℕ → ℕ) (c : ℚ),
        (l.map fun d => ((f d : ℕ) : ℚ) / c).sum = (l.map ((Nat.cast : ℕ → ℚ) ∘ f)).sum / c := by
      intro l f c
      induction l with
      | nil => simp
      | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, add_div, Function.comp]
    exact hdiv _ (fun d => nodeW d * (10 ^ 16 - uu d * gg d)) _
  rw [hsum]
  have hX : (10 ^ 8 : ℚ) * (1 - (S : ℚ) / (2 ^ 16 * 10 ^ 16)) =
      ((nodeA - 10 ^ 8 * S : ℕ) : ℚ) / (nodeK : ℕ) := by
    rw [Nat.cast_sub hA]
    simp only [nodeA, nodeK]
    push_cast
    field_simp
    ring
  have hK : 0 < nodeK := by unfold nodeK; positivity
  rw [hX, Rat.ceil_natCast_div_natCast,
    ← Int.cast_natCast (R := ℚ) ((nodeA - 10 ^ 8 * S + nodeK - 1) / nodeK),
    ceilDiv_cast _ _ hK]
  push_cast
  field_simp

/-! ### The check of consecutive points -/

/-- Whether the factor `G_d` at level `h` is a recorded future cost: `d ∉ {4, 5}` and
`h + d ≤ 14`. -/
def nodeHasG (h d : ℕ) : Bool := (d != 4 && d != 5) && Nat.ble (h + d) 14

/-- The list of the terms `(d - 1) 2^{16-d} (10^{16} - u_d g_d)` at the points `a, …, a + n - 1`
of level `h`. -/
noncomputable def nodeTerm (h a n d : ℕ) : List ℕ :=
  if d = 2 then
    cond (nodeHasG h 2)
      (mapR (fun g => Nat.mul (nodeW 2) (Nat.sub 10000000000000000 (Nat.mul 100000000 g)))
        (nodeSeg (h + 2) (a + 2) n))
      (rangeMap (fun _ => 0) n)
  else
    cond (nodeHasG h d)
      (zipR (fun u g => Nat.mul (nodeW d) (Nat.sub 10000000000000000 (Nat.mul u g)))
        (uSeg d (17 - h - d) a n) (nodeSeg (h + d) (a + 2) n))
      (mapR (fun u => Nat.mul (nodeW d) (Nat.sub 10000000000000000 (Nat.mul u 100000000)))
        (uSeg d (17 - h - d) a n))

/-- The sums `∑_{d=2}^{17-h} (d - 1) 2^{16-d} (10^{16} - u_d g_d)` at the points
`a, …, a + n - 1` of level `h`. -/
noncomputable def nodeAcc (h a n : ℕ) : List ℕ :=
  (List.range' 2 (16 - h)).foldr (fun d acc => zipR Nat.add (nodeTerm h a n d) acc)
    (rangeMap (fun _ => 0) n)

/-- The check of the recorded values at the points `a, …, a + n - 1` of level `h`. -/
noncomputable def nodeCheck (h a n : ℕ) : Bool :=
  allZipR (fun nv acc => Nat.ble (Nat.mul 100000000 acc) nodeA &&
      Nat.beq nv
        (Nat.div (Nat.sub (Nat.add (Nat.sub nodeA (Nat.mul 100000000 acc)) nodeK) 1) nodeK))
    (nodeSeg h a n) (nodeAcc h a n)

/-- The factor `u_d` used by `nodeTerm` at the point `a + k`. -/
noncomputable def nodeU (h a n d k : ℕ) : ℕ :=
  if d = 2 then 10 ^ 8 else (uSeg d (17 - h - d) a n).getD k 0

/-- The factor `g_d` used by `nodeTerm` at the point `a + k`. -/
noncomputable def nodeG (h a n d k : ℕ) : ℕ :=
  if nodeHasG h d = true then (nodeSeg (h + d) (a + 2) n).getD k 0 else 10 ^ 8

/-- Below both lengths, entry `k` of `zipR f l l'` is `f` of the entries `k` of `l` and `l'`. -/
theorem getD_zipR {f : ℕ → ℕ → ℕ} {l l' : List ℕ} {k : ℕ} (hk : k < l.length)
    (hk' : k < l'.length) : (zipR f l l').getD k 0 = f (l.getD k 0) (l'.getD k 0) := by
  rw [zipR_eq, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem hk']
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk']

/-- Below the length of `l`, entry `k` of `mapR f l` is `f` of entry `k` of `l`. -/
theorem getD_mapR {f : ℕ → ℕ} {l : List ℕ} {k : ℕ} (hk : k < l.length) :
    (mapR f l).getD k 0 = f (l.getD k 0) := by
  rw [mapR_eq]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- The segment hypotheses: `256 ∣ n`, and for every `v ≤ 16` either `n ≤ p_v` or
`p_v ∣ a`, `p_v ∣ n`. -/
def NodeSegOK (a n : ℕ) : Prop :=
  256 ∣ n ∧ ∀ v ≤ 16, n ≤ cosPer v ∨ (cosPer v ∣ a ∧ cosPer v ∣ n)

/-- Under the segment hypotheses, `uSeg d (17 - h - d) a n` has length `n`. -/
theorem length_uSeg_node {h a n d : ℕ} (h1 : 1 ≤ h) (hs : NodeSegOK a n) :
    (uSeg d (17 - h - d) a n).length = n := by
  rcases hs.2 (17 - h - d) (by omega) with h' | h'
  · exact length_uSeg hs.1 (Or.inl h')
  · exact length_uSeg hs.1 (Or.inr h'.2)

/-- Under the segment hypotheses, `nodeTerm h a n d` has length `n`. -/
theorem length_nodeTerm {h a n d : ℕ} (h1 : 1 ≤ h) (hs : NodeSegOK a n) :
    (nodeTerm h a n d).length = n := by
  have hu := length_uSeg_node (d := d) h1 hs
  unfold nodeTerm
  split_ifs
  · cases nodeHasG h 2 <;> simp only [Bool.cond_true, Bool.cond_false]
    · exact length_rangeMap _ _
    · rw [mapR_eq, List.length_map, length_nodeSeg]
  · cases nodeHasG h d <;> simp only [Bool.cond_true, Bool.cond_false]
    · rw [mapR_eq, List.length_map, hu]
    · rw [zipR_eq, List.length_zipWith, hu, length_nodeSeg, min_self]

/-- Under the segment hypotheses, entry `k < n` of `nodeTerm h a n d` is
`nodeW d (10^{16} - u_d g_d)`, with `u_d = nodeU h a n d k` and `g_d = nodeG h a n d k`. -/
theorem getD_nodeTerm {h a n d k : ℕ} (h1 : 1 ≤ h) (hs : NodeSegOK a n) (hk : k < n) :
    (nodeTerm h a n d).getD k 0 = nodeW d * (10 ^ 16 - nodeU h a n d k * nodeG h a n d k) := by
  have hu := length_uSeg_node (d := d) h1 hs
  by_cases h2 : d = 2
  · subst h2
    have hU : nodeU h a n 2 k = 10 ^ 8 := by simp [nodeU]
    rw [hU]
    unfold nodeTerm
    rw [ite_eq_left rfl]
    cases hg : nodeHasG h 2 <;> simp only [Bool.cond_true, Bool.cond_false]
    · rw [getD_rangeMap _ hk, nodeG, ite_eq_right (by simp [hg])]
      norm_num
    · rw [getD_mapR (by rw [length_nodeSeg]; exact hk), nodeG, ite_eq_left hg]
      rfl
  · have hU : nodeU h a n d k = (uSeg d (17 - h - d) a n).getD k 0 := by simp [nodeU, h2]
    rw [hU]
    unfold nodeTerm
    rw [ite_eq_right h2]
    cases hg : nodeHasG h d <;> simp only [Bool.cond_true, Bool.cond_false]
    · rw [getD_mapR (by rw [hu]; exact hk), nodeG, ite_eq_right (by simp [hg])]
      rfl
    · rw [getD_zipR (by rw [hu]; exact hk) (by rw [length_nodeSeg]; exact hk), nodeG,
        ite_eq_left hg]
      rfl

/-- Under the segment hypotheses, entry `k < n` of `nodeAcc h a n` is
`∑_{d=2}^{17-h} nodeW d (10^{16} - u_d g_d)`, with `u_d = nodeU h a n d k` and
`g_d = nodeG h a n d k`. -/
theorem getD_nodeAcc {h a n k : ℕ} (h1 : 1 ≤ h) (hs : NodeSegOK a n) (hk : k < n) :
    (nodeAcc h a n).getD k 0 = ((List.range' 2 (16 - h)).map fun d =>
      nodeW d * (10 ^ 16 - nodeU h a n d k * nodeG h a n d k)).sum := by
  unfold nodeAcc
  generalize List.range' 2 (16 - h) = L
  have hlen : ∀ L : List ℕ, (L.foldr (fun d acc => zipR Nat.add (nodeTerm h a n d) acc)
      (rangeMap (fun _ => 0) n)).length = n := by
    intro L
    induction L with
    | nil => exact length_rangeMap _ _
    | cons d L ih => rw [List.foldr_cons, zipR_eq, List.length_zipWith, length_nodeTerm h1 hs, ih,
        min_self]
  induction L with
  | nil => rw [List.foldr_nil, getD_rangeMap _ hk]; simp
  | cons d L ih =>
    rw [List.foldr_cons, getD_zipR (by rw [length_nodeTerm h1 hs]; exact hk)
      (by rw [hlen]; exact hk), ih, getD_nodeTerm h1 hs hk, List.map_cons, List.sum_cons]
    rfl

/-- A recorded value equal to `10^8 cf⁺_h(σ 3^J)` is at most `10^8`. -/
theorem nodeVal_le {h J : ℕ} {σ : ℤ}
    (hspec : (nodeVal h (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node h (σ * 3 ^ J)) :
    nodeVal h (J % 2 ^ 15) ≤ 10 ^ 8 := by
  have := c3H17Node_le_one h (σ * 3 ^ J)
  have : (nodeVal h (J % 2 ^ 15) : ℚ) ≤ 10 ^ 8 := by rw [hspec]; nlinarith
  exact_mod_cast this

/-- For `3 ≤ c ≤ 16`, `v ≤ 16` and the segment hypotheses, every entry of `uSeg c v a n` is at
most `10^8`. -/
theorem uSeg_le {c : ℕ} (hc3 : 3 ≤ c) (hc : c ≤ 16) {v : ℕ} (hv : v ≤ 16) {a n k : ℕ}
    (hn : 256 ∣ n) (h : n ≤ cosPer v ∨ (cosPer v ∣ a ∧ cosPer v ∣ n)) (hk : k < n) :
    (uSeg c v a n).getD k 0 ≤ 10 ^ 8 := by
  have hs := uSeg_spec hc3 hc hv hn h hk (σ := 1) (Or.inl rfl)
  have := c3H17CapUp_le_one c (((1 : ℤ) * 2 ^ v * 3 ^ (a + k) : ℤ) / 2 ^ 17)
  have : ((uSeg c v a n).getD k 0 : ℚ) ≤ 10 ^ 8 := by rw [hs]; nlinarith
  exact_mod_cast this

/-- For `v + h + d = 17`, `σ 3^J / 2^{h+d} = σ 2^v 3^J / 2^17`. -/
theorem div_two_pow_eq {h d v : ℕ} (hv : v + h + d = 17) (σ : ℤ) (J : ℕ) :
    ((σ * 3 ^ J : ℤ) : ℚ) / 2 ^ ((h : ℤ) + d) = ((σ * 2 ^ v * 3 ^ J : ℤ) : ℚ) / 2 ^ 17 := by
  rw [show ((h : ℤ) + d) = ((h + d : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [show (2 : ℚ) ^ 17 = 2 ^ v * 2 ^ (h + d) by rw [← pow_add]; congr 1; omega]
  push_cast
  field_simp

/-- A passing check certifies the recorded values at its points, given the higher levels. -/
theorem nodeVal_of_nodeCheck {h a n : ℕ} (h1 : 1 ≤ h) (h14 : h ≤ 14) (hs : NodeSegOK a n)
    (han : a + n ≤ 2 ^ 15)
    (hhigh : ∀ h', h < h' → h' ≤ 14 → ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
      (nodeVal h' (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node h' (σ * 3 ^ J))
    (hcheck : nodeCheck h a n = true) {k : ℕ} (hk : k < n) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    (nodeVal h (a + k) : ℚ) = 10 ^ 8 * c3H17Node h (σ * 3 ^ (a + k)) := by
  have hc := allZipR_getD hcheck (k := k) (by rw [length_nodeSeg]; exact hk)
    (by
      unfold nodeAcc
      generalize List.range' 2 (16 - h) = L
      induction L with
      | nil => rw [List.foldr_nil, length_rangeMap]; exact hk
      | cons d L ih =>
        rw [List.foldr_cons, zipR_eq, List.length_zipWith, length_nodeTerm h1 hs]; omega)
  rw [nodeSeg_getD (by omega) hk, Nat.mod_eq_of_lt (by omega), getD_nodeAcc h1 hs hk] at hc
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.mul_eq, Nat.sub_eq, Nat.add_eq] at hc
  have hG : ∀ d, nodeHasG h d = true ↔ (d ≠ 4 ∧ d ≠ 5) ∧ h + d ≤ 14 := by
    intro d; simp [nodeHasG]
  rw [hc.2]
  symm
  refine c3H17Node_eq_ceil h1 h14 (σ * 3 ^ (a + k)) (fun d => nodeU h a n d k)
    (fun d => nodeG h a n d k) ?_ ?_ ?_ ?_ hc.1
  · intro d hd
    rw [List.mem_range'_1] at hd
    by_cases h2 : d = 2
    · subst h2
      simp only [nodeU]
      rw [c3H17CapUp_of_not_mem (by omega)]
      push_cast; ring
    · simp only [nodeU, ite_eq_right h2]
      rcases hs.2 (17 - h - d) (by omega) with h' | h'
      · rw [uSeg_spec (by omega) (by omega) (by omega) hs.1 (Or.inl h') hk hσ,
          div_two_pow_eq (v := 17 - h - d) (by omega)]
      · rw [uSeg_spec (by omega) (by omega) (by omega) hs.1 (Or.inr h') hk hσ,
          div_two_pow_eq (v := 17 - h - d) (by omega)]
  · intro d hd
    rw [List.mem_range'_1] at hd
    simp only [nodeG]
    by_cases hg : nodeHasG h d = true
    · rw [ite_eq_left hg, nodeSeg_getD (by omega) hk]
      obtain ⟨⟨h4, h5⟩, hd14⟩ := (hG d).1 hg
      have hcond : (d : ℤ) ∉ ({4, 5} : Finset ℤ) ∧ (h : ℤ) + d ≤ 15 := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; omega
      rw [ite_eq_left hcond, show a + 2 + k = a + k + 2 by omega,
        hhigh (h + d) (by omega) hd14 (a + k + 2) σ hσ]
      push_cast
      rw [pow_add]
      ring_nf
    · rw [ite_eq_right hg]
      split_ifs with hcond
      · have h15 : (h : ℤ) + d = 15 := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcond
          rw [hG d] at hg
          omega
        rw [h15, c3H17Node_of_le le_rfl]
        push_cast; ring
      · push_cast; ring
  · intro d hd
    rw [List.mem_range'_1] at hd
    simp only [nodeU]
    split_ifs with h2
    · exact le_rfl
    · rcases hs.2 (17 - h - d) (by omega) with h' | h'
      · exact uSeg_le (by omega) (by omega) (by omega) hs.1 (Or.inl h') hk
      · exact uSeg_le (by omega) (by omega) (by omega) hs.1 (Or.inr h') hk
  · intro d hd
    rw [List.mem_range'_1] at hd
    simp only [nodeG]
    split_ifs with hg
    · rw [nodeSeg_getD (by omega) hk]
      obtain ⟨-, hd14⟩ := (hG d).1 hg
      exact nodeVal_le (hhigh (h + d) (by omega) hd14 (a + 2 + k) 1 (Or.inl rfl))
    · exact le_rfl

/-- `3^{2^15} ≡ 1 (mod 2^17)`. -/
theorem three_pow_two_pow_fifteen : ((3 : ℤ) ^ 2 ^ 15 - 1) % 2 ^ 17 = 0 := by decide +kernel

/-- The rounded future costs at `± 3^J` depend only on `J mod 2^15`. -/
theorem c3H17Node_three_pow_mod (h : ℤ) (σ : ℤ) (J : ℕ) :
    c3H17Node h (σ * 3 ^ J) = c3H17Node h (σ * 3 ^ (J % 2 ^ 15)) := by
  have hd : (2 : ℤ) ^ 17 ∣ 3 ^ J - 3 ^ (J % 2 ^ 15) := by
    have h3 : (3 : ℤ) ^ J = 3 ^ (J % 2 ^ 15) * (3 ^ 2 ^ 15) ^ (J / 2 ^ 15) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    have hQ := Int.dvd_of_emod_eq_zero three_pow_two_pow_fifteen
    rw [h3]
    generalize (3 : ℤ) ^ 2 ^ 15 = Q at hQ ⊢
    rw [show (3 : ℤ) ^ (J % 2 ^ 15) * Q ^ (J / 2 ^ 15) - 3 ^ (J % 2 ^ 15) =
      3 ^ (J % 2 ^ 15) * (Q ^ (J / 2 ^ 15) - 1) by ring]
    exact dvd_mul_of_dvd_right (dvd_trans hQ (sub_one_dvd_pow_sub_one _ _)) _
  obtain ⟨q, hq⟩ := hd
  rw [show σ * 3 ^ J = σ * 3 ^ (J % 2 ^ 15) + (σ * q) * 2 ^ 17 by linear_combination σ * hq,
    c3H17Node_add_mul_two_pow]

/-- The checks of the `2^15 / n` blocks of `n` points of level `h` certify level `h`, given the
higher levels. -/
theorem nodeVal_spec_of_checks {h n : ℕ} (h1 : 1 ≤ h) (h14 : h ≤ 14) (hn : n ∣ 2 ^ 15)
    (hs : ∀ p < 2 ^ 15 / n, NodeSegOK (n * p) n)
    (hhigh : ∀ h', h < h' → h' ≤ 14 → ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
      (nodeVal h' (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node h' (σ * 3 ^ J))
    (hchecks : ∀ p < 2 ^ 15 / n, nodeCheck h (n * p) n = true) (J : ℕ) (σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) :
    (nodeVal h (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node h (σ * 3 ^ J) := by
  have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hn (by norm_num)
  set J' := J % 2 ^ 15 with hJ'
  have hJ'lt : J' < 2 ^ 15 := Nat.mod_lt _ (by norm_num)
  have hp : J' / n < 2 ^ 15 / n := Nat.div_lt_div_of_lt_of_dvd hn hJ'lt
  have hle : n * (J' / n) + n ≤ 2 ^ 15 := by
    have := Nat.div_mul_cancel hn
    have : (J' / n + 1) * n ≤ 2 ^ 15 / n * n := Nat.mul_le_mul_right _ hp
    nlinarith
  have := nodeVal_of_nodeCheck h1 h14 (hs _ hp) hle hhigh (hchecks _ hp)
    (Nat.mod_lt J' hn0) hσ
  rw [Nat.div_add_mod] at this
  rw [this]
  conv_rhs => rw [c3H17Node_three_pow_mod]

/-! ### The check of consecutive points in one pass -/

/-- `zipR Nat.add (mapR f l) acc`, in one pass. -/
noncomputable def zipAdd1R (f : ℕ → ℕ) (l : List ℕ) : List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun _ => [])
    (fun x _ ih acc => List.rec (motive := fun _ => List ℕ) []
      (fun a as _ => Nat.add (f x) a :: ih as) acc) l

/-- `zipAdd1R f l acc = zipR Nat.add (mapR f l) acc`. -/
theorem zipAdd1R_eq (f : ℕ → ℕ) :
    ∀ l acc, zipAdd1R f l acc = zipR Nat.add (mapR f l) acc
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: l, a :: acc => by
    change Nat.add (f x) a :: zipAdd1R f l acc = Nat.add (f x) a :: zipR Nat.add (mapR f l) acc
    rw [zipAdd1R_eq f l acc]

/-- `zipR Nat.add (zipR f lu lg) acc`, in one pass. -/
noncomputable def zipAdd2R (f : ℕ → ℕ → ℕ) (lu : List ℕ) : List ℕ → List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ → List ℕ) (fun _ _ => [])
    (fun u _ ih lg acc => List.rec (motive := fun _ => List ℕ) []
      (fun g gs _ => List.rec (motive := fun _ => List ℕ) []
        (fun a as _ => Nat.add (f u g) a :: ih gs as) acc) lg) lu

/-- `zipAdd2R f lu lg acc = zipR Nat.add (zipR f lu lg) acc`. -/
theorem zipAdd2R_eq (f : ℕ → ℕ → ℕ) :
    ∀ lu lg acc, zipAdd2R f lu lg acc = zipR Nat.add (zipR f lu lg) acc
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | u :: lu, g :: lg, a :: acc => by
    change Nat.add (f u g) a :: zipAdd2R f lu lg acc =
      Nat.add (f u g) a :: zipR Nat.add (zipR f lu lg) acc
    rw [zipAdd2R_eq f lu lg acc]

/-- One step `zipR Nat.add (nodeTerm h a n d) acc` of `nodeAcc`, in one pass, with the values
`10^8 Ū_d` read from `uSegF`. -/
noncomputable def nodeStepF (h a n d : ℕ) (acc : List ℕ) : List ℕ :=
  if d = 2 then
    cond (nodeHasG h 2)
      (zipAdd1R (fun g => Nat.mul (nodeW 2) (Nat.sub 10000000000000000 (Nat.mul 100000000 g)))
        (nodeSeg (h + 2) (a + 2) n) acc)
      (zipR Nat.add (rangeMap (fun _ => 0) n) acc)
  else
    cond (nodeHasG h d)
      (zipAdd2R (fun u g => Nat.mul (nodeW d) (Nat.sub 10000000000000000 (Nat.mul u g)))
        (uSegF d (17 - h - d) a n) (nodeSeg (h + d) (a + 2) n) acc)
      (zipAdd1R (fun u => Nat.mul (nodeW d) (Nat.sub 10000000000000000 (Nat.mul u 100000000)))
        (uSegF d (17 - h - d) a n) acc)

/-- `nodeStepF h a n d acc = zipR Nat.add (nodeTerm h a n d) acc`. -/
theorem nodeStepF_eq (h a n d : ℕ) (acc : List ℕ) :
    nodeStepF h a n d acc = zipR Nat.add (nodeTerm h a n d) acc := by
  unfold nodeStepF nodeTerm
  split_ifs <;> cases nodeHasG h _ <;>
    simp only [Bool.cond_true, Bool.cond_false, zipAdd1R_eq, zipAdd2R_eq, uSegF_eq]

/-- `nodeAcc`, with the steps `nodeStepF`. -/
noncomputable def nodeAccF (h a n : ℕ) : List ℕ :=
  (List.range' 2 (16 - h)).foldr (fun d acc => nodeStepF h a n d acc) (rangeMap (fun _ => 0) n)

/-- `nodeAccF h a n = nodeAcc h a n`. -/
theorem nodeAccF_eq (h a n : ℕ) : nodeAccF h a n = nodeAcc h a n := by
  unfold nodeAccF nodeAcc
  simp only [nodeStepF_eq]

/-- `nodeCheck`, with the sums `nodeAccF`. -/
noncomputable def nodeCheckF (h a n : ℕ) : Bool :=
  allZipR (fun nv acc => Nat.ble (Nat.mul 100000000 acc) nodeA &&
      Nat.beq nv
        (Nat.div (Nat.sub (Nat.add (Nat.sub nodeA (Nat.mul 100000000 acc)) nodeK) 1) nodeK))
    (nodeSeg h a n) (nodeAccF h a n)

/-- A passing one-pass check is a passing check. -/
theorem nodeCheck_of_nodeCheckF {h a n : ℕ} (hc : nodeCheckF h a n = true) :
    nodeCheck h a n = true := by
  rwa [nodeCheckF, nodeAccF_eq] at hc

end C3H17Values

end CollatzPosDens
