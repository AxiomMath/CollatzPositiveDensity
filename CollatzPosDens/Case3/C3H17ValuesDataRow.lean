/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataNode
public import CollatzPosDens.Case3.C3H17TablePeriod
public import CollatzPosDens.Case3.C3H17Range

/-!
# The rows of the height-seventeen cost table

For `2 ≤ c ≤ 16`, `1 ≤ o ≤ c` and `m = ± 3^J`, the table value `ct_{c,o}(m)` is
`min (V p_d, 10^8 p_n) / (10^8 p_d)`, where `p_n / p_d` is the packet value `1 - δ'_{c,o}`
(`1` for `c = 2`),
`V = min (10^8, u + a_{dir}, ⌈u g / 10^8⌉ + a_{jo})` (the second entry only for `c ≥ 3`, the
third only for `c ∉ {4, 5}`), `u = 10^8 Ū_c(m / 2^o)`, `g = 10^8 cf⁺_o(9 m)`, and `a_{dir}`,
`a_{jo}` are the two rounded Lipschitz corrections.

Along the orbit of `s ∈ {1, 3, 5, 7}` under multiplication by `9` the points are `3^{2k}`,
`3^{2k+1}`, `-3^{2k+15627}` and `-3^{2k+1198}` modulo `2^17`. The row values at the `2^15` points
`3^J`, `J < 2^15`, are computed once; the four orbit sequences are the values at the even and
odd indices and their rotations by `7813` and `599`. A scan of each sequence returns its sum `T`
and the extreme values of `Q_k = 2^{14} ∑_{j<k} W_j + (2^{14} - k) T`, `k ≤ 2^{14}`, which give
the orbit mean and the orbit range.

## Main definitions

* `CollatzPosDens.C3H17Values.rowW`: the value `min (V p_d, 10^8 p_n)`.
* `CollatzPosDens.C3H17Values.rowCheck`: the check of the four orbit sequences of a row.

## Main results

* `CollatzPosDens.C3H17Values.c3H17Table_eq_rowW`: the table value from `rowW`.
* `CollatzPosDens.C3H17Values.rowSpec_of_rowCheck`: a passing check gives the orbit means and
  ranges of the row.
-/

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

open Finset

/-! ### The table value at one point -/

/-- The value `V = min (10^8, u + a_{dir}, ⌈u g / 10^8⌉ + a_{jo})`, with the second entry only for
`c ≥ 3` and the third only for `c ∉ {4, 5}`. -/
def rowV (c adir ajo u g : ℕ) : ℕ :=
  natMin 100000000 (natMin (cond (Nat.ble 3 c) (Nat.add u adir) 100000000)
    (cond (c != 4 && c != 5)
      (Nat.add (Nat.div (Nat.sub (Nat.add (Nat.mul u g) 100000000) 1) 100000000) ajo) 100000000))

/-- The value `min (V p_d, 10^8 p_n)`, that is `10^8 p_d ct_{c,o}`. -/
def rowW (c pn pd adir ajo u g : ℕ) : ℕ :=
  natMin (Nat.mul (rowV c adir ajo u g) pd) (Nat.mul 100000000 pn)

/-- The table value `ct_{c,o}(m)` is `rowW c pn pd adir ajo u g / (10^8 p_d)`, where `u`, `g`
are `10^8 Ū_c(m / 2^o)`, `10^8 cf⁺_o(9 m)` and `p_n / p_d = 1 - δ'_{c,o}` (`p_n = p_d` for
`c = 2`). -/
theorem c3H17Table_eq_rowW {c o : ℕ} (hc2 : 2 ≤ c) (hc : c ≤ 16) (m : ℤ)
    {u g pn pd adir ajo : ℕ}
    (hu : (u : ℚ) = 10 ^ 8 * c3H17CapUp c ((m : ℚ) / 2 ^ (o : ℤ)))
    (hg : (g : ℚ) = 10 ^ 8 * c3H17Node o (9 * m)) (hpd : 0 < pd)
    (hp : 3 ≤ c → (pn : ℚ) / pd = 1 - c3NarrowDeficit c o) (hp2 : c < 3 → pn = pd)
    (hadir : ⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-(o : ℤ))))⌉ = adir)
    (hajo : ⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-(o : ℤ)) +
      9 * c3H17Lip o))⌉ = ajo) :
    c3H17Table c o m = (rowW c pn pd adir ajo u g : ℚ) / (10 ^ 8 * pd) := by
  have hU : c3H17CapUp c ((m : ℚ) / 2 ^ (o : ℤ)) = (u : ℚ) / 10 ^ 8 := by rw [hu]; ring
  have hG : c3H17Node o (9 * m) = (g : ℚ) / 10 ^ 8 := by rw [hg]; ring
  have hceil : (⌈(10 ^ 8 : ℚ) * ((u : ℚ) / 10 ^ 8 * ((g : ℚ) / 10 ^ 8))⌉ : ℚ) =
      (((u * g + 10 ^ 8 - 1) / 10 ^ 8 : ℕ) : ℚ) := by
    rw [show (10 ^ 8 : ℚ) * ((u : ℚ) / 10 ^ 8 * ((g : ℚ) / 10 ^ 8)) =
        ((u * g : ℕ) : ℚ) / ((10 ^ 8 : ℕ) : ℚ) by push_cast; field_simp; ring,
      Rat.ceil_natCast_div_natCast, ← ceilDiv_cast _ _ (by norm_num)]
    push_cast
    rfl
  have hpd' : (0 : ℚ) < pd := by exact_mod_cast hpd
  have h8 : (0 : ℚ) < 10 ^ 8 := by norm_num
  unfold c3H17Table
  rw [hU, hG, hceil, hadir, hajo]
  simp only [rowW, rowV, natMin_eq, Nat.mul_eq, Nat.add_eq, Nat.sub_eq, Int.cast_natCast]
  have hrhs : ∀ V : ℕ, ((min (V * pd) (100000000 * pn) : ℕ) : ℚ) / (10 ^ 8 * pd) =
      min ((V : ℚ) / 10 ^ 8) ((pn : ℚ) / pd) := by
    intro V
    push_cast
    rw [← min_div_div_right (by positivity)]
    congr 1
    · field_simp
    · field_simp; ring
  rw [hrhs]
  have hm : ∀ X Y : ℕ, ((min 100000000 (min X Y) : ℕ) : ℚ) / 10 ^ 8 =
      min 1 (min ((X : ℚ) / 10 ^ 8) ((Y : ℚ) / 10 ^ 8)) := by
    intro X Y
    push_cast
    rw [← min_div_div_right h8.le, ← min_div_div_right h8.le]
    norm_num
  rw [hm]
  have hY : (((u * g + 100000000 - 1).div 100000000 + ajo : ℕ) : ℚ) / 10 ^ 8 =
      (((u * g + 10 ^ 8 - 1) / 10 ^ 8 : ℕ) : ℚ) / 10 ^ 8 + (ajo : ℚ) / 10 ^ 8 := by
    rw [← add_div]
    push_cast
    rfl
  by_cases hc3 : 3 ≤ c
  · have hc3' : (3 : ℤ) ≤ c := by exact_mod_cast hc3
    have hb3 : Nat.ble 3 c = true := by simpa using hc3
    rw [ite_eq_left hc3', ← hp hc3, hb3, Bool.cond_true]
    have hX : ((u + adir : ℕ) : ℚ) / 10 ^ 8 = (u : ℚ) / 10 ^ 8 + (adir : ℚ) / 10 ^ 8 := by
      push_cast; ring
    rw [hX]
    by_cases h45 : c = 4 ∨ c = 5
    · have h45' : (c : ℤ) ∈ ({4, 5} : Finset ℤ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have hb : (c != 4 && c != 5) = false := by
        rcases h45 with rfl | rfl <;> rfl
      rw [ite_eq_right (not_not.2 h45'), hb, Bool.cond_false]
      norm_num
      ac_rfl
    · have h45' : (c : ℤ) ∉ ({4, 5} : Finset ℤ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have hb : (c != 4 && c != 5) = true := by
        simp only [Bool.and_eq_true, bne_iff_ne]; omega
      rw [ite_eq_left h45', hb, Bool.cond_true, hY]
      generalize (u : ℚ) / 10 ^ 8 + (adir : ℚ) / 10 ^ 8 = A
      generalize (((u * g + 10 ^ 8 - 1) / 10 ^ 8 : ℕ) : ℚ) / 10 ^ 8 + (ajo : ℚ) / 10 ^ 8 = B
      ac_rfl
  · have hc3' : ¬ (3 : ℤ) ≤ c := by exact_mod_cast hc3
    have hb3 : Nat.ble 3 c = false :=
      Bool.eq_false_iff.2 (fun h => hc3 (Nat.le_of_ble_eq_true h))
    have h45' : (c : ℤ) ∉ ({4, 5} : Finset ℤ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hb : (c != 4 && c != 5) = true := by
      simp only [Bool.and_eq_true, bne_iff_ne]; omega
    rw [ite_eq_right hc3', hb3, Bool.cond_false, ite_eq_left h45', hb, Bool.cond_true, hY,
      hp2 (by omega), div_self (by positivity)]
    have h1 : ((100000000 : ℕ) : ℚ) / 10 ^ 8 = 1 := by norm_num
    rw [h1]
    generalize (((u * g + 10 ^ 8 - 1) / 10 ^ 8 : ℕ) : ℚ) / 10 ^ 8 + (ajo : ℚ) / 10 ^ 8 = B
    ac_rfl

/-! ### Scanning an orbit sequence -/

/-- `Q = 2^{14} P + (2^{14} - k) T`. -/
def rowQ (T P k : ℕ) : ℕ := 16384 * P + (16384 - k) * T

/-- The next value `Q + 2^{14} x - T` of `Q` after the entry `x`. -/
def nextQ (T Q x : ℕ) : ℕ := Nat.sub (Nat.add Q (Nat.mul 16384 x)) T

/-- The scan of a sequence: from the partial sum `P`, the current value `Q` and the extreme values
`mx`, `mn`, it returns the final partial sum and the extreme values over the remaining entries.
The comparison with `0` forces the state at every step. -/
noncomputable def scanR (T : ℕ) (l : List ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (fun P _ mx mn => (P, mx, mn))
    (fun x _ ih P Q mx mn =>
      cond (Nat.beq (Nat.add P (Nat.add Q (Nat.add mx mn))) 0)
        (ih (Nat.add P x) (nextQ T Q x) (natMax mx (nextQ T Q x)) (natMin mn (nextQ T Q x)))
        (ih (Nat.add P x) (nextQ T Q x) (natMax mx (nextQ T Q x)) (natMin mn (nextQ T Q x)))) l

/-- One step of the scan, with the primitive arithmetic of its definition. -/
theorem scanR_cons' (T x : ℕ) (l : List ℕ) (P Q mx mn : ℕ) :
    scanR T (x :: l) P Q mx mn = scanR T l (Nat.add P x) (nextQ T Q x)
      (natMax mx (nextQ T Q x)) (natMin mn (nextQ T Q x)) := by
  change cond _ _ _ = _
  rw [Bool.cond_self]
  rfl

/-- One step of the scan: the entry `x` is added to `P`, `Q` is updated, and the extreme values
are compared with the new `Q`. -/
theorem scanR_cons (T x : ℕ) (l : List ℕ) (P Q mx mn : ℕ) :
    scanR T (x :: l) P Q mx mn = scanR T l (P + x) (nextQ T Q x)
      (max mx (nextQ T Q x)) (min mn (nextQ T Q x)) := by
  rw [scanR_cons', natMax_eq, natMin_eq]
  rfl

/-- The scan of the empty sequence returns its state. -/
theorem scanR_nil (T P Q mx mn : ℕ) : scanR T [] P Q mx mn = (P, mx, mn) := rfl

/-- For `k < 2^{14}`, the value of `Q` after the entry `x` is `rowQ T (P + x) (k + 1)`. -/
theorem nextQ_eq {T P k x : ℕ} (hk : k < 16384) :
    nextQ T (rowQ T P k) x = rowQ T (P + x) (k + 1) := by
  have h : rowQ T P k + 16384 * x = rowQ T (P + x) (k + 1) + T := by
    unfold rowQ
    rw [show 16384 - k = (16384 - (k + 1)) + 1 by omega]
    ring
  simp only [nextQ, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  rw [h, Nat.add_sub_cancel]

/-- The partial sum returned by the scan of `l` from `P` is `P + ∑ l`. -/
theorem scanR_fst (T : ℕ) : ∀ (l : List ℕ) (P Q mx mn : ℕ), (scanR T l P Q mx mn).1 = P + l.sum
  | [], _, _, _, _ => by simp [scanR_nil]
  | x :: l, P, Q, mx, mn => by
    rw [scanR_cons, scanR_fst T l, List.sum_cons, add_assoc]

/-- The maximum returned by the scan bounds `mx` and every later value, and is one of them. -/
theorem scanR_snd (T : ℕ) : ∀ (l : List ℕ) (P mx mn k : ℕ), k + l.length ≤ 16384 →
    mx ≤ (scanR T l P (rowQ T P k) mx mn).2.1 ∧
      (∀ j, 1 ≤ j → j ≤ l.length →
        rowQ T (P + (l.take j).sum) (k + j) ≤ (scanR T l P (rowQ T P k) mx mn).2.1) ∧
      ((scanR T l P (rowQ T P k) mx mn).2.1 = mx ∨ ∃ j, 1 ≤ j ∧ j ≤ l.length ∧
        (scanR T l P (rowQ T P k) mx mn).2.1 = rowQ T (P + (l.take j).sum) (k + j))
  | [], P, mx, mn, k, _ => ⟨le_rfl, fun j h1 h2 => absurd h2 (by simp; omega), Or.inl rfl⟩
  | x :: l, P, mx, mn, k, hk => by
    simp only [List.length_cons] at hk
    rw [scanR_cons, nextQ_eq (by omega)]
    obtain ⟨h1, h2, h3⟩ := scanR_snd T l (P + x) (max mx (rowQ T (P + x) (k + 1)))
      (min mn (rowQ T (P + x) (k + 1))) (k + 1) (by omega)
    refine ⟨(le_max_left _ _).trans h1, ?_, ?_⟩
    · intro j hj1 hj
      rcases j with _ | j
      · omega
      rcases j with _ | j
      · simpa using (le_max_right _ _).trans h1
      · have := h2 (j + 1) (by omega) (by simp at hj; omega)
        simpa [List.take_succ_cons, add_assoc, add_comm 1, add_left_comm] using this
    · rcases h3 with h3 | ⟨j, hj1, hj, h3⟩
      · rw [h3]
        rcases le_total mx (rowQ T (P + x) (k + 1)) with h | h
        · right; exact ⟨1, le_rfl, by simp, by simp [max_eq_right h]⟩
        · left; exact max_eq_left h
      · right
        refine ⟨j + 1, by omega, by simp; omega, ?_⟩
        rw [h3]
        simp [List.take_succ_cons, add_assoc, add_comm 1, add_left_comm]

/-- The minimum returned by the scan is bounded by `mn` and every later value, and is one of
them. -/
theorem scanR_thd (T : ℕ) : ∀ (l : List ℕ) (P mx mn k : ℕ), k + l.length ≤ 16384 →
    (scanR T l P (rowQ T P k) mx mn).2.2 ≤ mn ∧
      (∀ j, 1 ≤ j → j ≤ l.length →
        (scanR T l P (rowQ T P k) mx mn).2.2 ≤ rowQ T (P + (l.take j).sum) (k + j)) ∧
      ((scanR T l P (rowQ T P k) mx mn).2.2 = mn ∨ ∃ j, 1 ≤ j ∧ j ≤ l.length ∧
        (scanR T l P (rowQ T P k) mx mn).2.2 = rowQ T (P + (l.take j).sum) (k + j))
  | [], P, mx, mn, k, _ => ⟨le_rfl, fun j h1 h2 => absurd h2 (by simp; omega), Or.inl rfl⟩
  | x :: l, P, mx, mn, k, hk => by
    simp only [List.length_cons] at hk
    rw [scanR_cons, nextQ_eq (by omega)]
    obtain ⟨h1, h2, h3⟩ := scanR_thd T l (P + x) (max mx (rowQ T (P + x) (k + 1)))
      (min mn (rowQ T (P + x) (k + 1))) (k + 1) (by omega)
    refine ⟨h1.trans (min_le_left _ _), ?_, ?_⟩
    · intro j hj1 hj
      rcases j with _ | j
      · omega
      rcases j with _ | j
      · simpa using h1.trans (min_le_right _ _)
      · have := h2 (j + 1) (by omega) (by simp at hj; omega)
        simpa [List.take_succ_cons, add_assoc, add_comm 1, add_left_comm] using this
    · rcases h3 with h3 | ⟨j, hj1, hj, h3⟩
      · rw [h3]
        rcases le_total mn (rowQ T (P + x) (k + 1)) with h | h
        · left; exact min_eq_left h
        · right; exact ⟨1, le_rfl, by simp, by simp [min_eq_right h]⟩
      · right
        refine ⟨j + 1, by omega, by simp; omega, ?_⟩
        rw [h3]
        simp [List.take_succ_cons, add_assoc, add_comm 1, add_left_comm]

/-- The check that the scan of `l` returns the sum `T` and the extreme values `M`, `m`. -/
noncomputable def scanOK (T M m : ℕ) (l : List ℕ) : Bool :=
  Nat.beq (scanR T l 0 (16384 * T) (16384 * T) (16384 * T)).1 T &&
    Nat.beq (scanR T l 0 (16384 * T) (16384 * T) (16384 * T)).2.1 M &&
    Nat.beq (scanR T l 0 (16384 * T) (16384 * T) (16384 * T)).2.2 m

/-- For `k ≤ |l|`, the sum of the first `k` entries of `l` is `∑_{j<k} l_j`. -/
theorem sum_take_eq_sum_getD (l : List ℕ) : ∀ k, k ≤ l.length →
    (l.take k).sum = ∑ j ∈ range k, l.getD j 0
  | 0, _ => by simp
  | k + 1, hk => by
    rw [List.sum_take_succ _ _ (by omega), sum_take_eq_sum_getD l k (by omega), sum_range_succ,
      List.getD_eq_getElem _ _ (by omega)]

/-- From a passing scan of the orbit sequence `l`, the orbit mean and the orbit range of the
row: if `ct_{c,o}(9^k s) = l_k / D` for `k < 2^14`, then `μʰ = T / (2^14 D)` and
`rg = (M - m) / (2^14 D)`. -/
theorem meanRange_of_scanOK {c o s : ℤ} {l : List ℕ} (hl : l.length = 2 ^ 14) {D : ℚ}
    (hD : 0 < D) (hct : ∀ k < 2 ^ 14, c3H17Table c o (9 ^ k * s) = (l.getD k 0 : ℚ) / D)
    {T M m : ℕ} (h : scanOK T M m l = true) :
    c3H17Mean c o s = (T : ℚ) / (2 ^ 14 * D) ∧
      c3H17Range c o s = ((M : ℚ) - m) / (2 ^ 14 * D) := by
  simp only [scanOK, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨hT, hM⟩, hm⟩ := h
  rw [scanR_fst, zero_add] at hT
  have hsum : ∑ k ∈ range (2 ^ 14), c3H17Table c o (9 ^ k * s) = (T : ℚ) / D := by
    rw [sum_congr rfl fun k hk => hct k (mem_range.1 hk), ← sum_div, ← hT, ← hl, ← Nat.cast_sum,
      ← sum_take_eq_sum_getD l _ le_rfl, List.take_length]
  have hmean : c3H17Mean c o s = (T : ℚ) / (2 ^ 14 * D) := by
    rw [c3H17Mean, hsum]
    field_simp
  refine ⟨hmean, ?_⟩
  have hD' := hD.ne'
  have hcs : ∀ k ≤ 2 ^ 14, c3H17CentredSum c o s k =
      ((rowQ T (l.take k).sum k : ℚ) - 2 ^ 14 * T) / (2 ^ 14 * D) := by
    intro k hk
    have hk' : k ≤ 16384 := hk
    rw [c3H17CentredSum, sum_sub_distrib, sum_congr rfl fun j hj => hct j (by
      have := mem_range.1 hj; omega), ← sum_div, sum_const, card_range, hmean,
      sum_take_eq_sum_getD l k (by omega), rowQ]
    push_cast [Nat.cast_sub hk']
    field_simp
    ring_nf
    rw [mul_comm D, mul_assoc, mul_assoc, ← mul_assoc D, mul_inv_cancel₀ hD', one_mul]
  have hq0 : rowQ T 0 0 = 16384 * T := by simp [rowQ]
  obtain ⟨hM1, hM2, hM3⟩ := scanR_snd T l 0 (16384 * T) (16384 * T) 0 (by rw [hl]; norm_num)
  obtain ⟨hm1, hm2, hm3⟩ := scanR_thd T l 0 (16384 * T) (16384 * T) 0 (by rw [hl]; norm_num)
  rw [hq0] at hM1 hM2 hM3 hm1 hm2 hm3
  rw [hM] at hM1 hM2 hM3
  rw [hm] at hm1 hm2 hm3
  simp only [zero_add] at hM2 hM3 hm2 hm3
  have hle : ∀ k ≤ 2 ^ 14, rowQ T (l.take k).sum k ≤ M := by
    intro k hk
    rcases k with _ | k
    · simpa [hq0] using hM1
    · exact hM2 _ (by omega) (by omega)
  have hge : ∀ k ≤ 2 ^ 14, m ≤ rowQ T (l.take k).sum k := by
    intro k hk
    rcases k with _ | k
    · simpa [hq0] using hm1
    · exact hm2 _ (by omega) (by omega)
  have hMa : ∃ k ≤ 2 ^ 14, rowQ T (l.take k).sum k = M := by
    rcases hM3 with h | ⟨j, -, hj, h⟩
    · exact ⟨0, by norm_num, by simp [hq0, h]⟩
    · exact ⟨j, by omega, h.symm⟩
  have hma : ∃ k ≤ 2 ^ 14, rowQ T (l.take k).sum k = m := by
    rcases hm3 with h | ⟨j, -, hj, h⟩
    · exact ⟨0, by norm_num, by simp [hq0, h]⟩
    · exact ⟨j, by omega, h.symm⟩
  have hD2 : (0 : ℚ) < 2 ^ 14 * D := by positivity
  have hsup : (range (2 ^ 14 + 1)).sup' nonempty_range_add_one (c3H17CentredSum c o s) =
      ((M : ℚ) - 2 ^ 14 * T) / (2 ^ 14 * D) := by
    refine le_antisymm (sup'_le _ _ fun k hk => ?_) ?_
    · have hk' : k ≤ 2 ^ 14 := by have := mem_range.1 hk; omega
      rw [hcs k hk']
      have : (rowQ T (l.take k).sum k : ℚ) ≤ M := by exact_mod_cast hle k hk'
      gcongr
    · obtain ⟨k, hk, hkM⟩ := hMa
      rw [← hkM, ← hcs k hk]
      exact le_sup' _ (mem_range.2 (by omega))
  have hinf : (range (2 ^ 14 + 1)).inf' nonempty_range_add_one (c3H17CentredSum c o s) =
      ((m : ℚ) - 2 ^ 14 * T) / (2 ^ 14 * D) := by
    refine le_antisymm ?_ (le_inf' _ _ fun k hk => ?_)
    · obtain ⟨k, hk, hkm⟩ := hma
      rw [← hkm, ← hcs k hk]
      exact inf'_le _ (mem_range.2 (by omega))
    · have hk' : k ≤ 2 ^ 14 := by have := mem_range.1 hk; omega
      rw [hcs k hk']
      have : (m : ℚ) ≤ rowQ T (l.take k).sum k := by exact_mod_cast hge k hk'
      gcongr
  rw [c3H17Range, hsup, hinf]
  ring

/-! ### Splitting and rotating sequences -/

/-- The entries of even and of odd index, by a recursion that the kernel evaluates directly. -/
noncomputable def splitR (l : List ℕ) : List ℕ × List ℕ :=
  List.rec (motive := fun _ => List ℕ × List ℕ) ([], []) (fun x _ ih => (x :: ih.2, ih.1)) l

/-- The split of `x :: l` is `x` followed by the odd-index entries of `l`, and the even-index
entries of `l`. -/
theorem splitR_cons (x : ℕ) (l : List ℕ) : splitR (x :: l) = (x :: (splitR l).2, (splitR l).1) :=
  rfl

/-- The `k`-th entries of the two halves of the split of `l` are `l_{2k}` and `l_{2k+1}`. -/
theorem splitR_getD : ∀ (l : List ℕ) (k : ℕ),
    (splitR l).1.getD k 0 = l.getD (2 * k) 0 ∧ (splitR l).2.getD k 0 = l.getD (2 * k + 1) 0
  | [], k => by simp [splitR]
  | x :: l, k => by
    rw [splitR_cons]
    refine ⟨?_, ?_⟩
    · rcases k with _ | k
      · simp
      · rw [List.getD_cons_succ, (splitR_getD l k).2, show 2 * (k + 1) = (2 * k + 1) + 1 by ring,
          List.getD_cons_succ]
    · rw [(splitR_getD l k).1, List.getD_cons_succ]

/-- The two halves of the split of `l` have lengths `⌈|l| / 2⌉` and `⌊|l| / 2⌋`. -/
theorem splitR_length : ∀ (l : List ℕ),
    (splitR l).1.length = (l.length + 1) / 2 ∧ (splitR l).2.length = l.length / 2
  | [] => by simp [splitR]
  | x :: l => by
    rw [splitR_cons]
    obtain ⟨h1, h2⟩ := splitR_length l
    simp only [List.length_cons]
    rw [h1, h2]
    constructor <;> omega

/-! ### The rows -/

/-- The values `10^8 Ū_c(3^J / 2^o)`, `J < 2^15` (all `10^8` for `c = 2`). -/
noncomputable def rowU (c o : ℕ) : List ℕ :=
  if 3 ≤ c then uSeg c (17 - o) 0 32768 else rangeMap (fun _ => 100000000) 32768

/-- The values `10^8 cf⁺_o(3^{J+2})`, `J < 2^15` (all `10^8` for `o ≥ 15`). -/
noncomputable def rowG (o : ℕ) : List ℕ :=
  if o ≤ 14 then nodeSeg o 2 32768 else rangeMap (fun _ => 100000000) 32768

/-- The values `10^8 p_d ct_{c,o}(3^J)`, `J < 2^15`. -/
noncomputable def rowList (c o pn pd adir ajo : ℕ) : List ℕ :=
  zipR (rowW c pn pd adir ajo) (rowU c o) (rowG o)

/-- The scan of the entries of even and of odd index of a sequence in one pass, followed by the
comparison of the two results with the claimed sums and extreme values. The flag `b` records
whether the next entry has odd index. -/
noncomputable def scan2R (T0 M0 m0 T1 M1 m1 : ℕ) (l : List ℕ) :
    Bool → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => Bool → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool)
    (fun _ P0 _ mx0 mn0 P1 _ mx1 mn1 =>
      Nat.beq P0 T0 && Nat.beq mx0 M0 && Nat.beq mn0 m0 && Nat.beq P1 T1 && Nat.beq mx1 M1 &&
        Nat.beq mn1 m1)
    (fun x _ ih b P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 =>
      cond (Nat.beq (Nat.add (Nat.add (Nat.add P0 Q0) (Nat.add mx0 mn0))
          (Nat.add (Nat.add P1 Q1) (Nat.add mx1 mn1))) 0)
        (cond b
          (ih false P0 Q0 mx0 mn0 (Nat.add P1 x) (nextQ T1 Q1 x) (natMax mx1 (nextQ T1 Q1 x))
            (natMin mn1 (nextQ T1 Q1 x)))
          (ih true (Nat.add P0 x) (nextQ T0 Q0 x) (natMax mx0 (nextQ T0 Q0 x))
            (natMin mn0 (nextQ T0 Q0 x)) P1 Q1 mx1 mn1))
        (cond b
          (ih false P0 Q0 mx0 mn0 (Nat.add P1 x) (nextQ T1 Q1 x) (natMax mx1 (nextQ T1 Q1 x))
            (natMin mn1 (nextQ T1 Q1 x)))
          (ih true (Nat.add P0 x) (nextQ T0 Q0 x) (natMax mx0 (nextQ T0 Q0 x))
            (natMin mn0 (nextQ T0 Q0 x)) P1 Q1 mx1 mn1))) l

/-- The final comparison of two scans with the claimed values. -/
def scanPairOK (T0 M0 m0 T1 M1 m1 : ℕ) (r0 r1 : ℕ × ℕ × ℕ) : Bool :=
  Nat.beq r0.1 T0 && Nat.beq r0.2.1 M0 && Nat.beq r0.2.2 m0 && Nat.beq r1.1 T1 &&
    Nat.beq r1.2.1 M1 && Nat.beq r1.2.2 m1

/-- The one-pass scan of `l` is the comparison of the scans of its entries of even and of odd
index; with the flag set, the roles of the two halves are exchanged. -/
theorem scan2R_eq (T0 M0 m0 T1 M1 m1 : ℕ) : ∀ (l : List ℕ) (P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 : ℕ),
    scan2R T0 M0 m0 T1 M1 m1 l false P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 =
      scanPairOK T0 M0 m0 T1 M1 m1 (scanR T0 (splitR l).1 P0 Q0 mx0 mn0)
        (scanR T1 (splitR l).2 P1 Q1 mx1 mn1) ∧
    scan2R T0 M0 m0 T1 M1 m1 l true P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 =
      scanPairOK T0 M0 m0 T1 M1 m1 (scanR T0 (splitR l).2 P0 Q0 mx0 mn0)
        (scanR T1 (splitR l).1 P1 Q1 mx1 mn1)
  | [], _, _, _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | x :: l, P0, Q0, mx0, mn0, P1, Q1, mx1, mn1 => by
    refine ⟨?_, ?_⟩
    · change cond _ _ _ = _
      rw [Bool.cond_self, Bool.cond_false, splitR_cons, scanR_cons']
      exact (scan2R_eq T0 M0 m0 T1 M1 m1 l _ _ _ _ _ _ _ _).2
    · change cond _ _ _ = _
      rw [Bool.cond_self, Bool.cond_true, splitR_cons, scanR_cons']
      exact (scan2R_eq T0 M0 m0 T1 M1 m1 l _ _ _ _ _ _ _ _).1

/-- The check of the orbit sequences of `s = 1` and `s = 3` of the row `(c, o)`, with the
claimed sums and extreme values. -/
noncomputable def rowCheck (c o pn pd adir ajo T1 M1 m1 T3 M3 m3 : ℕ) : Bool :=
  scan2R T1 M1 m1 T3 M3 m3 (rowList c o pn pd adir ajo) false 0 (16384 * T1) (16384 * T1)
    (16384 * T1) 0 (16384 * T3) (16384 * T3) (16384 * T3)

/-- A passing row check gives passing scans of the entries of even and of odd index of the row. -/
theorem scanOK_of_rowCheck {c o pn pd adir ajo T1 M1 m1 T3 M3 m3 : ℕ}
    (h : rowCheck c o pn pd adir ajo T1 M1 m1 T3 M3 m3 = true) :
    scanOK T1 M1 m1 (splitR (rowList c o pn pd adir ajo)).1 = true ∧
      scanOK T3 M3 m3 (splitR (rowList c o pn pd adir ajo)).2 = true := by
  rw [rowCheck, (scan2R_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1] at h
  simp only [scanPairOK, Bool.and_eq_true] at h
  simp only [scanOK, Bool.and_eq_true]
  tauto

/-- The period `cosPer v` divides `2^15`. -/
theorem cosPer_dvd_two_pow_fifteen (v : ℕ) : cosPer v ∣ 32768 := by
  unfold cosPer
  split_ifs
  · exact (show (32768 : ℕ) = 2 ^ 15 by norm_num) ▸ pow_dvd_pow 2 (by omega)
  · norm_num

/-- The sequence `rowU c o` has `2^15` entries. -/
theorem length_rowU (c o : ℕ) : (rowU c o).length = 32768 := by
  unfold rowU
  split_ifs
  · exact length_uSeg (by norm_num) (Or.inr (cosPer_dvd_two_pow_fifteen _))
  · exact length_rangeMap _ _

/-- The sequence `rowG o` has `2^15` entries. -/
theorem length_rowG (o : ℕ) : (rowG o).length = 32768 := by
  unfold rowG
  split_ifs
  · exact length_nodeSeg _ _ _
  · exact length_rangeMap _ _

/-- The row `rowList c o pn pd adir ajo` has `2^15` entries. -/
theorem length_rowList (c o pn pd adir ajo : ℕ) :
    (rowList c o pn pd adir ajo).length = 32768 := by
  rw [rowList, zipR_eq, List.length_zipWith, length_rowU c o, length_rowG, min_self]

/-- The entry of `rowU c o` at `J mod 2^15` is `10^8 Ū_c(± 3^J / 2^o)`. -/
theorem rowU_getD {c o : ℕ} (hc2 : 2 ≤ c) (hc : c ≤ 16) (ho1 : 1 ≤ o) (hoc : o ≤ c) (J : ℕ)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ((rowU c o).getD (J % 2 ^ 15) 0 : ℚ) =
      10 ^ 8 * c3H17CapUp c ((σ * 3 ^ J : ℤ) / 2 ^ (o : ℤ)) := by
  have hj : J % 2 ^ 15 < 32768 := Nat.mod_lt _ (by norm_num)
  have harg : ((σ * 3 ^ J : ℤ) : ℚ) / 2 ^ (o : ℤ) =
      ((σ * 2 ^ (17 - o) * 3 ^ J : ℤ) : ℚ) / 2 ^ 17 := by
    rw [zpow_natCast, show (2 : ℚ) ^ 17 = 2 ^ (17 - o) * 2 ^ o by rw [← pow_add]; congr 1; omega]
    push_cast
    field_simp
  unfold rowU
  split_ifs with hc3
  · rw [uSeg_spec hc3 hc (by omega) (by norm_num)
      (Or.inr ⟨dvd_zero _, cosPer_dvd_two_pow_fifteen _⟩) hj hσ, zero_add, harg,
      c3H17CapUp_mod_cosPer _ (by omega) σ J, c3H17CapUp_mod_cosPer _ (by omega) σ (J % 2 ^ 15),
      Nat.mod_mod_of_dvd _ (by simpa using cosPer_dvd_two_pow_fifteen (17 - o))]
  · rw [getD_rangeMap _ hj, c3H17CapUp_of_not_mem (by omega)]
    norm_num

/-- The entry of `rowG o` at `J mod 2^15` is `10^8 cf⁺_o(± 9 · 3^J)`, given the node values
`nodeVal o`. -/
theorem rowG_getD {o : ℕ}
    (hnode : o ≤ 14 → ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
      (nodeVal o (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node o (σ * 3 ^ J))
    (J : ℕ) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ((rowG o).getD (J % 2 ^ 15) 0 : ℚ) = 10 ^ 8 * c3H17Node o (9 * (σ * 3 ^ J)) := by
  have hj : J % 2 ^ 15 < 32768 := Nat.mod_lt _ (by norm_num)
  unfold rowG
  split_ifs with ho
  · rw [nodeSeg_getD (by norm_num) hj, show (2 + J % 2 ^ 15) % 2 ^ 15 = (J + 2) % 2 ^ 15 by omega,
      hnode ho (J + 2) σ hσ, pow_add]
    ring_nf
  · rw [getD_rangeMap _ hj, c3H17Node_of_le (by omega)]
    norm_num

/-- The row values at `± 3^J`. -/
theorem c3H17Table_eq_rowList {c o : ℕ} (hc2 : 2 ≤ c) (hc : c ≤ 16) (ho1 : 1 ≤ o) (hoc : o ≤ c)
    {pn pd adir ajo : ℕ} (hpd : 0 < pd)
    (hp : 3 ≤ c → (pn : ℚ) / pd = 1 - c3NarrowDeficit c o) (hp2 : c < 3 → pn = pd)
    (hadir : ⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-(o : ℤ))))⌉ = adir)
    (hajo : ⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-(o : ℤ)) +
      9 * c3H17Lip o))⌉ = ajo)
    (hnode : o ≤ 14 → ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
      (nodeVal o (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node o (σ * 3 ^ J))
    (J : ℕ) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    c3H17Table c o (σ * 3 ^ J) =
      ((rowList c o pn pd adir ajo).getD (J % 2 ^ 15) 0 : ℚ) / (10 ^ 8 * pd) := by
  have hj : J % 2 ^ 15 < 32768 := Nat.mod_lt _ (by norm_num)
  rw [rowList, getD_zipR (by rw [length_rowU c o]; exact hj) (by rw [length_rowG]; exact hj)]
  exact c3H17Table_eq_rowW hc2 hc _ (rowU_getD hc2 hc ho1 hoc J hσ) (rowG_getD hnode J hσ) hpd hp
    hp2 hadir hajo

/-! ### Rotations of a periodic orbit sequence -/

/-- The sum over a period of an `N`-periodic function is invariant under a shift. -/
theorem sum_range_add_of_periodic {f : ℕ → ℚ} {N : ℕ} (hf : ∀ k, f (k + N) = f k) (r : ℕ) :
    ∑ k ∈ range N, f (k + r) = ∑ k ∈ range N, f k := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← ih]
    have h1 := sum_range_succ' (fun k => f (k + r)) N
    have h2 := sum_range_succ (fun k => f (k + r)) N
    have h3 : f (N + r) = f (0 + r) := by rw [add_comm N r, hf, zero_add]
    have h4 : ∑ k ∈ range N, f (k + (r + 1)) = ∑ k ∈ range N, f (k + 1 + r) :=
      sum_congr rfl fun k _ => by rw [add_right_comm, add_assoc]
    rw [h4]
    linarith

/-- The range of the centred partial sums of a periodic sequence is invariant under rotation. -/
theorem range_rotate_of_periodic {x : ℕ → ℚ} {N : ℕ} (hN : 0 < N) (hxp : ∀ k, x (k + N) = x k)
    (μ : ℚ) (hμ : ∑ k ∈ range N, (x k - μ) = 0) (r : ℕ) :
    (range (N + 1)).sup' nonempty_range_add_one
        (fun k => ∑ j ∈ range k, (x (j + r) - μ)) -
      (range (N + 1)).inf' nonempty_range_add_one (fun k => ∑ j ∈ range k, (x (j + r) - μ)) =
    (range (N + 1)).sup' nonempty_range_add_one (fun k => ∑ j ∈ range k, (x j - μ)) -
      (range (N + 1)).inf' nonempty_range_add_one (fun k => ∑ j ∈ range k, (x j - μ)) := by
  set P : ℕ → ℚ := fun n => ∑ j ∈ range n, (x j - μ) with hP
  have hPadd : ∀ n, P (n + N) = P n := by
    intro n
    simp only [hP]
    rw [sum_range_add, sum_congr rfl fun j _ => show x (n + j) - μ = x (j + n) - μ by
      rw [add_comm], sum_range_add_of_periodic (f := fun j => x j - μ) (fun k => by
        simp only [hxp]) n, hμ, add_zero]
  have hPmod : ∀ n, P n = P (n % N) := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n N]
    generalize n / N = q
    induction q with
    | zero => simp
    | succ q ih => rw [mul_add, mul_one, ← add_assoc, hPadd, ih]
  have hcs : ∀ k, ∑ j ∈ range k, (x (j + r) - μ) = P (k + r) - P r := by
    intro k
    simp only [hP]
    rw [show k + r = r + k by ring, sum_range_add, add_sub_cancel_left]
    exact sum_congr rfl fun j _ => by rw [add_comm j r]
  have hback : ∀ j ≤ N, ∃ k ≤ N, P j = P (k + r) := by
    intro j _
    refine ⟨(j + N - r % N) % N, (Nat.mod_lt _ hN).le, ?_⟩
    rw [hPmod j, hPmod ((j + N - r % N) % N + r), Nat.mod_add_mod]
    have hr := Nat.mod_add_div r N
    have hrl := Nat.mod_lt r hN
    have : j + N - r % N + r = j + N * (r / N + 1) := by
      rw [mul_add, mul_one]
      generalize N * (r / N) = A at hr ⊢
      generalize r % N = B at hr hrl ⊢
      omega
    rw [this, Nat.add_mul_mod_self_left]
  have hfwd : ∀ k, P (k + r) = P ((k + r) % N) := fun k => hPmod _
  have hmem : ∀ k, (k + r) % N ∈ range (N + 1) := fun k =>
    mem_range.2 (by have := Nat.mod_lt (k + r) hN; omega)
  have hsup : (range (N + 1)).sup' nonempty_range_add_one
      (fun k => ∑ j ∈ range k, (x (j + r) - μ)) =
      (range (N + 1)).sup' nonempty_range_add_one P - P r := by
    simp only [hcs]
    refine le_antisymm (sup'_le _ _ fun k _ => ?_) ?_
    · rw [hfwd k]
      exact sub_le_sub_right (le_sup' P (hmem k)) _
    · rw [sub_le_iff_le_add]
      refine sup'_le _ _ fun j hj => ?_
      obtain ⟨k, hk, hjk⟩ := hback j (by have := mem_range.1 hj; omega)
      rw [hjk, ← sub_le_iff_le_add]
      exact le_sup' (fun k => P (k + r) - P r) (mem_range.2 (by omega))
  have hinf : (range (N + 1)).inf' nonempty_range_add_one
      (fun k => ∑ j ∈ range k, (x (j + r) - μ)) =
      (range (N + 1)).inf' nonempty_range_add_one P - P r := by
    simp only [hcs]
    refine le_antisymm ?_ (le_inf' _ _ fun k _ => ?_)
    · rw [le_sub_iff_add_le]
      refine le_inf' _ _ fun j hj => ?_
      obtain ⟨k, hk, hjk⟩ := hback j (by have := mem_range.1 hj; omega)
      rw [hjk, ← le_sub_iff_add_le]
      exact inf'_le (fun k => P (k + r) - P r) (mem_range.2 (by omega))
    · rw [hfwd k]
      exact sub_le_sub_right (inf'_le P (hmem k)) _
  rw [hsup, hinf]
  ring

/-- The orbit mean and range are invariant when the orbit sequence is rotated. -/
theorem meanRange_rotate {c o s s' : ℤ} (r : ℕ)
    (hper : ∀ k, c3H17Table c o (9 ^ (k + 2 ^ 14) * s) = c3H17Table c o (9 ^ k * s))
    (hrot : ∀ k, c3H17Table c o (9 ^ k * s') = c3H17Table c o (9 ^ (k + r) * s)) :
    c3H17Mean c o s' = c3H17Mean c o s ∧ c3H17Range c o s' = c3H17Range c o s := by
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℚ, ∀ k, c3H17Table c o (9 ^ k * s) = x k := ⟨_, fun _ => rfl⟩
  have hxp : ∀ k, x (k + 2 ^ 14) = x k := fun k => by rw [← hx, ← hx, hper]
  have hx' : ∀ k, c3H17Table c o (9 ^ k * s') = x (k + r) := fun k => by rw [hrot, hx]
  have hmean : c3H17Mean c o s' = c3H17Mean c o s := by
    unfold c3H17Mean
    simp only [hx, hx']
    rw [sum_range_add_of_periodic hxp r]
  refine ⟨hmean, ?_⟩
  have h0 := c3H17CentredSum_two_pow_fourteen c o s
  unfold c3H17CentredSum at h0
  simp only [hx] at h0
  have key := range_rotate_of_periodic (by norm_num) hxp (c3H17Mean c o s) h0 r
  unfold c3H17Range c3H17CentredSum
  rw [hmean]
  simp only [hx, hx']
  exact key

/-- `3^{1198} ≡ -7 (mod 2^17)`. -/
theorem seven_add_three_pow : ((7 : ℤ) + 3 ^ 1198) % 2 ^ 17 = 0 := by decide +kernel

/-- `3^{15627} ≡ -5 (mod 2^17)`. -/
theorem five_add_three_pow : ((5 : ℤ) + 3 ^ 15627) % 2 ^ 17 = 0 := by decide +kernel

/-- If `s ≡ -3^e (mod 2^17)`, then `9^k s ≡ -3^{2k+e} (mod 2^17)`. -/
theorem nine_pow_mul_eq_neg {s : ℤ} {e : ℕ} (h : (s + 3 ^ e) % 2 ^ 17 = 0) (k : ℕ) :
    ∃ q : ℤ, (9 : ℤ) ^ k * s = (-1) * 3 ^ (2 * k + e) + q * 2 ^ 17 := by
  obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero h
  refine ⟨9 ^ k * q, ?_⟩
  rw [pow_add, pow_mul]
  norm_num
  linear_combination (9 : ℤ) ^ k * hq

/-- `9^{2^{14}} ≡ 1 (mod 2^17)`. -/
theorem nine_pow_two_pow_fourteen : ((9 : ℤ) ^ 2 ^ 14 - 1) % 2 ^ 17 = 0 := by decide +kernel

/-- A passing row check gives the orbit means and ranges of the row for `s = 1, 3, 5, 7`. -/
theorem rowSpec_of_rowCheck {c o : ℕ} (hc2 : 2 ≤ c) (hc : c ≤ 16) (ho1 : 1 ≤ o) (hoc : o ≤ c)
    {pn pd adir ajo : ℕ} (hpd : 0 < pd)
    (hp : 3 ≤ c → (pn : ℚ) / pd = 1 - c3NarrowDeficit c o) (hp2 : c < 3 → pn = pd)
    (hadir : ⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-(o : ℤ))))⌉ = adir)
    (hajo : ⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-(o : ℤ)) +
      9 * c3H17Lip o))⌉ = ajo)
    (hnode : o ≤ 14 → ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
      (nodeVal o (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node o (σ * 3 ^ J))
    {T1 M1 m1 T3 M3 m3 : ℕ} (h : rowCheck c o pn pd adir ajo T1 M1 m1 T3 M3 m3 = true) :
    (c3H17Mean c o 1 = (T1 : ℚ) / (2 ^ 14 * (10 ^ 8 * pd)) ∧
      c3H17Range c o 1 = ((M1 : ℚ) - m1) / (2 ^ 14 * (10 ^ 8 * pd))) ∧
    (c3H17Mean c o 3 = (T3 : ℚ) / (2 ^ 14 * (10 ^ 8 * pd)) ∧
      c3H17Range c o 3 = ((M3 : ℚ) - m3) / (2 ^ 14 * (10 ^ 8 * pd))) ∧
    (c3H17Mean c o 5 = (T3 : ℚ) / (2 ^ 14 * (10 ^ 8 * pd)) ∧
      c3H17Range c o 5 = ((M3 : ℚ) - m3) / (2 ^ 14 * (10 ^ 8 * pd))) ∧
    (c3H17Mean c o 7 = (T1 : ℚ) / (2 ^ 14 * (10 ^ 8 * pd)) ∧
      c3H17Range c o 7 = ((M1 : ℚ) - m1) / (2 ^ 14 * (10 ^ 8 * pd))) := by
  obtain ⟨h1, h3⟩ := scanOK_of_rowCheck h
  set W := rowList c o pn pd adir ajo with hW
  have hWl : W.length = 32768 := length_rowList c o pn pd adir ajo
  have hEl : (splitR W).1.length = 2 ^ 14 := by rw [(splitR_length W).1, hWl]; norm_num
  have hOl : (splitR W).2.length = 2 ^ 14 := by rw [(splitR_length W).2, hWl]; norm_num
  have hD : (0 : ℚ) < 10 ^ 8 * pd := by positivity
  have hrow := fun (J : ℕ) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) =>
    c3H17Table_eq_rowList (pn := pn) (pd := pd) (adir := adir) (ajo := ajo) hc2 hc ho1 hoc hpd hp
      hp2 hadir hajo hnode J hσ
  have hs1 : ∀ k : ℕ, (9 : ℤ) ^ k * 1 = 1 * 3 ^ (2 * k) := fun k => by rw [pow_mul]; norm_num
  have hs3 : ∀ k : ℕ, (9 : ℤ) ^ k * 3 = 1 * 3 ^ (2 * k + 1) := fun k => by
    rw [pow_succ, pow_mul]; norm_num
  have R1 := meanRange_of_scanOK hEl hD (fun k hk => by
    rw [hs1, hrow (2 * k) (Or.inl rfl), (splitR_getD W k).1, Nat.mod_eq_of_lt (by omega)]) h1
  have R3 := meanRange_of_scanOK hOl hD (fun k hk => by
    rw [hs3, hrow (2 * k + 1) (Or.inl rfl), (splitR_getD W k).2, Nat.mod_eq_of_lt (by omega)]) h3
  have hper : ∀ (s : ℤ) (k : ℕ),
      c3H17Table c o (9 ^ (k + 2 ^ 14) * s) = c3H17Table c o (9 ^ k * s) := by
    intro s k
    obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero nine_pow_two_pow_fourteen
    have hsplit : (9 : ℤ) ^ (k + 2 ^ 14) * s = 9 ^ k * s + (9 ^ k * s * q) * 2 ^ 17 := by
      rw [pow_add]
      generalize (9 : ℤ) ^ 2 ^ 14 = Q at hq ⊢
      linear_combination (9 : ℤ) ^ k * s * hq
    rw [hsplit, c3H17Table_add_mul_two_pow _ (by omega)]
  have R5 := meanRange_rotate (s := 3) (s' := 5) 7813 (hper 3) (fun k => by
    obtain ⟨q, hq⟩ := nine_pow_mul_eq_neg five_add_three_pow k
    rw [hq, c3H17Table_add_mul_two_pow _ (by omega), hrow (2 * k + 15627) (Or.inr rfl), hs3,
      hrow _ (Or.inl rfl), show (2 * k + 15627) % 2 ^ 15 = (2 * (k + 7813) + 1) % 2 ^ 15 by omega])
  have R7 := meanRange_rotate (s := 1) (s' := 7) 599 (hper 1) (fun k => by
    obtain ⟨q, hq⟩ := nine_pow_mul_eq_neg seven_add_three_pow k
    rw [hq, c3H17Table_add_mul_two_pow _ (by omega), hrow (2 * k + 1198) (Or.inr rfl), hs1,
      hrow _ (Or.inl rfl), show (2 * k + 1198) % 2 ^ 15 = 2 * (k + 599) % 2 ^ 15 by omega])
  refine ⟨R1, R3, ?_, ?_⟩
  · rw [R5.1, R5.2]; exact R3
  · rw [R7.1, R7.2]; exact R1

/-! ### The row check in one pass -/

/-- `x`, once the natural number `n` has been evaluated: the kernel reduces `n` before `x`. The
body is the bare recursor application `Bool.rec x x (Nat.beq n 0)`. -/
def forceR {α : Sort*} (n : ℕ) (x : α) : α := Bool.rec (motive := fun _ => α) x x (Nat.beq n 0)

/-- `forceR n x` is `x`. -/
theorem forceR_eq {α : Sort*} (n : ℕ) (x : α) : forceR n x = x := by
  unfold forceR
  cases Nat.beq n 0 <;> rfl

/-- `cond b x y`, as a definition whose body is the bare recursor application `Bool.rec y x b`:
the kernel unfolds it in one step (and `cond`, a definition by pattern matching, in several),
and a loop driven by it is reduced at a bounded depth. -/
def condD {α : Sort*} (b : Bool) (x y : α) : α := Bool.rec (motive := fun _ => α) y x b

/-- `condD b x y` is `cond b x y`. -/
theorem condD_eq {α : Sort*} (b : Bool) (x y : α) : condD b x y = cond b x y := by
  cases b <;> rfl

/-- One step of the one-pass scan: the entry `x` updates the state of the odd-index scan if the
flag is set and of the even-index scan otherwise, and the flag is flipped. -/
theorem scan2R_cons (T0 M0 m0 T1 M1 m1 x : ℕ) (l : List ℕ) (b : Bool)
    (P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 : ℕ) :
    scan2R T0 M0 m0 T1 M1 m1 (x :: l) b P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 =
      cond b
        (scan2R T0 M0 m0 T1 M1 m1 l false P0 Q0 mx0 mn0 (Nat.add P1 x) (nextQ T1 Q1 x)
          (natMax mx1 (nextQ T1 Q1 x)) (natMin mn1 (nextQ T1 Q1 x)))
        (scan2R T0 M0 m0 T1 M1 m1 l true (Nat.add P0 x) (nextQ T0 Q0 x)
          (natMax mx0 (nextQ T0 Q0 x)) (natMin mn0 (nextQ T0 Q0 x)) P1 Q1 mx1 mn1) := by
  change cond _ (cond b _ _) (cond b _ _) = _
  cases Nat.beq _ 0 <;> rfl

/-- `scan2R` on the list `mapR f l`, in one pass. Each step updates the state of the orbit of its
parity and evaluates the four updated values; `nextQ`, `natMax` and `natMin` are written out in
primitive arithmetic. -/
noncomputable def scanMapR (f : ℕ → ℕ) (T0 M0 m0 T1 M1 m1 : ℕ) (l : List ℕ) :
    Bool → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => Bool → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool)
    (fun _ P0 _ mx0 mn0 P1 _ mx1 mn1 =>
      Nat.beq P0 T0 && Nat.beq mx0 M0 && Nat.beq mn0 m0 && Nat.beq P1 T1 && Nat.beq mx1 M1 &&
        Nat.beq mn1 m1)
    (fun y _ ih b P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 =>
      condD b
        (forceR (Nat.add (Nat.add (Nat.add P1 (f y))
              (Nat.sub (Nat.add Q1 (Nat.mul 16384 (f y))) T1))
            (Nat.add (Nat.add mx1 (Nat.sub (Nat.sub (Nat.add Q1 (Nat.mul 16384 (f y))) T1) mx1))
              (Nat.sub mn1 (Nat.sub mn1 (Nat.sub (Nat.add Q1 (Nat.mul 16384 (f y))) T1)))))
          (ih false P0 Q0 mx0 mn0 (Nat.add P1 (f y)) (Nat.sub (Nat.add Q1 (Nat.mul 16384 (f y))) T1)
            (Nat.add mx1 (Nat.sub (Nat.sub (Nat.add Q1 (Nat.mul 16384 (f y))) T1) mx1))
            (Nat.sub mn1 (Nat.sub mn1 (Nat.sub (Nat.add Q1 (Nat.mul 16384 (f y))) T1)))))
        (forceR (Nat.add (Nat.add (Nat.add P0 (f y))
              (Nat.sub (Nat.add Q0 (Nat.mul 16384 (f y))) T0))
            (Nat.add (Nat.add mx0 (Nat.sub (Nat.sub (Nat.add Q0 (Nat.mul 16384 (f y))) T0) mx0))
              (Nat.sub mn0 (Nat.sub mn0 (Nat.sub (Nat.add Q0 (Nat.mul 16384 (f y))) T0)))))
          (ih true (Nat.add P0 (f y)) (Nat.sub (Nat.add Q0 (Nat.mul 16384 (f y))) T0)
            (Nat.add mx0 (Nat.sub (Nat.sub (Nat.add Q0 (Nat.mul 16384 (f y))) T0) mx0))
            (Nat.sub mn0 (Nat.sub mn0 (Nat.sub (Nat.add Q0 (Nat.mul 16384 (f y))) T0)))
            P1 Q1 mx1 mn1))) l

/-- One step of `scanMapR`, as the step of `scan2R` on the entry `f y`. -/
theorem scanMapR_cons (f : ℕ → ℕ) (T0 M0 m0 T1 M1 m1 y : ℕ) (l : List ℕ) (b : Bool)
    (P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 : ℕ) :
    scanMapR f T0 M0 m0 T1 M1 m1 (y :: l) b P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 =
      cond b
        (scanMapR f T0 M0 m0 T1 M1 m1 l false P0 Q0 mx0 mn0 (Nat.add P1 (f y))
          (nextQ T1 Q1 (f y)) (natMax mx1 (nextQ T1 Q1 (f y))) (natMin mn1 (nextQ T1 Q1 (f y))))
        (scanMapR f T0 M0 m0 T1 M1 m1 l true (Nat.add P0 (f y)) (nextQ T0 Q0 (f y))
          (natMax mx0 (nextQ T0 Q0 (f y))) (natMin mn0 (nextQ T0 Q0 (f y))) P1 Q1 mx1 mn1) := by
  change condD b (forceR _ _) (forceR _ _) = _
  rw [condD_eq, forceR_eq, forceR_eq]
  rfl

/-- `scanMapR f` on `l` is `scan2R` on `mapR f l`. -/
theorem scanMapR_eq (f : ℕ → ℕ) (T0 M0 m0 T1 M1 m1 : ℕ) :
    ∀ (l : List ℕ) (b : Bool) (P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 : ℕ),
      scanMapR f T0 M0 m0 T1 M1 m1 l b P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 =
        scan2R T0 M0 m0 T1 M1 m1 (mapR f l) b P0 Q0 mx0 mn0 P1 Q1 mx1 mn1
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | y :: l, b, P0, Q0, mx0, mn0, P1, Q1, mx1, mn1 => by
    rw [scanMapR_cons, show mapR f (y :: l) = f y :: mapR f l from rfl, scan2R_cons,
      scanMapR_eq f T0 M0 m0 T1 M1 m1 l, scanMapR_eq f T0 M0 m0 T1 M1 m1 l]

/-- `scan2R` on the list `zipR f lu lg`, in one pass, as `scanMapR`. -/
noncomputable def scanZipR (f : ℕ → ℕ → ℕ) (T0 M0 m0 T1 M1 m1 : ℕ) (lu : List ℕ) :
    List ℕ → Bool → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool)
    (fun _ _ P0 _ mx0 mn0 P1 _ mx1 mn1 =>
      Nat.beq P0 T0 && Nat.beq mx0 M0 && Nat.beq mn0 m0 && Nat.beq P1 T1 && Nat.beq mx1 M1 &&
        Nat.beq mn1 m1)
    (fun u _ ih lg => List.rec (motive := fun _ => Bool → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool)
      (fun _ P0 _ mx0 mn0 P1 _ mx1 mn1 =>
        Nat.beq P0 T0 && Nat.beq mx0 M0 && Nat.beq mn0 m0 && Nat.beq P1 T1 && Nat.beq mx1 M1 &&
          Nat.beq mn1 m1)
      (fun g gs _ b P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 =>
        condD b
          (forceR (Nat.add (Nat.add (Nat.add P1 (f u g))
                (Nat.sub (Nat.add Q1 (Nat.mul 16384 (f u g))) T1))
              (Nat.add (Nat.add mx1 (Nat.sub (Nat.sub (Nat.add Q1 (Nat.mul 16384 (f u g))) T1) mx1))
                (Nat.sub mn1 (Nat.sub mn1 (Nat.sub (Nat.add Q1 (Nat.mul 16384 (f u g))) T1)))))
            (ih gs false P0 Q0 mx0 mn0 (Nat.add P1 (f u g))
              (Nat.sub (Nat.add Q1 (Nat.mul 16384 (f u g))) T1)
              (Nat.add mx1 (Nat.sub (Nat.sub (Nat.add Q1 (Nat.mul 16384 (f u g))) T1) mx1))
              (Nat.sub mn1 (Nat.sub mn1 (Nat.sub (Nat.add Q1 (Nat.mul 16384 (f u g))) T1)))))
          (forceR (Nat.add (Nat.add (Nat.add P0 (f u g))
                (Nat.sub (Nat.add Q0 (Nat.mul 16384 (f u g))) T0))
              (Nat.add (Nat.add mx0 (Nat.sub (Nat.sub (Nat.add Q0 (Nat.mul 16384 (f u g))) T0) mx0))
                (Nat.sub mn0 (Nat.sub mn0 (Nat.sub (Nat.add Q0 (Nat.mul 16384 (f u g))) T0)))))
            (ih gs true (Nat.add P0 (f u g)) (Nat.sub (Nat.add Q0 (Nat.mul 16384 (f u g))) T0)
              (Nat.add mx0 (Nat.sub (Nat.sub (Nat.add Q0 (Nat.mul 16384 (f u g))) T0) mx0))
              (Nat.sub mn0 (Nat.sub mn0 (Nat.sub (Nat.add Q0 (Nat.mul 16384 (f u g))) T0)))
              P1 Q1 mx1 mn1))) lg) lu

/-- One step of `scanZipR`, as the step of `scan2R` on the entry `f u g`. -/
theorem scanZipR_cons (f : ℕ → ℕ → ℕ) (T0 M0 m0 T1 M1 m1 u g : ℕ) (lu lg : List ℕ) (b : Bool)
    (P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 : ℕ) :
    scanZipR f T0 M0 m0 T1 M1 m1 (u :: lu) (g :: lg) b P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 =
      cond b
        (scanZipR f T0 M0 m0 T1 M1 m1 lu lg false P0 Q0 mx0 mn0 (Nat.add P1 (f u g))
          (nextQ T1 Q1 (f u g)) (natMax mx1 (nextQ T1 Q1 (f u g)))
          (natMin mn1 (nextQ T1 Q1 (f u g))))
        (scanZipR f T0 M0 m0 T1 M1 m1 lu lg true (Nat.add P0 (f u g)) (nextQ T0 Q0 (f u g))
          (natMax mx0 (nextQ T0 Q0 (f u g))) (natMin mn0 (nextQ T0 Q0 (f u g))) P1 Q1 mx1 mn1) := by
  change condD b (forceR _ _) (forceR _ _) = _
  rw [condD_eq, forceR_eq, forceR_eq]
  rfl

/-- `scanZipR f` on `lu`, `lg` is `scan2R` on `zipR f lu lg`. -/
theorem scanZipR_eq (f : ℕ → ℕ → ℕ) (T0 M0 m0 T1 M1 m1 : ℕ) :
    ∀ (lu lg : List ℕ) (b : Bool) (P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 : ℕ),
      scanZipR f T0 M0 m0 T1 M1 m1 lu lg b P0 Q0 mx0 mn0 P1 Q1 mx1 mn1 =
        scan2R T0 M0 m0 T1 M1 m1 (zipR f lu lg) b P0 Q0 mx0 mn0 P1 Q1 mx1 mn1
  | [], _, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _, _, _, _, _, _ => rfl
  | u :: lu, g :: lg, b, P0, Q0, mx0, mn0, P1, Q1, mx1, mn1 => by
    rw [scanZipR_cons, show zipR f (u :: lu) (g :: lg) = f u g :: zipR f lu lg from rfl,
      scan2R_cons, scanZipR_eq f T0 M0 m0 T1 M1 m1 lu lg,
      scanZipR_eq f T0 M0 m0 T1 M1 m1 lu lg]

/-- `rowW c pn pd adir ajo u g` for `3 ≤ c`, `c ∉ {4, 5}`, without the case distinctions on
`c`. -/
def rowWG (pn pd adir ajo u g : ℕ) : ℕ :=
  let x1 := Nat.add u adir
  let x2 := Nat.add (Nat.div (Nat.sub (Nat.add (Nat.mul u g) 100000000) 1) 100000000) ajo
  let m1 := Nat.sub x1 (Nat.sub x1 x2)
  let w := Nat.mul (Nat.sub 100000000 (Nat.sub 100000000 m1)) pd
  Nat.sub w (Nat.sub w (Nat.mul 100000000 pn))

/-- For `3 ≤ c` and `c ∉ {4, 5}`, `rowWG` is `rowW c`. -/
theorem rowWG_eq {c : ℕ} (hc3 : 3 ≤ c) (hc4 : c ≠ 4) (hc5 : c ≠ 5) :
    rowWG = rowW c := by
  have h1 : Nat.ble 3 c = true := ble_true hc3
  have h2 : (c != 4 && c != 5) = true := by simp [hc4, hc5]
  funext pn pd adir ajo u g
  simp only [rowW, rowV, h1, h2, Bool.cond_true]
  rfl

/-- Zipping the constant sequence `k` of length `|l|` with `l` under `f` is mapping `f k`. -/
theorem zipR_rangeMap_left (f : ℕ → ℕ → ℕ) (k : ℕ) {l : List ℕ} {n : ℕ} (hl : l.length = n) :
    zipR f (rangeMap (fun _ => k) n) l = mapR (f k) l := by
  rw [zipR_eq, mapR_eq, rangeMap_eq]
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp

/-- Zipping `l` with the constant sequence `k` of length `|l|` under `f` is mapping
`fun u => f u k`. -/
theorem zipR_rangeMap_right (f : ℕ → ℕ → ℕ) (k : ℕ) {l : List ℕ} {n : ℕ} (hl : l.length = n) :
    zipR f l (rangeMap (fun _ => k) n) = mapR (fun u => f u k) l := by
  rw [zipR_eq, mapR_eq, rangeMap_eq]
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp

/-- The check of the row `(c, o)` in one pass: the scans of `rowCheck`, with the values
`10^8 Ū_c` read from `uSegF`, the constant sequence `10^8` of `rowU` (for `c = 2`) or `rowG` (for
`o ≥ 15`) folded into the step, and the case distinctions on `c` taken once. -/
noncomputable def rowCheckF (c o pn pd adir ajo T1 M1 m1 T3 M3 m3 : ℕ) : Bool :=
  if c < 3 then
    scanMapR (rowW c pn pd adir ajo 100000000) T1 M1 m1 T3 M3 m3 (rowG o) false 0 (16384 * T1)
      (16384 * T1) (16384 * T1) 0 (16384 * T3) (16384 * T3) (16384 * T3)
  else if c = 4 ∨ c = 5 then
    scanZipR (rowW c pn pd adir ajo) T1 M1 m1 T3 M3 m3 (uSegF c (17 - o) 0 32768) (rowG o) false
      0 (16384 * T1) (16384 * T1) (16384 * T1) 0 (16384 * T3) (16384 * T3) (16384 * T3)
  else if 15 ≤ o then
    scanMapR (fun u => rowWG pn pd adir ajo u 100000000) T1 M1 m1 T3 M3 m3
      (uSegF c (17 - o) 0 32768) false
      0 (16384 * T1) (16384 * T1) (16384 * T1) 0 (16384 * T3) (16384 * T3) (16384 * T3)
  else
    scanZipR (rowWG pn pd adir ajo) T1 M1 m1 T3 M3 m3 (uSegF c (17 - o) 0 32768) (rowG o) false
      0 (16384 * T1) (16384 * T1) (16384 * T1) 0 (16384 * T3) (16384 * T3) (16384 * T3)

/-- The one-pass check `rowCheckF` is the row check `rowCheck`. -/
theorem rowCheckF_eq (c o pn pd adir ajo T1 M1 m1 T3 M3 m3 : ℕ) :
    rowCheckF c o pn pd adir ajo T1 M1 m1 T3 M3 m3 =
      rowCheck c o pn pd adir ajo T1 M1 m1 T3 M3 m3 := by
  have hU3 : 3 ≤ c → rowU c o = uSegF c (17 - o) 0 32768 := fun h => by
    rw [rowU, ite_eq_left h, uSegF_eq]
  unfold rowCheckF rowCheck rowList
  by_cases hc : c < 3
  · rw [ite_eq_left hc, scanMapR_eq, show rowU c o = rangeMap (fun _ => 100000000) 32768 by
      rw [rowU, ite_eq_right (by omega)], zipR_rangeMap_left _ _ (length_rowG o)]
  rw [ite_eq_right hc, hU3 (by omega)]
  by_cases h45 : c = 4 ∨ c = 5
  · rw [ite_eq_left h45, scanZipR_eq]
  rw [ite_eq_right h45, rowWG_eq (c := c) (by omega) (by omega) (by omega)]
  by_cases ho : 15 ≤ o
  · rw [ite_eq_left ho, scanMapR_eq, show rowG o = rangeMap (fun _ => 100000000) 32768 by
      rw [rowG, ite_eq_right (by omega)], zipR_rangeMap_right _ _
        (by rw [← hU3 (by omega)]; exact length_rowU c o)]
  · rw [ite_eq_right ho, scanZipR_eq]

/-- A passing one-pass check is a passing row check. -/
theorem rowCheck_of_rowCheckF {c o pn pd adir ajo T1 M1 m1 T3 M3 m3 : ℕ}
    (h : rowCheckF c o pn pd adir ajo T1 M1 m1 T3 M3 m3 = true) :
    rowCheck c o pn pd adir ajo T1 M1 m1 T3 M3 m3 = true := by
  rwa [← rowCheckF_eq]

end C3H17Values

end CollatzPosDens
