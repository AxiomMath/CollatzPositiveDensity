/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCapUpper
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Packed lanes and exact square roots for the height-seventeen certificate

A natural number `X` is read as a vector of *lanes* of width `w`: the `i`-th lane is
`⌊X / 2^{w i}⌋ mod 2^w`. A finite vector `f 0, …, f (n - 1)` with entries below `2^w` is packed
into `∑_{i<n} f i 2^{w i}`; packing is additive, so a sum of packed vectors whose lane sums stay
below `2^w` is the packed vector of the lane sums. The *window* `⌊X / 2^{w s}⌋ mod 2^{w n}` is the
packed vector of the lanes `s, …, s + n - 1` of `X`.

The least natural number whose square is at least a natural number `m` is computed by Newton's
iteration, checked against the defining inequalities, with a fallback that is again Newton's
iteration in natural-number arithmetic, and shown equal to `natCeilSqrt m`.

## Main definitions

* `CollatzPosDens.C3H17Values.lane`: the `i`-th lane of width `w`.
* `CollatzPosDens.C3H17Values.packF`: the packed vector of a function on `{0, …, n - 1}`.
* `CollatzPosDens.C3H17Values.win`: the window of `n` lanes starting at lane `s`.
* `CollatzPosDens.C3H17Values.ceilSqrt`: the least `k` with `m ≤ k^2`, by Newton's iteration.

## Main results

* `CollatzPosDens.C3H17Values.lane_packF`: the lanes of a packed vector are its entries.
* `CollatzPosDens.C3H17Values.win_eq_packF`: a window is the packed vector of its lanes.
* `CollatzPosDens.C3H17Values.lane_sum_win`: the lanes of a sum of windows are the sums of
  lanes, when no lane sum overflows.
* `CollatzPosDens.C3H17Values.ceilSqrt_eq`: `ceilSqrt m = natCeilSqrt m`.
-/

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

open Finset

/-! ### Lanes -/

/-- The `i`-th lane of width `w` of `X`: `⌊X / 2^{w i}⌋ mod 2^w`, computed by a shift. -/
def lane (w X i : ℕ) : ℕ := (X >>> (w * i)) % 2 ^ w

/-- The `i`-th lane of width `w` of `X` is `⌊X / 2^{w i}⌋ mod 2^w`. -/
theorem lane_def' (w X i : ℕ) : lane w X i = X / 2 ^ (w * i) % 2 ^ w := by
  rw [lane, Nat.shiftRight_eq_div_pow]

/-- The lane `0` of width `w` of `X` is `X mod 2^w`. -/
theorem lane_zero (w X : ℕ) : lane w X 0 = X % 2 ^ w := by simp [lane_def']

/-- The lane `i + 1` of `X` is the lane `i` of `⌊X / 2^w⌋`. -/
theorem lane_succ (w X i : ℕ) : lane w X (i + 1) = lane w (X / 2 ^ w) i := by
  simp only [lane_def', Nat.div_div_eq_div_mul, ← pow_add]
  congr 3
  ring

/-- The lane `i` of `⌊X / 2^{w s}⌋` is the lane `s + i` of `X`. -/
theorem lane_div (w X s i : ℕ) : lane w (X / 2 ^ (w * s)) i = lane w X (s + i) := by
  simp only [lane_def', Nat.div_div_eq_div_mul, ← pow_add, mul_add]

/-- Every lane of width `w` is below `2^w`. -/
theorem lane_lt (w X i : ℕ) : lane w X i < 2 ^ w := Nat.mod_lt _ (by positivity)

/-- The lanes of `A + 2^{w m} B` with `A < 2^{w m}`: those of `A` below `m`, then those of
`B`. -/
theorem lane_add_mul {w m A : ℕ} (hA : A < 2 ^ (w * m)) (B i : ℕ) :
    lane w (A + 2 ^ (w * m) * B) i = if i < m then lane w A i else lane w B (i - m) := by
  induction m generalizing A i with
  | zero =>
    simp only [mul_zero, pow_zero, Nat.lt_one_iff] at hA
    subst hA
    simp
  | succ m ih =>
    have hA' : A / 2 ^ w < 2 ^ (w * m) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      convert hA using 2
    have hsplit : 2 ^ (w * (m + 1)) * B = 2 ^ w * (2 ^ (w * m) * B) := by
      rw [mul_add, mul_one, pow_add]
      ring
    have hdiv : (A + 2 ^ (w * (m + 1)) * B) / 2 ^ w = A / 2 ^ w + 2 ^ (w * m) * B := by
      rw [hsplit]
      exact Nat.add_mul_div_left _ _ (by positivity)
    rcases i with _ | i
    · simp only [lane_zero, Nat.zero_lt_succ, ite_true]
      rw [hsplit]
      exact Nat.add_mul_mod_self_left _ _ _
    · rw [lane_succ, hdiv, ih hA', lane_succ]
      simp only [Nat.add_lt_add_iff_right, Nat.add_sub_add_right]

/-! ### Packed vectors -/

/-- The packed vector `∑_{i<n} f i 2^{w i}` of the entries `f 0, …, f (n - 1)`. -/
def packF (w n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ i ∈ range n, f i * 2 ^ (w * i)

/-- The packed vector of `f 0, …, f n` is `f 0` plus `2^w` times the packed vector of
`f 1, …, f n`. -/
theorem packF_succ (w n : ℕ) (f : ℕ → ℕ) :
    packF w (n + 1) f = f 0 + 2 ^ w * packF w n (fun i => f (i + 1)) := by
  rw [packF, sum_range_succ', packF, Finset.mul_sum, add_comm]
  congr 1
  · simp
  · refine sum_congr rfl fun i _ => ?_
    rw [mul_add, mul_one, pow_add]
    ring

/-- The lanes of a packed vector with entries below `2^w` are its entries. -/
theorem lane_packF {w : ℕ} : ∀ {n : ℕ} {f : ℕ → ℕ}, (∀ i < n, f i < 2 ^ w) →
    ∀ {k : ℕ}, k < n → lane w (packF w n f) k = f k
  | 0, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, f, hf, k, hk => by
    rw [packF_succ]
    rcases k with _ | k
    · rw [lane_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf 0 (Nat.zero_lt_succ _))]
    · rw [lane_succ, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt (hf 0 (Nat.zero_lt_succ _)), zero_add]
      exact lane_packF (fun i hi => hf (i + 1) (by omega)) (by omega)

/-- Reducing modulo `2^{w n}` keeps the first `n` lanes. -/
theorem mod_eq_packF (w : ℕ) : ∀ (n Y : ℕ), Y % 2 ^ (w * n) = packF w n (lane w Y)
  | 0, Y => by simp [packF, Nat.mod_one]
  | n + 1, Y => by
    rw [packF_succ, show w * (n + 1) = w + w * n by ring, pow_add, Nat.mod_mul, lane_zero,
      mod_eq_packF w n (Y / 2 ^ w)]
    congr 2
    unfold packF
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [lane_succ]

/-- The window of `n` lanes of `X` starting at lane `s`, computed by a shift. -/
def win (w X s n : ℕ) : ℕ := (X >>> (w * s)) % 2 ^ (w * n)

/-- The window of `n` lanes of `X` starting at lane `s` is the packed vector of the lanes
`s, …, s + n - 1` of `X`. -/
theorem win_eq_packF (w X s n : ℕ) : win w X s n = packF w n (fun i => lane w X (s + i)) := by
  rw [win, Nat.shiftRight_eq_div_pow, mod_eq_packF]
  congr 1
  funext i
  rw [lane_div]

/-- Packing is additive. -/
theorem sum_packF {ι : Type*} (P : Finset ι) (w n : ℕ) (f : ι → ℕ → ℕ) :
    ∑ p ∈ P, packF w n (f p) = packF w n (fun i => ∑ p ∈ P, f p i) := by
  simp only [packF, Finset.sum_mul]
  exact Finset.sum_comm

/-- The lanes of a sum of windows are the sums of their lanes, if every lane sum is below
`2^w`. -/
theorem lane_sum_win {ι : Type*} (P : Finset ι) {w n : ℕ} (X s : ι → ℕ)
    (hb : ∀ i < n, ∑ p ∈ P, lane w (X p) (s p + i) < 2 ^ w) {k : ℕ} (hk : k < n) :
    lane w (∑ p ∈ P, win w (X p) (s p) n) k = ∑ p ∈ P, lane w (X p) (s p + k) := by
  simp only [win_eq_packF]
  rw [sum_packF]
  exact lane_packF hb hk

/-! ### Kernel-friendly list and order operations -/

/-- The list `[f k, …, f (k + n - 1)]`, by a recursion that the kernel evaluates directly. -/
noncomputable def rangeMapFrom (f : ℕ → ℕ) (n : ℕ) : ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => []) (fun _ ih k => f k :: ih (Nat.add k 1)) n

/-- The list `[f 0, …, f (n - 1)]`. -/
noncomputable def rangeMap (f : ℕ → ℕ) (n : ℕ) : List ℕ := rangeMapFrom f n 0

/-- `rangeMapFrom f n k` is the image of `[k, …, k + n - 1]` under `f`. -/
theorem rangeMapFrom_eq (f : ℕ → ℕ) : ∀ n k, rangeMapFrom f n k = (List.range' k n).map f
  | 0, _ => rfl
  | n + 1, k => by
    rw [List.range'_succ, List.map_cons, ← rangeMapFrom_eq f n (k + 1)]
    rfl

/-- `rangeMap f n` is the image of `[0, …, n - 1]` under `f`. -/
theorem rangeMap_eq (f : ℕ → ℕ) (n : ℕ) : rangeMap f n = (List.range n).map f := by
  rw [rangeMap, rangeMapFrom_eq, List.range_eq_range']

/-- `rangeMap f n` has length `n`. -/
theorem length_rangeMap (f : ℕ → ℕ) (n : ℕ) : (rangeMap f n).length = n := by
  simp [rangeMap_eq]

/-- The entry `k < n` of `rangeMap f n` is `f k`. -/
theorem getD_rangeMap (f : ℕ → ℕ) {n k : ℕ} (hk : k < n) : (rangeMap f n).getD k 0 = f k := by
  simp [rangeMap_eq, List.getD_eq_getElem?_getD, hk]

/-- The minimum `a - (a - b)`, by arithmetic that the kernel evaluates directly. -/
def natMin (a b : ℕ) : ℕ := Nat.sub a (Nat.sub a b)

/-- The maximum `a + (b - a)`, by arithmetic that the kernel evaluates directly. -/
def natMax (a b : ℕ) : ℕ := Nat.add a (Nat.sub b a)

/-- `natMin a b` is `min a b`. -/
@[simp] theorem natMin_eq (a b : ℕ) : natMin a b = min a b := by
  simp only [natMin, Nat.sub_eq]; omega

/-- `natMax a b` is `max a b`. -/
@[simp] theorem natMax_eq (a b : ℕ) : natMax a b = max a b := by
  simp only [natMax, Nat.add_eq, Nat.sub_eq]; omega

/-- `map`, by a recursion that the kernel evaluates directly. -/
noncomputable def mapR (f : ℕ → ℕ) (l : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun x _ ih => f x :: ih) l

/-- `mapR f l` is `l.map f`. -/
theorem mapR_eq (f : ℕ → ℕ) : ∀ l, mapR f l = l.map f
  | [] => rfl
  | x :: l => by rw [List.map_cons, ← mapR_eq f l]; rfl

/-- `zipWith`, by a recursion that the kernel evaluates directly. -/
noncomputable def zipR (f : ℕ → ℕ → ℕ) (l : List ℕ) : List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun _ => [])
    (fun x _ ih l' => List.rec (motive := fun _ => List ℕ) [] (fun y ys _ => f x y :: ih ys) l') l

/-- `zipR f l l'` is `List.zipWith f l l'`. -/
theorem zipR_eq (f : ℕ → ℕ → ℕ) : ∀ l l', zipR f l l' = List.zipWith f l l'
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: l, y :: l' => by rw [List.zipWith_cons_cons, ← zipR_eq f l l']; rfl

/-- `all` of a pointwise relation of two lists, by a recursion that the kernel evaluates
directly. -/
noncomputable def allZipR (p : ℕ → ℕ → Bool) (l : List ℕ) : List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun _ => true)
    (fun x _ ih l' => List.rec (motive := fun _ => Bool) true (fun y ys _ => p x y && ih ys) l') l

/-- If `allZipR p l l'` holds, then `p` holds of the entries `k` of `l` and `l'` for every `k`
below both lengths. -/
theorem allZipR_getD {p : ℕ → ℕ → Bool} : ∀ {l l' : List ℕ}, allZipR p l l' = true →
    ∀ {k : ℕ}, k < l.length → k < l'.length → p (l.getD k 0) (l'.getD k 0) = true
  | [], _, _, k, hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: _, [], _, k, _, hk => absurd hk (Nat.not_lt_zero _)
  | x :: l, y :: l', h, k, hk, hk' => by
    have h' : (p x y && allZipR p l l') = true := h
    rw [Bool.and_eq_true] at h'
    rcases k with _ | k
    · simpa using h'.1
    · simp only [List.getD_cons_succ]
      exact allZipR_getD h'.2 (by simpa using hk) (by simpa using hk')

/-- `append`, by a recursion that the kernel evaluates directly. -/
noncomputable def appendR (l l' : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) l' (fun x _ ih => x :: ih) l

/-- `appendR l l'` is `l ++ l'`. -/
theorem appendR_eq (l' : List ℕ) : ∀ l, appendR l l' = l ++ l'
  | [] => rfl
  | x :: l => by rw [List.cons_append, ← appendR_eq l' l]; rfl

/-- The concatenation `g k ++ g (k + 1) ++ ⋯ ++ g (k + m - 1)`. -/
noncomputable def flatRangeFrom (g : ℕ → List ℕ) (m : ℕ) : ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
    (fun _ ih k => appendR (g k) (ih (Nat.add k 1))) m

/-- `flatRangeFrom g m k` is the concatenation of the image of `[k, …, k + m - 1]` under `g`. -/
theorem flatRangeFrom_eq (g : ℕ → List ℕ) :
    ∀ m k, flatRangeFrom g m k = ((List.range' k m).map g).flatten
  | 0, _ => rfl
  | m + 1, k => by
    rw [List.range'_succ, List.map_cons, List.flatten_cons, ← flatRangeFrom_eq g m (k + 1),
      ← appendR_eq]
    rfl

/-- `drop`, by a recursion on the list that the kernel evaluates directly; the list is forced
at every step. -/
noncomputable def dropR (n : ℕ) (l : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
    (fun x xs ih k => cond (Nat.beq k 0) (x :: xs) (ih (Nat.sub k 1))) l n

/-- `dropR n l` is `l.drop n`. -/
theorem dropR_eq : ∀ (n : ℕ) (l : List ℕ), dropR n l = l.drop n
  | _, [] => by simp [dropR]
  | 0, x :: l => rfl
  | n + 1, x :: l => by
    change cond (Nat.beq (n + 1) 0) (x :: l) (dropR (Nat.sub (n + 1) 1) l) = _
    rw [show Nat.beq (n + 1) 0 = false from rfl, Bool.cond_false, show Nat.sub (n + 1) 1 = n from
      Nat.add_sub_cancel n 1, dropR_eq n l]
    rfl

/-- `take`, by a recursion that the kernel evaluates directly. -/
noncomputable def takeR (n : ℕ) (l : List ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ → List ℕ) (fun _ => [])
    (fun _ ih l => List.rec (motive := fun _ => List ℕ) [] (fun x xs _ => x :: ih xs) l) n l

/-- `takeR n l` is `l.take n`. -/
theorem takeR_eq : ∀ (n : ℕ) (l : List ℕ), takeR n l = l.take n
  | 0, _ => rfl
  | n + 1, [] => rfl
  | n + 1, x :: l => by
    change x :: takeR n l = _
    rw [takeR_eq n l]; rfl

/-- The lanes `0, …, n - 1` of width `w` of `X`, by successive shifts. -/
noncomputable def unpackR (w n : ℕ) (X : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
    (fun _ ih Y => Nat.mod Y (2 ^ w) :: ih (Nat.shiftRight Y w)) n X

/-- `unpackR w n X` is the list of the lanes `0, …, n - 1` of width `w` of `X`. -/
theorem unpackR_eq (w : ℕ) : ∀ (n X : ℕ), unpackR w n X = (List.range n).map (lane w X)
  | 0, _ => rfl
  | n + 1, X => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    change X % 2 ^ w :: unpackR w n (X >>> w) = _
    rw [unpackR_eq w n, lane_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, lane_succ, Nat.shiftRight_eq_div_pow]

/-- `condR b x y` is `cond b x y`, written as the bare recursor application `Bool.rec y x b`, which
the kernel reduces in one step (`cond`, a definition by pattern matching, takes several). -/
scoped macro "condR " b:term:max x:term:max y:term:max : term =>
  `(Bool.rec (motive := fun _ => _) $y $x $b)

/-- `Nat.ble a b` is `true` when `a ≤ b`. -/
theorem ble_true {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := by
  rw [Nat.ble_eq]; exact h

/-- `Nat.ble a b` is `false` when `¬ a ≤ b`. -/
theorem ble_false {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; exact h

/-- `getD`, by a recursion on the list that the kernel evaluates directly. -/
noncomputable def getR {α : Type*} (d : α) (l : List α) : ℕ → α :=
  List.rec (motive := fun _ => ℕ → α) (fun _ => d)
    (fun x _ ih k => condR (Nat.beq k 0) x (ih (Nat.sub k 1))) l

/-- `getR d l k` is `l.getD k d`. -/
theorem getR_eq {α : Type*} (d : α) : ∀ (l : List α) (k : ℕ), getR d l k = l.getD k d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: l, k + 1 => by
    change getR d l (Nat.sub (k + 1) 1) = _
    rw [show Nat.sub (k + 1) 1 = k from Nat.add_sub_cancel k 1, getR_eq d l k]
    rfl

/-- The packed number `l₀ + 2^w l₁ + 2^{2w} l₂ + ⋯` of a list, by a recursion that the kernel
evaluates directly. -/
noncomputable def packR (w : ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.add x (Nat.shiftLeft ih w)) l

/-- The packed number of `x :: l` is `x` plus `2^w` times the packed number of `l`. -/
theorem packR_cons (w x : ℕ) (l : List ℕ) : packR w (x :: l) = x + 2 ^ w * packR w l := by
  change Nat.add x (Nat.shiftLeft (packR w l) w) = _
  rw [Nat.add_eq, show Nat.shiftLeft (packR w l) w = packR w l <<< w from rfl, Nat.shiftLeft_eq,
    mul_comm]

/-- The lane `q` of a packed list is its entry `q`, if the entries `0, …, q` are below `2^w`. -/
theorem lane_packR {w : ℕ} : ∀ (l : List ℕ) (q : ℕ), (∀ i ≤ q, l.getD i 0 < 2 ^ w) →
    lane w (packR w l) q = l.getD q 0
  | [], q, _ => by simp [packR, lane_def']
  | x :: l, q, h => by
    have hx : x < 2 ^ w := by simpa using h 0 (Nat.zero_le _)
    rw [packR_cons]
    rcases q with _ | q
    · rw [lane_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
      rfl
    · rw [lane_succ, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add,
        List.getD_cons_succ]
      exact lane_packR l q fun i hi => by simpa using h (i + 1) (by omega)

/-- A lane of width `w` of a lane of width `w m` is a lane of width `w`. -/
theorem lane_lane {w m : ℕ} (X q : ℕ) {r : ℕ} (hr : r < m) :
    lane w (lane (w * m) X q) r = lane w X (m * q + r) := by
  simp only [lane_def']
  have h1 : 2 ^ (w * (m * q + r)) = 2 ^ (w * m * q) * 2 ^ (w * r) := by
    rw [← pow_add]; congr 1; ring
  have h2 : 2 ^ (w * m) = 2 ^ (w * r) * 2 ^ (w * (m - r)) := by
    rw [← pow_add]; congr 1
    rw [← mul_add]; congr 1; omega
  have h3 : 2 ^ w ∣ 2 ^ (w * (m - r)) :=
    pow_dvd_pow 2 (Nat.le_mul_of_pos_right w (by omega))
  rw [h1, ← Nat.div_div_eq_div_mul, h2, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ h3]

/-- The lanes `0, …, k - 1` of width `w` of `Z`, followed by `rest`, by successive shifts. -/
noncomputable def unpackOnto (w k Z : ℕ) (rest : List ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => rest)
    (fun _ ih Y => Nat.mod Y (2 ^ w) :: ih (Nat.shiftRight Y w)) k Z

/-- `unpackOnto w k Z rest` is the list of the lanes `0, …, k - 1` of width `w` of `Z`, followed
by `rest`. -/
theorem unpackOnto_eq (w : ℕ) (rest : List ℕ) :
    ∀ k Z, unpackOnto w k Z rest = (List.range k).map (lane w Z) ++ rest
  | 0, _ => rfl
  | k + 1, Z => by
    change Z % 2 ^ w :: unpackOnto w k (Z >>> w) rest = _
    rw [unpackOnto_eq w rest k, List.range_succ_eq_map, List.map_cons, List.map_map, lane_zero,
      List.cons_append]
    congr 2
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, lane_succ, Nat.shiftRight_eq_div_pow]

/-- Reducing modulo `2^{w n}` keeps the lanes below `n`. -/
theorem lane_mod_pow {w n : ℕ} (X : ℕ) {i : ℕ} (hi : i < n) :
    lane w (X % 2 ^ (w * n)) i = lane w X i := by
  rw [mod_eq_packF, lane_packF (fun _ _ => lane_lt _ _ _) hi]

/-- The lanes `0, …, 256 m + r - 1` of width `32` of `Z`, unpacked `256` at a time, so that every
shift is of a number of at most `8192` bits. -/
noncomputable def chunksR (m r Z : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun Y => unpackOnto 32 r (Y % 2 ^ (32 * 256)) [])
    (fun _ ih Y => unpackOnto 32 256 (Y % 2 ^ (32 * 256)) (ih (Y >>> (32 * 256)))) m Z

/-- For `r ≤ 256`, `chunksR m r Z` is the list of the lanes `0, …, 256 m + r - 1` of width `32`
of `Z`. -/
theorem chunksR_eq {r : ℕ} (hr : r ≤ 256) :
    ∀ m Z, chunksR m r Z = (List.range (256 * m + r)).map (lane 32 Z)
  | 0, Z => by
    change unpackOnto 32 r (Z % 2 ^ (32 * 256)) [] = _
    rw [unpackOnto_eq, List.append_nil, Nat.mul_zero, Nat.zero_add]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    exact lane_mod_pow Z (by omega)
  | m + 1, Z => by
    change unpackOnto 32 256 (Z % 2 ^ (32 * 256)) (chunksR m r (Z >>> (32 * 256))) = _
    rw [unpackOnto_eq, chunksR_eq hr m, show 256 * (m + 1) + r = 256 + (256 * m + r) by ring,
      @List.range_add 256 (256 * m + r), List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      exact lane_mod_pow Z hi
    · refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp, Nat.shiftRight_eq_div_pow, lane_div]

/-- `X + X <<< n = X + 2^n X`. -/
theorem add_shiftLeft_eq (X n : ℕ) : X + X <<< n = X + 2 ^ n * X := by
  rw [Nat.shiftLeft_eq, mul_comm]

/-- The packed number of a list `l` with entries below `2^w` is below `2^{w |l|}`. -/
theorem packR_lt {w : ℕ} : ∀ {l : List ℕ}, (∀ x ∈ l, x < 2 ^ w) → packR w l < 2 ^ (w * l.length)
  | [], _ => by simp [packR]
  | x :: l, h => by
    have hx := h x (by simp)
    have hl := packR_lt (l := l) fun y hy => h y (by simp [hy])
    rw [packR_cons, List.length_cons, mul_add, mul_one, pow_add]
    calc x + 2 ^ w * packR w l < 2 ^ w + 2 ^ w * packR w l := by omega
      _ = 2 ^ w * (packR w l + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * l.length) := Nat.mul_le_mul_left _ hl
      _ = 2 ^ (w * l.length) * 2 ^ w := by ring

/-! ### Ceiling division -/

/-- The natural ceiling division `⌊(Z + Y - 1) / Y⌋` is the integer `⌈Z / Y⌉ = -⌊-Z / Y⌋`. -/
theorem ceilDiv_cast (Z Y : ℕ) (hY : 0 < Y) : (((Z + Y - 1) / Y : ℕ) : ℤ) = -((-(Z : ℤ)) / Y) := by
  have h1 := Nat.div_add_mod (Z + Y - 1) Y
  have h2 := Nat.mod_lt (Z + Y - 1) hY
  set q := (Z + Y - 1) / Y
  set ρ := (Z + Y - 1) % Y
  have h3 : ((Y * q + ρ : ℕ) : ℤ) = ((Z + Y - 1 : ℕ) : ℤ) := by rw [h1]
  push_cast [Nat.cast_sub (by omega : 1 ≤ Z + Y)] at h3
  have h4 : (ρ : ℤ) < Y := by exact_mod_cast h2
  have h5 : (0 : ℤ) ≤ ρ := by positivity
  have hq : (-(Z : ℤ)) / Y = -q :=
    ((Int.ediv_emod_unique (a := -(Z : ℤ)) (b := Y) (q := -q) (r := Y * q - Z)
      (by exact_mod_cast hY)).2 ⟨by ring, by linarith, by linarith⟩).1
  rw [hq, neg_neg]

/-! ### Exact ceiling square roots -/

/-- One Newton step `y ↦ ⌊(y + ⌊m / y⌋) / 2⌋` towards `√m`. -/
def newtonStep (m y : ℕ) : ℕ := Nat.div (Nat.add y (Nat.div m y)) 2

/-- A starting point for Newton's iteration: `2^{e+1}` for `4^e ≤ m < 4^{e+1}`, `e ≤ 28`, found
by binary search. -/
def newtonStart (m : ℕ) : ℕ :=
  cond (Nat.blt m 268435456)
    (cond (Nat.blt m 16384)
      (cond (Nat.blt m 64)
        (cond (Nat.blt m 4)
          (2)
          (cond (Nat.blt m 16)
            (4)
            (8)))
        (cond (Nat.blt m 1024)
          (cond (Nat.blt m 256)
            (16)
            (32))
          (cond (Nat.blt m 4096)
            (64)
            (128))))
      (cond (Nat.blt m 1048576)
        (cond (Nat.blt m 65536)
          (256)
          (cond (Nat.blt m 262144)
            (512)
            (1024)))
        (cond (Nat.blt m 16777216)
          (cond (Nat.blt m 4194304)
            (2048)
            (4096))
          (cond (Nat.blt m 67108864)
            (8192)
            (16384)))))
    (cond (Nat.blt m 4398046511104)
      (cond (Nat.blt m 17179869184)
        (cond (Nat.blt m 1073741824)
          (32768)
          (cond (Nat.blt m 4294967296)
            (65536)
            (131072)))
        (cond (Nat.blt m 274877906944)
          (cond (Nat.blt m 68719476736)
            (262144)
            (524288))
          (cond (Nat.blt m 1099511627776)
            (1048576)
            (2097152))))
      (cond (Nat.blt m 1125899906842624)
        (cond (Nat.blt m 70368744177664)
          (cond (Nat.blt m 17592186044416)
            (4194304)
            (8388608))
          (cond (Nat.blt m 281474976710656)
            (16777216)
            (33554432)))
        (cond (Nat.blt m 18014398509481984)
          (cond (Nat.blt m 4503599627370496)
            (67108864)
            (134217728))
          (cond (Nat.blt m 72057594037927936)
            (268435456)
            (536870912)))))

/-- Seven Newton steps from `newtonStart m`. -/
def newtonIter (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun y => y) (fun _ ih y => ih (newtonStep m y)) 7
    (newtonStart m)

/-- The candidate for the least `k` with `m ≤ k^2`, from the Newton value `s`: the least of
`s - 1`, `s`, `s + 1` whose square is at least `m`. -/
def ceilSqrtCand (m : ℕ) : ℕ :=
  let s := newtonIter m
  cond (Nat.ble 1 s && Nat.ble m (Nat.mul (Nat.sub s 1) (Nat.sub s 1))) (Nat.sub s 1)
    (cond (Nat.ble m (Nat.mul s s)) s (Nat.add s 1))

/-- The defining inequalities of the least `k` with `m ≤ k^2`. -/
def ceilSqrtOK (m k : ℕ) : Bool :=
  (Nat.beq m 0 && Nat.beq k 0) ||
    (Nat.ble 1 k && Nat.blt (Nat.mul (Nat.sub k 1) (Nat.sub k 1)) m && Nat.ble m (Nat.mul k k))

/-- At most `fuel` steps of Newton's iteration towards `⌊√n⌋` from `y`, stopping at the first
step that does not decrease. -/
def floorSqrtIter (n fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun y => y)
    (fun _ ih y => condR (Nat.blt (newtonStep n y) y) (ih (newtonStep n y)) y) fuel

/-- The least natural number `k` with `m ≤ k^2`, in natural-number arithmetic: `0` for `m = 0`,
and `⌊√(m - 1)⌋ + 1` otherwise, by Newton's iteration from `m - 1`. -/
def ceilSqrtNat (m : ℕ) : ℕ :=
  condR (Nat.beq m 0) 0 (Nat.succ (floorSqrtIter (Nat.sub m 1) (Nat.sub m 1) (Nat.sub m 1)))

/-- The least natural number `k` with `m ≤ k^2`: the Newton candidate when it satisfies the
defining inequalities, and `ceilSqrtNat m` otherwise. -/
def ceilSqrt (m : ℕ) : ℕ :=
  let k := ceilSqrtCand m
  cond (ceilSqrtOK m k) k (ceilSqrtNat m)

/-- With `fuel + 1` steps, the iteration takes a Newton step from `y` if it decreases, and
stops at `y` otherwise. -/
theorem floorSqrtIter_succ (n fuel y : ℕ) :
    floorSqrtIter n (fuel + 1) y =
      if newtonStep n y < y then floorSqrtIter n fuel (newtonStep n y) else y := by
  change Bool.rec (motive := fun _ => ℕ) y (floorSqrtIter n fuel (newtonStep n y))
    (Nat.blt (newtonStep n y) y) = _
  cases h : Nat.blt (newtonStep n y) y
  · have h' : ¬ newtonStep n y < y := by rw [← Nat.blt_eq, h]; decide
    simp only [h', ↓reduceIte]
  · have h' : newtonStep n y < y := by simpa [Nat.blt_eq] using h
    simp only [h', ↓reduceIte]

/-- A Newton step from any `y ≥ 1` stays above `⌊√n⌋`. -/
theorem lt_succ_newtonStep_sq {n y : ℕ} (hy : 1 ≤ y) :
    n < (newtonStep n y + 1) * (newtonStep n y + 1) := by
  change n < ((y + n / y) / 2 + 1) * ((y + n / y) / 2 + 1)
  have h1 := Nat.div_add_mod n y
  have h2 := Nat.mod_lt n hy
  set q := n / y
  set t := (y + q) / 2
  have ht : y + q + 1 ≤ 2 * (t + 1) := by omega
  have h3 : ((y + q + 1 : ℕ) : ℤ) ≤ 2 * ((t : ℤ) + 1) := by exact_mod_cast ht
  have h4 : (n : ℤ) < (y : ℤ) * (q + 1) := by
    have : (n : ℤ) = y * q + (n % y : ℕ) := by exact_mod_cast h1.symm
    have : ((n % y : ℕ) : ℤ) < y := by exact_mod_cast h2
    nlinarith
  have h5 : (0 : ℤ) ≤ (y + q + 1 : ℕ) := by positivity
  zify
  push_cast at h3 h5
  nlinarith [sq_nonneg ((y : ℤ) - q - 1)]

/-- Newton's iteration from `y` with `n < (y + 1)^2` and at least `y` steps of fuel ends at
`⌊√n⌋`. -/
theorem floorSqrtIter_spec (n : ℕ) : ∀ (fuel y : ℕ), n < (y + 1) * (y + 1) → y ≤ fuel →
    floorSqrtIter n fuel y * floorSqrtIter n fuel y ≤ n ∧
      n < (floorSqrtIter n fuel y + 1) * (floorSqrtIter n fuel y + 1)
  | 0, y, hy, hf => by
    obtain rfl : y = 0 := by omega
    exact ⟨Nat.zero_le _, hy⟩
  | fuel + 1, y, hy, hf => by
    rw [floorSqrtIter_succ]
    split_ifs with h
    · exact floorSqrtIter_spec n fuel _ (lt_succ_newtonStep_sq (by omega)) (by omega)
    · refine ⟨?_, hy⟩
      have : y ≤ n / y := by
        change ¬ (y + n / y) / 2 < y at h
        omega
      calc y * y ≤ n / y * y := Nat.mul_le_mul_right _ this
        _ ≤ n := Nat.div_mul_le_self n y

/-- `ceilSqrtNat m` satisfies the defining inequalities of the least `k` with `m ≤ k^2`. -/
theorem ceilSqrtOK_ceilSqrtNat (m : ℕ) : ceilSqrtOK m (ceilSqrtNat m) = true := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  · have hb : Nat.beq m 0 = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]; omega
    obtain ⟨h1, h2⟩ := floorSqrtIter_spec (m - 1) (m - 1) (m - 1) (by nlinarith) le_rfl
    change ceilSqrtOK m (Bool.rec (motive := fun _ => ℕ)
      (Nat.succ (floorSqrtIter (m - 1) (m - 1) (m - 1))) 0 (Nat.beq m 0)) = true
    rw [hb]
    generalize floorSqrtIter (m - 1) (m - 1) (m - 1) = s at h1 h2 ⊢
    simp only [ceilSqrtOK, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq,
      Nat.sub_eq, Nat.mul_eq, Nat.succ_sub_one, Nat.succ_eq_add_one]
    right
    exact ⟨⟨Nat.succ_pos s, by omega⟩, by omega⟩

/-- A `k` satisfying the defining inequalities is `natCeilSqrt m`. -/
theorem eq_natCeilSqrt_of_ceilSqrtOK {m k : ℕ} (h : ceilSqrtOK m k = true) :
    k = natCeilSqrt (m : ℚ) := by
  simp only [ceilSqrtOK, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq,
    Nat.sub_eq, Nat.mul_eq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨⟨h1, h2⟩, h3⟩
  · simp [natCeilSqrt]
  · symm
    refine natCeilSqrt_eq_of_lt_of_le ?_ ?_ h1
    · have : ((k - 1 : ℕ) : ℚ) * ((k - 1 : ℕ) : ℚ) < m := by exact_mod_cast h2
      rw [Nat.cast_sub h1, Nat.cast_one] at this
      nlinarith
    · have : (m : ℚ) ≤ (k : ℚ) * (k : ℚ) := by exact_mod_cast h3
      nlinarith

/-- `ceilSqrt m` is `natCeilSqrt m`. -/
theorem ceilSqrt_eq (m : ℕ) : ceilSqrt m = natCeilSqrt (m : ℚ) := by
  simp only [ceilSqrt]
  cases h : ceilSqrtOK m (ceilSqrtCand m)
  · exact eq_natCeilSqrt_of_ceilSqrtOK (ceilSqrtOK_ceilSqrtNat m)
  · exact eq_natCeilSqrt_of_ceilSqrtOK h

/-! ### Square roots in the middle range -/

/-- A starting point for Newton's iteration from above on `2^{21} ≤ m < 2^{54}`:
`⌈2^{(k+1)/2}⌉` for `2^k ≤ m < 2^{k+1}`, found by binary search. -/
def startMid (m : ℕ) : ℕ :=
  condR (Nat.ble 137438953472 m)
    (condR (Nat.ble 35184372088832 m)
      (condR (Nat.ble 562949953421312 m)
        (condR (Nat.ble 2251799813685248 m)
          (condR (Nat.ble 4503599627370496 m)
            (condR (Nat.ble 9007199254740992 m) 134217728 94906266)
            67108864)
          (condR (Nat.ble 1125899906842624 m) 47453133 33554432))
        (condR (Nat.ble 140737488355328 m)
          (condR (Nat.ble 281474976710656 m) 23726567 16777216)
          (condR (Nat.ble 70368744177664 m) 11863284 8388608)))
      (condR (Nat.ble 2199023255552 m)
        (condR (Nat.ble 8796093022208 m)
          (condR (Nat.ble 17592186044416 m) 5931642 4194304)
          (condR (Nat.ble 4398046511104 m) 2965821 2097152))
        (condR (Nat.ble 549755813888 m)
          (condR (Nat.ble 1099511627776 m) 1482911 1048576)
          (condR (Nat.ble 274877906944 m) 741456 524288))))
    (condR (Nat.ble 536870912 m)
      (condR (Nat.ble 8589934592 m)
        (condR (Nat.ble 34359738368 m)
          (condR (Nat.ble 68719476736 m) 370728 262144)
          (condR (Nat.ble 17179869184 m) 185364 131072))
        (condR (Nat.ble 2147483648 m)
          (condR (Nat.ble 4294967296 m) 92682 65536)
          (condR (Nat.ble 1073741824 m) 46341 32768)))
      (condR (Nat.ble 33554432 m)
        (condR (Nat.ble 134217728 m)
          (condR (Nat.ble 268435456 m) 23171 16384)
          (condR (Nat.ble 67108864 m) 11586 8192))
        (condR (Nat.ble 8388608 m)
          (condR (Nat.ble 16777216 m) 5793 4096)
          (condR (Nat.ble 4194304 m) 2897 2048))))

/-- Four Newton steps from `startMid m`. -/
def newtonMid (m : ℕ) : ℕ :=
  newtonStep m (newtonStep m (newtonStep m (newtonStep m (startMid m))))

/-- The least natural number `k` with `m ≤ k^2`, from the Newton value `s`: `s + 1` when
`s^2 < m ≤ (s + 1)^2`, `s` when `(s - 1)^2 < m ≤ s^2` and `s ≥ 1`, and `ceilSqrt m` otherwise. -/
def ceilSqrtMid (m : ℕ) : ℕ :=
  let s := newtonMid m
  condR (Nat.ble m (Nat.mul s s))
    (condR (Nat.ble m (Nat.mul (Nat.sub s 1) (Nat.sub s 1))) (ceilSqrt m)
      (condR (Nat.ble 1 s) s (ceilSqrt m)))
    (condR (Nat.ble m (Nat.mul (Nat.add s 1) (Nat.add s 1))) (Nat.add s 1) (ceilSqrt m))

/-- `ceilSqrtMid m` is `ceilSqrt m`. -/
theorem ceilSqrtMid_eq (m : ℕ) : ceilSqrtMid m = ceilSqrt m := by
  simp only [ceilSqrtMid]
  generalize newtonMid m = s
  simp only [Nat.mul_eq, Nat.sub_eq, Nat.add_eq]
  rw [ceilSqrt_eq]
  by_cases h1 : m ≤ s * s
  · simp only [ble_true h1]
    by_cases h2 : m ≤ (s - 1) * (s - 1)
    · simp only [ble_true h2]
    · simp only [ble_false h2]
      by_cases h3 : 1 ≤ s
      · simp only [ble_true h3]
        symm
        refine natCeilSqrt_eq_of_lt_of_le ?_ ?_ h3
        · have : ((s - 1 : ℕ) : ℚ) * ((s - 1 : ℕ) : ℚ) < m := by exact_mod_cast not_le.1 h2
          rw [Nat.cast_sub h3, Nat.cast_one] at this
          nlinarith
        · have : (m : ℚ) ≤ (s : ℚ) * s := by exact_mod_cast h1
          nlinarith
      · simp only [ble_false h3]
  · simp only [ble_false h1]
    by_cases h2 : m ≤ (s + 1) * (s + 1)
    · simp only [ble_true h2]
      symm
      refine natCeilSqrt_eq_of_lt_of_le ?_ ?_ (Nat.le_add_left 1 s)
      · have : (s : ℚ) * s < m := by exact_mod_cast not_le.1 h1
        push_cast
        nlinarith
      · have : (m : ℚ) ≤ ((s + 1 : ℕ) : ℚ) * ((s + 1 : ℕ) : ℚ) := by exact_mod_cast h2
        push_cast at this ⊢
        nlinarith
    · simp only [ble_false h2]

end C3H17Values

end CollatzPosDens
