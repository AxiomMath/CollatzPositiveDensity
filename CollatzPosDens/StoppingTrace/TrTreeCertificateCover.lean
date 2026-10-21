/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.StoppingTrace.TrTreeCertificateCheck

/-!
# The checks of cells and of covers of the gap-zero certificate

The bound `CollatzPosDens.TrTreeCertificate.cellV` for the tree cost on a cell, compared with
$77/100 + T^{\mathrm{root}}_{0,12}$, gives the check `CollatzPosDens.TrTreeCertificate.cellOK`
of a cell; a cover of a residue class modulo `2^k` by residue classes and bisections of
`[-1/3, 1/3]` is checked cell by cell (`CollatzPosDens.TrTreeCertificate.checkR`).

## Main definitions

* `CollatzPosDens.TrTreeCertificate.F.cellV`: a copy of the cell bound for the kernel.
* `CollatzPosDens.TrTreeCertificate.cellOK`: the check of a cell.
* `CollatzPosDens.TrTreeCertificate.checkR`: the check of a cover of a residue class.
* `CollatzPosDens.TrTreeCertificate.Good`: the conclusion of the certificate for a residue class.

## Main results

* `CollatzPosDens.TrTreeCertificate.cellV_fast`: `F.cellV = cellV`.
* `CollatzPosDens.TrTreeCertificate.cell_spec`: an accepted cell bounds the tree cost by
  `77/100 + 1197/13107200`.
* `CollatzPosDens.TrTreeCertificate.good_of_checkR`: an accepted cover of a residue class proves
  the conclusion of the certificate for that class.

## Implementation notes

The kernel evaluates the cell bound through the copy `F.cellV` of `cellV`, written with bare
recursors over natural-number operations (the integer operations `F.iadd`, `F.imul`, `F.idiv`,
… are `Int.rec` applications over `Nat.add`, `Nat.mul`, `Nat.div`), which it reduces in far fewer
steps than the instances and pattern matching of the integer operations.

## References

* [Mazur, *Collatz positive density*], §9.8.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrTreeCertificate

open Complex Real

/-! ### A fast copy of the cell bound

The kernel evaluates arithmetic on `ℤ` through the instances and the pattern matching of
`Int.add`, `Int.mul` and `Int.ediv`, and conditions through `Decidable` instances, at a cost of
many reduction steps per operation. The definitions of the namespace `F` compute the same
numbers as the cell bound `cellV`, with every operation on `ℤ` a bare recursor `Int.rec` over the
natural-number operations that the kernel evaluates directly, every condition a `Nat.ble` and
every recursion a bare recursor; `cellV_fast` proves that `F.cellV` is `cellV`. -/

namespace F

local macro "condR " b:term:max x:term:max y:term:max : term =>
  `(Bool.rec (motive := fun _ => _) $y $x $b)

/-- `-a`. -/
noncomputable def ineg (a : ℤ) : ℤ :=
  Int.rec (motive := fun _ => ℤ)
    (fun m => Nat.rec (motive := fun _ => ℤ) (Int.ofNat 0) (fun k _ => Int.negSucc k) m)
    (fun m => Int.ofNat (Nat.succ m)) a

/-- `m - n` as an integer. -/
noncomputable def subNN (m n : ℕ) : ℤ :=
  condR (Nat.ble n m) (Int.ofNat (Nat.sub m n)) (Int.negSucc (Nat.sub (Nat.sub n m) 1))

/-- `a + b`. -/
noncomputable def iadd (a b : ℤ) : ℤ :=
  Int.rec (motive := fun _ => ℤ)
    (fun m => Int.rec (motive := fun _ => ℤ) (fun n => Int.ofNat (Nat.add m n))
      (fun n => subNN m (Nat.succ n)) b)
    (fun m => Int.rec (motive := fun _ => ℤ) (fun n => subNN n (Nat.succ m))
      (fun n => Int.negSucc (Nat.succ (Nat.add m n))) b) a

/-- `a - b`. -/
noncomputable def isub (a b : ℤ) : ℤ := iadd a (ineg b)

/-- `a * b`. -/
noncomputable def imul (a b : ℤ) : ℤ :=
  Int.rec (motive := fun _ => ℤ)
    (fun m => Int.rec (motive := fun _ => ℤ) (fun n => Int.ofNat (Nat.mul m n))
      (fun n => ineg (Int.ofNat (Nat.mul m (Nat.succ n)))) b)
    (fun m => Int.rec (motive := fun _ => ℤ) (fun n => ineg (Int.ofNat (Nat.mul (Nat.succ m) n)))
      (fun n => Int.ofNat (Nat.mul (Nat.succ m) (Nat.succ n))) b) a

/-- `a / d` (floor) for a natural `d`. -/
noncomputable def idiv (a : ℤ) (d : ℕ) : ℤ :=
  Int.rec (motive := fun _ => ℤ) (fun m => Int.ofNat (Nat.div m d))
    (fun m => condR (Nat.beq d 0) (Int.ofNat 0) (Int.negSucc (Nat.div m d))) a

/-- `a % d` for a positive natural `d`, as a natural number. -/
noncomputable def imodN (a : ℤ) (d : ℕ) : ℕ :=
  Int.rec (motive := fun _ => ℕ) (fun m => Nat.mod m d)
    (fun m => Nat.sub (Nat.sub d 1) (Nat.mod m d)) a

/-- `a.toNat`. -/
noncomputable def itoNat (a : ℤ) : ℕ := Int.rec (motive := fun _ => ℕ) (fun m => m) (fun _ => 0) a

/-- `a.natAbs`. -/
noncomputable def iabs (a : ℤ) : ℕ :=
  Int.rec (motive := fun _ => ℕ) (fun m => m) (fun m => Nat.succ m) a

/-- `a ≤ b`. -/
noncomputable def ile (a b : ℤ) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun _ => true) (fun _ => false) (isub b a)

/-- `min a b` for integers. -/
noncomputable def imin (a b : ℤ) : ℤ := condR (ile a b) a b

/-- `max a b` for integers. -/
noncomputable def imax (a b : ℤ) : ℤ := condR (ile a b) b a

/-- `min a b` for natural numbers. -/
noncomputable def nmin (a b : ℕ) : ℕ := condR (Nat.ble a b) a b

/-- `max a b` for natural numbers. -/
noncomputable def nmax (a b : ℕ) : ℕ := condR (Nat.ble a b) b a

/-- `l.getD i d`. -/
noncomputable def getR {α : Type} (d : α) (l : List α) : ℕ → α :=
  List.rec (motive := fun _ => ℕ → α) (fun _ => d)
    (fun x _ ih k => condR (Nat.beq k 0) x (ih (Nat.sub k 1))) l

/-- `l.drop n`. -/
noncomputable def dropR {α : Type} (n : ℕ) : List α → List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun l => l)
    (fun _ ih l => ih (List.rec (motive := fun _ => List α) [] (fun _ xs _ => xs) l)) n

/-- The fixed-point unit `2^60`, as a natural number. -/
noncomputable def P : ℕ := 1152921504606846976

/-- The fixed-point unit `2^60`, as an integer. -/
noncomputable def Pz : ℤ := Int.ofNat 1152921504606846976

/-- The fixed-point unit `2^72` of the tree costs, as a natural number. -/
noncomputable def Q : ℕ := 4722366482869645213696

/-- The fixed-point unit `2^72` of the tree costs, as an integer. -/
noncomputable def Qz : ℤ := Int.ofNat 4722366482869645213696

/-- One step `(S, T) ↦ (S + T, ⌊T · iY / (2^60 (n + 1))⌋)` of the Taylor terms of `exp(iy)`. -/
noncomputable def expStep (Y : ℤ) (n : ℕ) (p : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((iadd p.1.1 p.2.1, iadd p.1.2 p.2.2),
   (idiv (imul (ineg p.2.2) Y) (Nat.mul P (Nat.succ n)),
    idiv (imul p.2.1 Y) (Nat.mul P (Nat.succ n))))

/-- The Taylor terms `(∑_{m<n} T_m, T_n)` of `exp(iy)` at `y = Y / 2^60`, in fixed point with
unit `2^64`. -/
noncomputable def expI (Y : ℤ) (n : ℕ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  Nat.rec (motive := fun _ => (ℤ × ℤ) × (ℤ × ℤ))
    ((Int.ofNat 0, Int.ofNat 0), (Int.ofNat 18446744073709551616, Int.ofNat 0))
    (fun n ih => expStep Y n ih) n

/-- Multiplication by `i^n`. -/
noncomputable def rotI (n : ℕ) : ℤ × ℤ → ℤ × ℤ :=
  Nat.rec (motive := fun _ => ℤ × ℤ → ℤ × ℤ) (fun z => z) (fun _ ih z => ih (ineg z.2, z.1)) n

/-- The quarter-turn count `⌊4q + 1/2⌋` of `q = num / den`. -/
noncomputable def topN (num : ℤ) (den : ℕ) : ℤ :=
  idiv (iadd (imul (Int.ofNat 8) num) (Int.ofNat den)) (Nat.mul 2 den)

/-- `⌊2^60 · 2 π₀ τ⌋` for the reduced argument `τ = q - topN / 4` of `q = num / den`, where
`π₀ = 314159265358979323846 / 10^20`. -/
noncomputable def topY (num : ℤ) (den : ℕ) : ℤ :=
  idiv (imul (Int.ofNat (Nat.mul 314159265358979323846 P))
      (isub (imul (Int.ofNat 4) num) (imul (topN num den) (Int.ofNat den))))
    (Nat.mul 200000000000000000000 den)

/-- An approximation of `e(num / den)` in fixed point with unit `2^60`. -/
noncomputable def topI (num : ℤ) (den : ℕ) : ℤ × ℤ :=
  let s := (expI (topY num den) 18).1
  rotI (imodN (topN num den) 4) (idiv s.1 16, idiv s.2 16)

/-- Rounded squaring of a fixed-point Gaussian integer. -/
noncomputable def gsqI (z : ℤ × ℤ) : ℤ × ℤ :=
  (idiv (isub (imul z.1 z.1) (imul z.2 z.2)) P, idiv (imul (imul (Int.ofNat 2) z.1) z.2) P)

/-- The error after one rounded squaring, in units `2^{-60}`, rounded up. -/
noncomputable def errI (e : ℤ) : ℤ :=
  iadd (idiv (isub (iadd (imul e (iadd (Int.ofNat (Nat.mul 2 P)) e)) Pz) (Int.ofNat 1)) P)
    (Int.ofNat 2)

/-- The chain of `n + 1` successive rounded squares with their errors. -/
noncomputable def chainI (n : ℕ) : ℤ × ℤ → ℤ → List ((ℤ × ℤ) × ℤ) :=
  Nat.rec (motive := fun _ => ℤ × ℤ → ℤ → List ((ℤ × ℤ) × ℤ)) (fun z e => [(z, e)])
    (fun _ ih z e => (z, e) :: ih (gsqI z) (errI e)) n

/-- The sum of the first `n` entries of a chain, with the sum of their errors; missing entries
are charged the error `1` each. -/
noncomputable def sumI (n : ℕ) : List ((ℤ × ℤ) × ℤ) → (ℤ × ℤ) × ℤ :=
  Nat.rec (motive := fun _ => List ((ℤ × ℤ) × ℤ) → (ℤ × ℤ) × ℤ)
    (fun _ => ((Int.ofNat 0, Int.ofNat 0), Int.ofNat 0))
    (fun n ih l => List.rec (motive := fun _ => (ℤ × ℤ) × ℤ)
      ((Int.ofNat 0, Int.ofNat 0), Int.ofNat (Nat.mul (Nat.succ n) P))
      (fun ze l' _ => let r := ih l'
        ((iadd ze.1.1 r.1.1, iadd ze.1.2 r.1.2), iadd ze.2 r.2)) l) n

/-- The approximation `max |a| |b| + ⌊min |a| |b| / 2⌋ + 1` of `√(a² + b²)`. -/
noncomputable def sqGuess (a b : ℤ) : ℕ :=
  Nat.add (Nat.add (nmax (iabs a) (iabs b)) (Nat.div (nmin (iabs a) (iabs b)) 2)) 1

/-- `n` steps of Newton's iteration `q ↦ ⌈(N + q²) / (2q)⌉` for `√N`. -/
noncomputable def newtonUp (N : ℕ) (n : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun q => q)
    (fun _ ih q =>
      ih (Nat.div (Nat.sub (Nat.add (Nat.add N (Nat.mul q q)) (Nat.mul 2 q)) 1) (Nat.mul 2 q))) n

/-- The bound, in units `2^{-60}`, for a capped factor from the sum `T` of `t` chain entries
with its error and a Lipschitz term `lip`. -/
noncomputable def capI (t : ℕ) (T : (ℤ × ℤ) × ℤ) (lip : ℤ) : ℤ :=
  let N := itoNat (iadd (imul T.1.1 T.1.1) (imul T.1.2 T.1.2))
  let S := newtonUp N 3 (sqGuess T.1.1 T.1.2)
  condR (Nat.ble N (Nat.mul S S))
    (imin (iadd (imax (idiv (isub (iadd (iadd (Int.ofNat S) T.2) (Int.ofNat t)) (Int.ofNat 1)) t)
      (Int.ofNat 17592186044416)) lip) Pz)
    Pz

/-- The numerator `7 (c - 1) ℓ_c` of the Lipschitz constant `ℓ_c` of the capped factor. -/
noncomputable def lnum (c : ℕ) : ℕ :=
  getR 0 [0, 0, 0, 44, 132, 396, 924, 2156, 4620, 9900, 20460, 42284, 85932] c

/-- The Lipschitz term `⌈ℓ_c 9^r 2^{60} / (3 · 2^{d+L})⌉`, in units `2^{-60}`. -/
noncomputable def lipI (d r L c : ℕ) : ℤ :=
  Int.ofNat (Nat.div (Nat.sub (Nat.add (Nat.mul (Nat.mul (lnum c) (Nat.pow 9 r)) P)
    (Nat.mul (Nat.mul 21 (Nat.sub c 1)) (Nat.pow 2 (Nat.add d L)))) 1)
    (Nat.mul (Nat.mul 21 (Nat.sub c 1)) (Nat.pow 2 (Nat.add d L))))

/-- The chains of the cell with numerator `x`: for `r < 8`, the chain of successive squares
starting from an approximation of `e(9^r x / (3 · 2^{d+17}))`. -/
noncomputable def chainsI (x : ℤ) (d : ℕ) : List (List ((ℤ × ℤ) × ℤ)) :=
  Nat.rec (motive := fun _ => ℕ → List (List ((ℤ × ℤ) × ℤ))) (fun _ => [])
    (fun _ ih r => chainI 15 (topI (imul (Int.ofNat (Nat.pow 9 r)) x)
      (Nat.mul 3 (Nat.pow 2 (Nat.add d 17)))) (Int.ofNat 116) :: ih (Nat.succ r)) 8 0

/-- The bound, in units `2^{-60}`, for the retained factor of the letter `c` at the node
`(r, h)`: `2^{60}` unless `3 ≤ c ≤ 12`, `r < 8` and `h + c ≤ min k 17`. -/
noncomputable def facI (k d r h c : ℕ) (chs : List (List ((ℤ × ℤ) × ℤ))) : ℤ :=
  condR (Nat.ble 3 c && Nat.ble c 12 && Nat.blt r 8 && Nat.ble (Nat.add h c) k &&
      Nat.ble (Nat.add h c) 17)
    (capI (Nat.sub c 1) (sumI (Nat.sub c 1) (dropR (Nat.sub 17 (Nat.add h c)) (getR [] chs r)))
      (lipI d r (Nat.add h c) c))
    Pz

/-- The certified white test at the continuation `(r, h, c)`, `L = h + c`, of the cell with
numerator `x`: `L ≤ k` and `37037 D + 10^6 · 9^r < 10^6 min (N % D) (D - N % D)` for
`D = 3 · 2^{d+L}` and `N = 9^r x`. -/
noncomputable def whiteI (k d r L : ℕ) (x : ℤ) : Bool :=
  let D := Nat.mul 3 (Nat.pow 2 (Nat.add d L))
  let ρ := imodN (imul (Int.ofNat (Nat.pow 9 r)) x) D
  Nat.ble L k && Nat.blt (Nat.add (Nat.mul 37037 D) (Nat.mul 1000000 (Nat.pow 9 r)))
    (Nat.mul 1000000 (nmin ρ (Nat.sub D ρ)))

/-- The certified continuations: `2 ≤ c ≤ 12`, `h + c ≤ 14`, and `c ∉ {4, 5}` or the white
test passes. -/
noncomputable def edgeI (k d r h c : ℕ) (x : ℤ) : Bool :=
  Nat.ble 2 c && Nat.ble c 12 && Nat.ble (Nat.add h c) 14 &&
    (!(Nat.beq c 4 || Nat.beq c 5) || whiteI k d r (Nat.add h c) x)

/-- The Pascal weight `(c - 1) 2^{-c}`, in units `2^{-12}`. -/
noncomputable def wq (c : ℕ) : ℕ := Nat.mul (Nat.sub c 1) (Nat.pow 2 (Nat.sub 12 c))

/-- The product of `f` (units `2^{-60}`) and `g` (units `2^{-72}`), rounded up to units
`2^{-60}`. -/
noncomputable def mulUp (f g : ℤ) : ℤ := idiv (isub (iadd (imul f g) Qz) (Int.ofNat 1)) Q

/-- The cutoff `min {12, 17 - h}` for `h ≤ 17`, and `0` for `h > 17`. -/
noncomputable def cutoff (h : ℕ) : ℕ := condR (Nat.ble h 17) (nmin 12 (Nat.sub 17 h)) 0

/-- The sum over `c = c₀, …, c₀ + m - 1` of the terms of `stateI`. -/
noncomputable def stateSum (k d : ℕ) (x : ℤ) (chs : List (List ((ℤ × ℤ) × ℤ))) (next : List ℤ)
    (r h m : ℕ) : ℕ → ℤ :=
  Nat.rec (motive := fun _ => ℕ → ℤ) (fun _ => Int.ofNat 0)
    (fun _ ih c => iadd (imul (Int.ofNat (wq c)) (isub Pz (mulUp (facI k d r h c chs)
      (condR (edgeI k d r h c x) (getR Qz next (Nat.add h c)) Qz)))) (ih (Nat.succ c))) m

/-- The cost bound, in units `2^{-72}`, at the node `(r, h)`, given the bounds `next` of the
nodes `(r + 1, ·)`. -/
noncomputable def stateI (k d : ℕ) (x : ℤ) (chs : List (List ((ℤ × ℤ) × ℤ))) (next : List ℤ)
    (r h : ℕ) : ℤ :=
  isub Qz (stateSum k d x chs next r h (Nat.sub (cutoff h) 1) 2)

/-- The nodes `(r, h)` reached from the root: `(0, 0)`, and `(r, h)` with `1 ≤ r` and
`2r ≤ h ≤ 14`. -/
noncomputable def live (r h : ℕ) : Bool :=
  (Nat.beq r 0 && Nat.beq h 0) || (Nat.ble 1 r && Nat.ble (Nat.mul 2 r) h && Nat.ble h 14)

/-- The cost bounds of the nodes `(r, h)`, `h < 18`, given those of the nodes `(r + 1, ·)`;
nodes that are not reached carry the bound `2^{72}`. -/
noncomputable def rowI (k d : ℕ) (x : ℤ) (chs : List (List ((ℤ × ℤ) × ℤ))) (next : List ℤ)
    (r : ℕ) : List ℤ :=
  Nat.rec (motive := fun _ => ℕ → List ℤ) (fun _ => [])
    (fun _ ih h => condR (live r h) (stateI k d x chs next r h) Qz :: ih (Nat.succ h)) 18 0

/-- `f l`, with every entry of `l` brought to a constructor of `ℤ` first. -/
noncomputable def forceRow {β : Type} (l : List ℤ) (f : List ℤ → β) : β :=
  List.rec (motive := fun _ => (List ℤ → β) → β) (fun f => f [])
    (fun v _ ih f => Int.rec (motive := fun _ => β) (fun n => ih fun l' => f (Int.ofNat n :: l'))
      (fun n => ih fun l' => f (Int.negSucc n :: l')) v) l f

/-- The cost bound at the root, from the bounds `next` of the nodes `(n, ·)`, computing the
rows `n - 1, …, 0` in turn. -/
noncomputable def rowsI (k d : ℕ) (x : ℤ) (chs : List (List ((ℤ × ℤ) × ℤ))) (n : ℕ) : List ℤ → ℤ :=
  Nat.rec (motive := fun _ => List ℤ → ℤ) (fun next => getR Qz next 0)
    (fun n ih next => forceRow (rowI k d x chs next n) ih) n

/-- The cost bound, in units `2^{-72}`, for the cell with numerator `x`. -/
noncomputable def cellV (k d : ℕ) (x : ℤ) : ℤ := rowsI k d x (chainsI x d) 8 (List.replicate 18 Qz)

/-- The check `cellV k d x · 1310720000 < 1009374100 · 2^72` of a cell. -/
noncomputable def cellOK (k d : ℕ) (x : ℤ) : Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun v => Nat.blt (Nat.mul v 1310720000) (Nat.mul 1009374100 Q)) (fun _ => true) (cellV k d x)

end F

/-! ### The fast arithmetic agrees with the integer operations -/

namespace F

/-- `ineg a = -a`. -/
theorem ineg_eq (a : ℤ) : ineg a = -a := by
  rcases a with (_ | m) | m <;> rfl

/-- `subNN m n = m - n` in `ℤ`. -/
theorem subNN_eq (m n : ℕ) : subNN m n = (m : ℤ) - n := by
  unfold subNN
  cases h : Nat.ble n m
  · have : ¬ n ≤ m := fun h' => by simp [Nat.ble_eq_true_of_le h'] at h
    change Int.negSucc (Nat.sub (Nat.sub n m) 1) = _
    rw [Int.negSucc_eq]; simp only [Nat.sub_eq]; omega
  · have := Nat.le_of_ble_eq_true h
    change Int.ofNat (Nat.sub m n) = _
    simp only [Int.ofNat_eq_natCast, Nat.sub_eq]; omega

/-- `iadd a b = a + b`. -/
theorem iadd_eq (a b : ℤ) : iadd a b = a + b := by
  rcases a with m | m <;> rcases b with n | n <;>
    simp only [iadd, subNN_eq, Int.ofNat_eq_natCast, Int.negSucc_eq, Nat.add_eq,
      Nat.succ_eq_add_one] <;> push_cast <;> ring

/-- `isub a b = a - b`. -/
theorem isub_eq (a b : ℤ) : isub a b = a - b := by
  rw [isub, iadd_eq, ineg_eq, sub_eq_add_neg]

/-- `imul a b = a * b`. -/
theorem imul_eq (a b : ℤ) : imul a b = a * b := by
  rcases a with m | m <;> rcases b with n | n <;>
    simp only [imul, ineg_eq, Int.ofNat_eq_natCast, Int.negSucc_eq, Nat.mul_eq,
      Nat.succ_eq_add_one] <;> push_cast <;> ring

/-- `idiv a d = a / d`. -/
theorem idiv_eq (a : ℤ) (d : ℕ) : idiv a d = a / (d : ℤ) := by
  rcases a with m | m <;> rcases d with _ | d <;> rfl

/-- `imodN a d = a % d` for `0 < d`. -/
theorem imodN_eq (a : ℤ) {d : ℕ} (hd : 0 < d) : (imodN a d : ℤ) = a % (d : ℤ) := by
  rcases a with m | m
  · change ((m % d : ℕ) : ℤ) = _
    simp
  · obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    change ((Nat.sub (Nat.sub (d + 1) 1) (m % (d + 1)) : ℕ) : ℤ) = _
    simp only [Nat.sub_eq, Nat.add_sub_cancel]
    have hlt : m % (d + 1) < d + 1 := Nat.mod_lt m (Nat.succ_pos d)
    have hdm := Nat.div_add_mod m (d + 1)
    generalize m / (d + 1) = q at hdm
    generalize m % (d + 1) = r at hdm hlt ⊢
    subst hdm
    refine (((Int.ediv_emod_unique (a := Int.negSucc ((d + 1) * q + r))
      (b := ((d + 1 : ℕ) : ℤ)) (r := ((d - r : ℕ) : ℤ)) (q := -(q : ℤ) - 1)
      (by positivity)).2 ⟨?_, by positivity, ?_⟩).2).symm
    · rw [Int.negSucc_eq]
      push_cast [show r ≤ d by omega]
      ring
    · push_cast [show r ≤ d by omega]
      omega

/-- `itoNat a = a.toNat`. -/
theorem itoNat_eq (a : ℤ) : itoNat a = a.toNat := by rcases a with m | m <;> rfl

/-- `iabs a = a.natAbs`. -/
theorem iabs_eq (a : ℤ) : iabs a = a.natAbs := by rcases a with m | m <;> rfl

/-- `ile a b = decide (a ≤ b)`. -/
theorem ile_eq (a b : ℤ) : ile a b = decide (a ≤ b) := by
  unfold ile
  rw [isub_eq]
  rcases h : b - a with m | m
  · have : a ≤ b := by rw [Int.ofNat_eq_natCast] at h; omega
    simp [this]
  · have : ¬ a ≤ b := by rw [Int.negSucc_eq] at h; omega
    simp [this]

/-- `imin a b = min a b`. -/
theorem imin_eq (a b : ℤ) : imin a b = min a b := by
  unfold imin; rw [ile_eq]; by_cases h : a ≤ b <;> simp [h, min_def]

/-- `imax a b = max a b`. -/
theorem imax_eq (a b : ℤ) : imax a b = max a b := by
  unfold imax; rw [ile_eq]; by_cases h : a ≤ b <;> simp [h, max_def]

/-- `nmin a b = min a b`. -/
theorem nmin_eq (a b : ℕ) : nmin a b = min a b := by
  unfold nmin; by_cases h : a ≤ b
  · rw [Nat.ble_eq_true_of_le h]; simp [h]
  · have hb : Nat.ble a b = false := by
      cases hb : Nat.ble a b
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) h
    rw [hb]; simp; omega

/-- `nmax a b = max a b`. -/
theorem nmax_eq (a b : ℕ) : nmax a b = max a b := by
  unfold nmax; by_cases h : a ≤ b
  · rw [Nat.ble_eq_true_of_le h]; simp [h]
  · have hb : Nat.ble a b = false := by
      cases hb : Nat.ble a b
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) h
    rw [hb]; simp; omega

/-- `getR d l k = l.getD k d`. -/
theorem getR_eq {α : Type} (d : α) : ∀ (l : List α) (k : ℕ), getR d l k = l.getD k d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: l, k + 1 => by
    change Bool.rec (motive := fun _ => α) (getR d l (Nat.sub (k + 1) 1)) x (Nat.beq (k + 1) 0) = _
    rw [show Nat.beq (k + 1) 0 = false from rfl,
      show Nat.sub (k + 1) 1 = k from Nat.add_sub_cancel ..]
    exact getR_eq d l k

/-- `dropR n l = l.drop n`. -/
theorem dropR_eq {α : Type} : ∀ (n : ℕ) (l : List α), dropR n l = l.drop n
  | 0, _ => rfl
  | n + 1, [] => by
    change dropR n [] = _
    rw [dropR_eq n []]; simp
  | n + 1, _ :: l => by
    change dropR n l = _
    rw [dropR_eq n l]; rfl

end F

/-! ### The fast checker agrees with the checker -/

/-- `Nat.div a b = a / b`. -/
theorem F.ndiv (a b : ℕ) : Nat.div a b = a / b := rfl

/-- The recursor of `Bool` at `decide p` is `if p then x else y`. -/
theorem F.rec_decide {α : Type} (x y : α) (p : Prop) [Decidable p] :
    Bool.rec (motive := fun _ => α) y x (decide p) = if p then x else y := by
  by_cases h : p <;> simp [h]

/-- The recursor of `Bool` at `Nat.ble a b` is `if a ≤ b then x else y`. -/
theorem F.rec_ble {α : Type} (x y : α) (a b : ℕ) :
    Bool.rec (motive := fun _ => α) y x (Nat.ble a b) = if a ≤ b then x else y := by
  rw [show Nat.ble a b = decide (a ≤ b) from Bool.eq_iff_iff.2 (by simp [Nat.ble_eq])]
  exact F.rec_decide x y _

/-- `F.expI = expI`. -/
theorem expI_fast (Y : ℤ) (n : ℕ) : F.expI Y n = expI Y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change F.expStep Y n (F.expI Y n) = _
    rw [ih, expI]
    rcases expI Y n with ⟨⟨s1, s2⟩, ⟨t1, t2⟩⟩
    simp only [F.expStep, F.iadd_eq, F.imul_eq, F.idiv_eq, F.ineg_eq, Nat.mul_eq,
      Nat.succ_eq_add_one]
    push_cast [F.P, P]
    rfl

/-- `F.rotI = rotI`. -/
theorem rotI_fast (n : ℕ) (z : ℤ × ℤ) : F.rotI n z = rotI n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change F.rotI n (F.ineg z.2, z.1) = _
    rw [ih, F.ineg_eq, rotI]

/-- `F.topN = topN`. -/
theorem topN_fast (num : ℤ) (den : ℕ) : F.topN num den = topN num den := by
  simp only [F.topN, topN, F.idiv_eq, F.iadd_eq, F.imul_eq, Nat.mul_eq, Int.ofNat_eq_natCast]
  push_cast
  ring_nf

/-- `F.topY = topY`. -/
theorem topY_fast (num : ℤ) (den : ℕ) : F.topY num den = topY num den := by
  simp only [F.topY, topY, F.idiv_eq, F.isub_eq, F.imul_eq, topN_fast, Nat.mul_eq,
    Int.ofNat_eq_natCast]
  push_cast [F.P, P]
  ring_nf

/-- `F.topI = topI`. -/
theorem topI_fast (num : ℤ) {den : ℕ} : F.topI num den = topI num den := by
  simp only [F.topI, topI, expI_fast, topY_fast]
  rcases expI (topY num den) 18 with ⟨⟨a, b⟩, _⟩
  simp only [F.idiv_eq, rotI_fast, topN_fast]
  congr 1
  have h := F.imodN_eq (topN num den) (d := 4) (by norm_num)
  omega

/-- `F.gsqI = gsqI`. -/
theorem gsqI_fast (z : ℤ × ℤ) : F.gsqI z = gsqI z := by
  simp only [F.gsqI, gsqI, F.idiv_eq, F.isub_eq, F.imul_eq, Int.ofNat_eq_natCast]
  push_cast [F.P, P]
  ring_nf

/-- `F.errI = errI`. -/
theorem errI_fast (e : ℤ) : F.errI e = errI e := by
  simp only [F.errI, errI, F.idiv_eq, F.isub_eq, F.iadd_eq, F.imul_eq, Int.ofNat_eq_natCast,
    F.Pz, Nat.mul_eq]
  push_cast [F.P, P]
  ring_nf

/-- `F.chainI = chainI`. -/
theorem chainI_fast (n : ℕ) (z : ℤ × ℤ) (e : ℤ) : F.chainI n z e = chainI n z e := by
  induction n generalizing z e with
  | zero => rfl
  | succ n ih =>
    change (z, e) :: F.chainI n (F.gsqI z) (F.errI e) = _
    rw [ih, gsqI_fast, errI_fast, chainI]

/-- `F.sumI = sumI`. -/
theorem sumI_fast (n : ℕ) (l : List ((ℤ × ℤ) × ℤ)) : F.sumI n l = sumI n l := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rcases l with _ | ⟨⟨z, e⟩, l⟩
    · change ((Int.ofNat 0, Int.ofNat 0), Int.ofNat (Nat.mul (Nat.succ n) F.P)) = _
      simp only [sumI, Int.ofNat_eq_natCast, Nat.mul_eq, Nat.succ_eq_add_one]
      push_cast [F.P, P]
      rfl
    · change ((F.iadd z.1 (F.sumI n l).1.1, F.iadd z.2 (F.sumI n l).1.2),
        F.iadd e (F.sumI n l).2) = _
      rw [ih, sumI]
      rcases sumI n l with ⟨⟨a, b⟩, f⟩
      simp only [F.iadd_eq]

/-- `F.sqGuess = sqGuess`. -/
theorem sqGuess_fast (a b : ℤ) : F.sqGuess a b = sqGuess a b := by
  simp only [F.sqGuess, sqGuess, F.nmax_eq, F.nmin_eq, F.iabs_eq, Nat.add_eq, F.ndiv]

/-- `F.newtonUp = newtonUp`. -/
theorem newtonUp_fast (N n q : ℕ) : F.newtonUp N n q = newtonUp N n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    change F.newtonUp N n _ = _
    rw [ih, newtonUp]
    rfl

/-- `F.capI = capI`. -/
theorem capI_fast (t : ℕ) (T : (ℤ × ℤ) × ℤ) (lip : ℤ) : F.capI t T lip = capI t T lip := by
  simp only [F.capI, capI, F.itoNat_eq, F.iadd_eq, F.imul_eq, newtonUp_fast, sqGuess_fast,
    F.rec_ble, Nat.mul_eq]
  split_ifs
  · simp only [F.imin_eq, F.imax_eq, F.idiv_eq, F.isub_eq, F.Pz,
      Int.ofNat_eq_natCast, P]
    push_cast
    ring_nf
  · rfl

/-- `F.lnum = lnum`, as integers. -/
theorem lnum_fast : ∀ c : ℕ, (F.lnum c : ℤ) = lnum c
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl
  | 8 => rfl | 9 => rfl | 10 => rfl | 11 => rfl | 12 => rfl
  | c + 13 => by
    simp [F.lnum, F.getR_eq, lnum]

/-- `F.lipI d r L c = lipI d r L c` for `2 ≤ c`. -/
theorem lipI_fast (d r L : ℕ) {c : ℕ} (hc : 2 ≤ c) : F.lipI d r L c = lipI d r L c := by
  simp only [F.lipI, lipI, Int.ofNat_eq_natCast, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Nat.pow_eq,
    F.ndiv]
  have h1 : 1 ≤ 21 * (c - 1) * 2 ^ (d + L) := by
    have : 1 ≤ c - 1 := by omega
    have : 1 ≤ 2 ^ (d + L) := Nat.one_le_two_pow
    nlinarith
  rw [Int.natCast_div, Nat.cast_sub (by omega)]
  push_cast [Nat.cast_sub (show 1 ≤ c by omega), F.P, P, ← lnum_fast]
  ring_nf

/-- `F.chainsI = chainsI`. -/
theorem chainsI_fast (x : ℤ) (d : ℕ) : F.chainsI x d = chainsI x d := by
  have h : ∀ m r, (Nat.rec (motive := fun _ => ℕ → List (List ((ℤ × ℤ) × ℤ))) (fun _ => [])
      (fun _ ih r => F.chainI 15 (F.topI (F.imul (Int.ofNat (Nat.pow 9 r)) x)
        (Nat.mul 3 (Nat.pow 2 (Nat.add d 17)))) (Int.ofNat 116) :: ih (Nat.succ r)) m r) =
      (List.range' r m).map fun r =>
        chainI 15 (topI (((9 ^ r : ℕ) : ℤ) * x) (3 * 2 ^ (d + 17))) 116 := by
    intro m
    induction m with
    | zero => intro r; rfl
    | succ m ih =>
      intro r
      rw [List.range'_succ, List.map_cons, ← ih]
      change F.chainI 15 _ _ :: _ = _
      rw [chainI_fast, topI_fast, F.imul_eq]
      rfl
  rw [F.chainsI, h, chainsI, List.range_eq_range']


/-- `F.facI = facI`. -/
theorem facI_fast (k d r h c : ℕ) (chs : List (List ((ℤ × ℤ) × ℤ))) :
    F.facI k d r h c chs = facI k d r h c chs := by
  unfold F.facI facI
  have hb : (Nat.ble 3 c && Nat.ble c 12 && Nat.blt r 8 && Nat.ble (Nat.add h c) k &&
      Nat.ble (Nat.add h c) 17) = decide (3 ≤ c ∧ c ≤ 12 ∧ r < 8 ∧ h + c ≤ k ∧ h + c ≤ 17) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.add_eq, decide_eq_true_eq]
    tauto
  rw [hb, F.rec_decide]
  split_ifs with hg
  · rw [capI_fast, sumI_fast, F.dropR_eq, F.getR_eq, lipI_fast _ _ _ (by omega)]
    rfl
  · rfl

/-- `F.whiteI = whiteI`. -/
theorem whiteI_fast (k d r L : ℕ) (x : ℤ) : F.whiteI k d r L x = whiteI k d r L x := by
  unfold F.whiteI whiteI
  simp only [Nat.mul_eq, Nat.pow_eq, Nat.add_eq, Nat.sub_eq, Int.ofNat_eq_natCast, F.imul_eq]
  generalize hT : 2 ^ (d + L) = T
  generalize hN : 9 ^ r = N
  have hT0 : 0 < T := by rw [← hT]; positivity
  have hρ := F.imodN_eq ((N : ℤ) * x) (d := 3 * T) (by omega)
  have hlt := Int.emod_lt_of_pos ((N : ℤ) * x) (b := ((3 * T : ℕ) : ℤ)) (by positivity)
  rw [← hρ] at hlt
  generalize F.imodN ((N : ℤ) * x) (3 * T) = ρ at hρ hlt ⊢
  rw [← hρ, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, decide_eq_true_eq, F.nmin_eq]
  push_cast at hlt ⊢
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> omega

/-- `F.edgeI = edgeI`. -/
theorem edgeI_fast (k d r h c : ℕ) (x : ℤ) : F.edgeI k d r h c x = edgeI k d r h c x := by
  unfold F.edgeI edgeI
  rw [Nat.add_eq, whiteI_fast]
  cases whiteI k d r (h + c) x <;> rw [Bool.eq_iff_iff] <;>
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.ble_eq, decide_eq_true_eq,
      Bool.or_eq_false_iff, Bool.or_false, Bool.or_true, Bool.and_true]
  exact Iff.rfl


/-- `F.mulUp = mulUp`. -/
theorem mulUp_fast (f g : ℤ) : F.mulUp f g = mulUp f g := by
  simp only [F.mulUp, mulUp, F.idiv_eq, F.isub_eq, F.iadd_eq, F.imul_eq, F.Qz, F.Q, Q,
    Int.ofNat_eq_natCast]
  push_cast
  ring_nf

/-- `F.cutoff = trZeroCutoff`. -/
theorem cutoff_fast (h : ℕ) : F.cutoff h = trZeroCutoff h := by
  rw [F.cutoff, F.rec_ble, F.nmin_eq, Nat.sub_eq]
  rfl

/-- For `2 ≤ c₀`, `F.stateSum` is the sum over `c ∈ [c₀, c₀ + m)` of the terms of `stateI`. -/
theorem stateSum_fast (k d : ℕ) (x : ℤ) (chs : List (List ((ℤ × ℤ) × ℤ))) (next : List ℤ)
    (r h : ℕ) : ∀ (m c₀ : ℕ), 2 ≤ c₀ → F.stateSum k d x chs next r h m c₀ =
      ((List.range' c₀ m).map fun c : ℕ => wq c * (P - mulUp (facI k d r h c chs)
        (if edgeI k d r h c x then next.getD (h + c) Q else Q))).sum
  | 0, _, _ => rfl
  | m + 1, c₀, hc => by
    change F.iadd _ (F.stateSum k d x chs next r h m (Nat.succ c₀)) = _
    rw [stateSum_fast k d x chs next r h m (Nat.succ c₀) (by omega), List.range'_succ,
      List.map_cons, List.sum_cons, F.iadd_eq, F.imul_eq, F.isub_eq, mulUp_fast, facI_fast,
      edgeI_fast, F.getR_eq]
    have hw : ((F.wq c₀ : ℕ) : ℤ) = wq c₀ := by
      simp only [F.wq, wq, Nat.mul_eq, Nat.sub_eq, Nat.pow_eq]
      push_cast [Nat.cast_sub (show 1 ≤ c₀ by omega)]
      ring
    have hG : Bool.rec (motive := fun _ => ℤ) F.Qz (next.getD (Nat.add h c₀) F.Qz)
        (edgeI k d r h c₀ x) = if edgeI k d r h c₀ x then next.getD (h + c₀) Q else Q := by
      cases edgeI k d r h c₀ x <;> rfl
    rw [← hw, hG]
    rfl

/-- `F.stateI = stateI`. -/
theorem stateI_fast (k d : ℕ) (x : ℤ) (chs : List (List ((ℤ × ℤ) × ℤ))) (next : List ℤ)
    (r h : ℕ) : F.stateI k d x chs next r h = stateI k d x chs next r h := by
  rw [F.stateI, stateSum_fast _ _ _ _ _ _ _ _ _ le_rfl, F.isub_eq, cutoff_fast, Nat.sub_eq,
    stateI]
  rfl

/-- `F.live = live`. -/
theorem live_fast (r h : ℕ) : F.live r h = live r h := by
  unfold F.live live
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, beq_iff_eq, Nat.ble_eq,
    decide_eq_true_eq, Nat.mul_eq]

/-- `F.rowI = rowI`. -/
theorem rowI_fast (k d : ℕ) (x : ℤ) (chs : List (List ((ℤ × ℤ) × ℤ))) (next : List ℤ) (r : ℕ) :
    F.rowI k d x chs next r = rowI k d x chs next r := by
  have h : ∀ m h₀, (Nat.rec (motive := fun _ => ℕ → List ℤ) (fun _ => [])
      (fun _ ih h => Bool.rec (motive := fun _ => ℤ) F.Qz (F.stateI k d x chs next r h)
        (F.live r h) :: ih (Nat.succ h)) m h₀) =
      (List.range' h₀ m).map fun h => if live r h then stateI k d x chs next r h else Q := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro h₀
      rw [List.range'_succ, List.map_cons, ← ih]
      change Bool.rec (motive := fun _ => ℤ) F.Qz (F.stateI k d x chs next r h₀) (F.live r h₀) ::
        _ = _
      rw [live_fast, stateI_fast]
      cases live r h₀ <;> rfl
  rw [F.rowI, h, rowI, List.range_eq_range']

/-- `F.forceRow l f = f l`. -/
theorem forceRow_fast {β : Type} (l : List ℤ) (f : List ℤ → β) : F.forceRow l f = f l := by
  induction l generalizing f with
  | nil => rfl
  | cons v l ih =>
    rcases v with n | n
    · change F.forceRow l (fun l' => f (Int.ofNat n :: l')) = _
      rw [ih]
    · change F.forceRow l (fun l' => f (Int.negSucc n :: l')) = _
      rw [ih]

/-- `F.rowsI = rowsI`. -/
theorem rowsI_fast (k d : ℕ) (x : ℤ) (chs : List (List ((ℤ × ℤ) × ℤ))) (n : ℕ)
    (next : List ℤ) : F.rowsI k d x chs n next = rowsI k d x chs n next := by
  induction n generalizing next with
  | zero => exact F.getR_eq _ _ _
  | succ n ih =>
    change F.forceRow (F.rowI k d x chs next n) (F.rowsI k d x chs n) = _
    rw [forceRow_fast, ih, rowI_fast, rowsI, forceRow_eq]

/-- `F.cellV = cellV`. -/
theorem cellV_fast (k d : ℕ) (x : ℤ) : F.cellV k d x = cellV k d x := by
  rw [F.cellV, chainsI_fast, rowsI_fast, cellV]
  rfl

/-- `F.cellOK k d x` decides `cellV k d x · 1310720000 < 1009374100 · Q`. -/
theorem cellOK_fast (k d : ℕ) (x : ℤ) :
    F.cellOK k d x = decide (cellV k d x * 1310720000 < 1009374100 * Q) := by
  rw [F.cellOK, cellV_fast]
  rcases cellV k d x with v | v
  · change Nat.blt (Nat.mul v 1310720000) (Nat.mul 1009374100 F.Q) = _
    rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_eq, Q, F.Q, Nat.mul_eq, Nat.mul_eq]
    simp only [Int.ofNat_eq_natCast]
    omega
  · change true = _
    rw [eq_comm, decide_eq_true_eq, Int.negSucc_eq, Q]
    omega

/-- The check of a cell: the cost bound is below `77/100 + T^{root}_{0,12}`, where
`T^{root}_{0,12} = 1197/13107200`; evaluated with the fast copy `F.cellOK` (`cellOK_fast`). -/
noncomputable def cellOK (k d : ℕ) (x : ℤ) : Bool := F.cellOK k d x

/-- `1009374100 / 1310720000 = 77/100 + 1197/13107200`. -/
theorem bound_eq : (1009374100 / 1310720000 : ℝ) = 77 / 100 + 1197 / 13107200 := by norm_num

/-- If the check of the cell with numerator `3 · 2^d · res + p` passes, then for every `β`
within `1 / (3 · 2^d)` of `p / (3 · 2^d)` the tree cost at `res + 2^k n + β` is below
`1009374100 / 1310720000`. -/
theorem cell_spec {k d : ℕ} {res n p : ℤ} {β : ℝ} (hβ : |β - p / (3 * 2 ^ d)| ≤ 1 / (3 * 2 ^ d))
    (h : cellOK k d (3 * (2 ^ d : ℕ) * res + p) = true) :
    trTreeCost trZeroCutoff (trWhitePolicy 0 12 14 (res + 2 ^ k * n) ((p - 1) / (3 * 2 ^ d))
      ((p + 1) / (3 * 2 ^ d))) 0 0 (((res + 2 ^ k * n : ℤ) : ℝ) + β) <
        1009374100 / 1310720000 := by
  have hb := trTreeCost_le_rowsI (X := ((res + 2 ^ k * n : ℤ) : ℝ) + β) (k := k) (d := d)
    (x := 3 * (2 ^ d : ℕ) * res + p) (chs := chainsI (3 * (2 ^ d : ℕ) * res + p) d)
    (trZeroDatum (res + 2 ^ k * n) ((p - 1) / (3 * 2 ^ d)) ((p + 1) / (3 * 2 ^ d))).isBoundedPolicy
    (fun r h c hc2 hc => trTreeFactor_le_facI (k := k) (n := n) hc hc2 hβ)
    (fun r h c he => mem_trWhitePolicy_of_edgeI (n := n) he) 8 (rowBound_replicate 8)
  change _ ≤ (cellV k d (3 * (2 ^ d : ℕ) * res + p) : ℝ) / 2 ^ 72 at hb
  have h' : cellV k d (3 * (2 ^ d : ℕ) * res + p) * 1310720000 < 1009374100 * Q :=
    of_decide_eq_true ((cellOK_fast _ _ _).symm.trans h)
  generalize cellV k d (3 * (2 ^ d : ℕ) * res + p) = V at h' hb
  refine hb.trans_lt ?_
  have h'' : ((V * 1310720000 : ℤ) : ℝ) < ((1009374100 * Q : ℤ) : ℝ) := by exact_mod_cast h'
  push_cast [cast_Q] at h''
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- A cover of an interval of `β` by bisection. -/
inductive BT
  /-- An accepted interval. -/
  | leaf
  /-- The two halves of the interval. -/
  | node (l r : BT)

/-- A cover of a residue class modulo `2^k`. -/
inductive RT
  /-- A cover of `[-1/3, 1/3]` for the residue class. -/
  | beta (b : BT)
  /-- The classes `r` and `r + 2^k` modulo `2^{k+1}`. -/
  | split (l r : RT)
  /-- A residue class without elements in `(0, 2^16)`. -/
  | none

/-- The check of a cover of the interval `[(p - 1) / (3 · 2^d), (p + 1) / (3 · 2^d)]` of `β`,
for the residue `res` modulo `2^k`. -/
noncomputable def checkB (k : ℕ) (res : ℤ) : ℕ → ℤ → BT → Bool
  | d, p, .leaf => cellOK k d (3 * (2 ^ d : ℕ) * res + p)
  | d, p, .node l r => checkB k res (d + 1) (2 * p - 1) l && checkB k res (d + 1) (2 * p + 1) r

/-- The check of a cover of the residue class of `res` modulo `2^k`. -/
noncomputable def checkR : ℕ → ℤ → RT → Bool
  | k, res, .beta b => checkB k res 0 0 b
  | k, res, .split l r => checkR (k + 1) res l && checkR (k + 1) (res + (2 ^ k : ℕ)) r
  | k, res, .none => decide (16 ≤ k ∧ 2 ^ 16 ≤ res ∧ res < 2 ^ k)

/-- The conclusion of the certificate for the integers `m = res + 2^k n` with `0 < m < 2^16`. -/
def Good (k : ℕ) (res : ℤ) : Prop :=
  ∀ n : ℤ, 0 < res + 2 ^ k * n → res + 2 ^ k * n < 2 ^ 16 → ∀ β : ℝ, |β| ≤ 1 / 3 →
    ∃ a b : ℝ, -(1 / 3) ≤ a ∧ a ≤ β ∧ β ≤ b ∧ b ≤ 1 / 3 ∧
      trTreeCost trZeroCutoff (trWhitePolicy 0 12 14 (res + 2 ^ k * n) a b) 0 0
        (((res + 2 ^ k * n : ℤ) : ℝ) + β) < 1009374100 / 1310720000

/-- If the check of a cover of `[(p - 1) / (3 · 2^d), (p + 1) / (3 · 2^d)]` passes, then every
`β` in that interval lies in a subinterval `[a, b]` on which the tree cost at `res + 2^k n + β`
is below `1009374100 / 1310720000`. -/
theorem checkB_spec (k : ℕ) (res : ℤ) (t : BT) (d : ℕ) (p : ℤ) (h : checkB k res d p t = true)
    (n : ℤ) (β : ℝ) (h1 : (p - 1) / (3 * 2 ^ d) ≤ β) (h2 : β ≤ (p + 1) / (3 * 2 ^ d)) :
    ∃ a b : ℝ, (p - 1) / (3 * 2 ^ d) ≤ a ∧ a ≤ β ∧ β ≤ b ∧ b ≤ (p + 1) / (3 * 2 ^ d) ∧
      trTreeCost trZeroCutoff (trWhitePolicy 0 12 14 (res + 2 ^ k * n) a b) 0 0
        (((res + 2 ^ k * n : ℤ) : ℝ) + β) < 1009374100 / 1310720000 := by
  induction t generalizing d p with
  | leaf =>
    rw [checkB] at h
    have hβ : |β - p / (3 * 2 ^ d)| ≤ 1 / (3 * 2 ^ d) := by
      rw [abs_le]
      rw [sub_div] at h1
      rw [add_div] at h2
      constructor <;> linarith
    exact ⟨_, _, le_rfl, h1, h2, le_rfl, cell_spec hβ h⟩
  | node l r ihl ihr =>
    simp only [checkB, Bool.and_eq_true] at h
    have e1 : (((2 * p - 1 : ℤ) : ℝ) - 1) / (3 * 2 ^ (d + 1)) = (p - 1) / (3 * 2 ^ d) := by
      push_cast; rw [pow_succ]; field_simp; ring
    have e2 : (((2 * p - 1 : ℤ) : ℝ) + 1) / (3 * 2 ^ (d + 1)) = p / (3 * 2 ^ d) := by
      push_cast; rw [pow_succ]; field_simp; ring
    have e3 : (((2 * p + 1 : ℤ) : ℝ) - 1) / (3 * 2 ^ (d + 1)) = p / (3 * 2 ^ d) := by
      push_cast; rw [pow_succ]; field_simp; ring
    have e4 : (((2 * p + 1 : ℤ) : ℝ) + 1) / (3 * 2 ^ (d + 1)) = (p + 1) / (3 * 2 ^ d) := by
      push_cast; rw [pow_succ]; field_simp; ring
    have hp : (p - 1 : ℝ) / (3 * 2 ^ d) ≤ p / (3 * 2 ^ d) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hp' : (p : ℝ) / (3 * 2 ^ d) ≤ (p + 1) / (3 * 2 ^ d) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    rcases le_total β (p / (3 * 2 ^ d)) with hm | hm
    · obtain ⟨a, b, ha, hab, hb, hb', hc⟩ := ihl (d + 1) (2 * p - 1) h.1 (e1 ▸ h1) (e2 ▸ hm)
      exact ⟨a, b, e1 ▸ ha, hab, hb, (e2 ▸ hb').trans hp', hc⟩
    · obtain ⟨a, b, ha, hab, hb, hb', hc⟩ := ihr (d + 1) (2 * p + 1) h.2 (e3 ▸ hm) (e4 ▸ h2)
      exact ⟨a, b, hp.trans (e3 ▸ ha), hab, hb, e4 ▸ hb', hc⟩

/-- `Good k res` follows from `Good (k + 1) res` and `Good (k + 1) (res + 2^k)`. -/
theorem Good.split {k k' : ℕ} {res res' : ℤ} (hk : k' = k + 1) (hr : res' = res + 2 ^ k)
    (h0 : Good k' res) (h1 : Good k' res') : Good k res := by
  subst hk hr
  intro n
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · have e : res + 2 ^ k * (2 * m) = res + 2 ^ (k + 1) * m := by ring
    rw [e]
    exact h0 m
  · have e : res + 2 ^ k * (2 * m + 1) = (res + 2 ^ k) + 2 ^ (k + 1) * m := by ring
    rw [e]
    exact h1 m

/-- An accepted cover of the residue class of `res` modulo `2^k` proves `Good k res`. -/
theorem good_of_checkR (t : RT) (k : ℕ) (res : ℤ) (h : checkR k res t = true) :
    Good k res := by
  induction t generalizing k res with
  | beta b =>
    intro n _ _ β hβ
    obtain ⟨hβ1, hβ2⟩ := abs_le.mp hβ
    obtain ⟨a, b, ha, hab, hb, hb', hc⟩ :=
      checkB_spec k res b 0 0 h n β (by norm_num; linarith) (by norm_num; linarith)
    exact ⟨a, b, by norm_num at ha; linarith, hab, hb, by norm_num at hb'; linarith, hc⟩
  | split l r ihl ihr =>
    simp only [checkR, Bool.and_eq_true] at h
    exact Good.split rfl (by push_cast; ring) (ihl _ _ h.1) (ihr _ _ h.2)
  | none =>
    simp only [checkR, decide_eq_true_eq] at h
    obtain ⟨hk, h1, h2⟩ := h
    intro n hpos hlt
    exfalso
    have hk' : (2 : ℤ) ^ 16 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    rcases le_or_gt 0 n with hn | hn
    · nlinarith [pow_pos (by norm_num : (0 : ℤ) < 2) k]
    · nlinarith [pow_pos (by norm_num : (0 : ℤ) < 2) k]

end TrTreeCertificate

end CollatzPosDens
