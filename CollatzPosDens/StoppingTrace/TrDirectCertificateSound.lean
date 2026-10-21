/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDirectCertificateCheck
public import CollatzPosDens.StoppingTrace.TrTreeCost
public import CollatzPosDens.StoppingTrace.TrTreeCostLipschitz
public import CollatzPosDens.StoppingTrace.TrTreeCostNodeBound
public import CollatzPosDens.StoppingTrace.TrTailGain
public import CollatzPosDens.StoppingTrace.TrWhitePolicy
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.BigOperators.Field

/-!
# The checker of the direct-entry certificate

Fix `ω, p` and put `H = ω + p`. The cell `(D, k)` is the interval `[a, b]` with
`a = (2k - 2^D) / (3 · 2^D)` and `b = (2k + 2 - 2^D) / (3 · 2^D)`; for a natural number `m ≥ 1` the
point `2^ω m + (a + b)/2` is `X / X_D` with `X = 3 · 2^{D+ω} m + 2k + 1 - 2^D` and `X_D = 3 · 2^D`.
Let `W` be the white-test policy `W^{ω,8,H}_{m,a,b}` and `F_{r,h} = F^{8,W}_{r,h}(X / X_D)`.

Since `∑_{c=2}^{8} ϖ(c) = 247/256`, the recursion of the tree cost reads
`F_{r,h} = 9/256 + ∑_{c=2}^{8} ϖ(c) ψ_c G_c`, with `ψ_c` the capped factor at
`θ_{h+c} = 9^r X / (X_D 2^{h+c})` and `G_c = F_{r+1,h+c}` if `(r, h, c) ∈ W` and `G_c = 1`
otherwise. As all terms are nonnegative, upper bounds for the `ψ_c` (the entries of
`CollatzPosDens.TrDirectCertificate.mkEntry`) and for the `G_c` give an upper bound for
`F_{r,h}`, rounded up on the scale `2^64` (`CollatzPosDens.TrDirectCertificate.nodeB`). The
bounds for all states are computed row by row, a row being a level `r`
(`CollatzPosDens.TrDirectCertificate.rowsGo`). Together with the Lipschitz bound for `F_{0,0}`
on the cell and the Lipschitz constant of the policy of all triples, which contains `W`, this
gives the acceptance test `CollatzPosDens.TrDirectCertificate.leafB` of a cell.

The entries at `θ_n` depend on `X` modulo `X_D 2^n`, hence on `m` modulo `2^{n-ω}`. The check
`CollatzPosDens.TrDirectCertificate.cellCheck` of a cell for a list of values of `m` computes the
entries level by level, splitting the list by the next bit of `m` whenever the level exceeds
`ω`, so that the entries of a level are computed once for each residue class.

## Main definitions

* `CollatzPosDens.TrDirectCertificate.cellCheck`: the check of a cell for a list of values of
  `m`.
* `CollatzPosDens.TrDirectCertificate.Shape`: bisection shapes of `[-1/3, 1/3]`.
* `CollatzPosDens.TrDirectCertificate.allPolicy`: the policy of all triples `(r, h, c)` with
  `2 ≤ c ≤ 8` and `h + c ≤ H`.

## Main results

* `CollatzPosDens.TrDirectCertificate.trTreeCost_le_nodeB`: the bound at one state.
* `CollatzPosDens.trTreeLip_mono`: the Lipschitz constant of a tree cost is monotone in the
  policy.
* `CollatzPosDens.TrDirectCertificate.trTreeLip_allPolicy_le`: a bound for the Lipschitz
  constant of the policy of all triples.
* `CollatzPosDens.TrDirectCertificate.cellGood_of_cellCheck`: soundness of the check of a cell.
* `CollatzPosDens.TrDirectCertificate.exists_of_cellGood`: from good cells to the bound of the
  direct-entry certificate.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrDirectCertificate

/-- `condR b x y` is `cond b x y`, written as the bare recursor application `Bool.rec y x b`, which
the kernel reduces in one step (`cond`, a definition by pattern matching, takes several). -/
local macro "condR " b:term:max x:term:max y:term:max : term =>
  `(Bool.rec (motive := fun _ => _) $y $x $b)

/-- The numerator `X = 3 · 2^{D+ω} m + 2k + 1 - 2^D` of `2^ω m + u`, `u` the centre of the cell
`(D, k)`, over `X_D = 3 · 2^D`. -/
def cellX (ω D k m : ℕ) : ℕ :=
  Nat.sub (Nat.add (Nat.mul (Nat.mul 3 (Nat.pow 2 (Nat.add D ω))) m) (Nat.add (Nat.mul 2 k) 1))
    (Nat.pow 2 D)

/-! ### The combination at a state -/

/-- `⌈x / d⌉`, written `⌊(x + d₁) / d⌋` with `d₁ = d - 1`. -/
def ceilDiv (x d₁ d : ℕ) : ℕ := Nat.div (Nat.add x d₁) d

/-- The bound at a state `(r, h)` from the bounds `g_c` at its children `(r + 1, h + c)` and
the entries `e_c` at `θ_{h+c}`. -/
def nodeB (ω H h : ℕ) (g8 g7 g6 g5 g4 g3 g2 : ℕ) (e8 e7 e6 e5 e4 e3 : Entry) : ℕ :=
  let G2 := condR (Nat.ble (Nat.add h 2) H) g2 one
  let G3 := condR (Nat.ble (Nat.add h 3) H) g3 one
  let G4 := condR (and (Nat.ble (Nat.add h 4) H) (or (Nat.ble (Nat.add h 4) ω) e4.wh)) g4 one
  let G5 := condR (and (Nat.ble (Nat.add h 5) H) (or (Nat.ble (Nat.add h 5) ω) e5.wh)) g5 one
  let G6 := condR (Nat.ble (Nat.add h 6) H) g6 one
  let G7 := condR (Nat.ble (Nat.add h 7) H) g7 one
  let G8 := condR (Nat.ble (Nat.add h 8) H) g8 one
  Nat.add (Nat.add (Nat.add (Nat.add 648518346341351424 (ceilDiv G2 3 4))
      (Nat.add (ceilDiv (Nat.mul (Nat.mul 2 e3.c3) G3) 147573952589676412927
          147573952589676412928)
        (ceilDiv (Nat.mul (Nat.mul 3 e4.c4) G4) 295147905179352825855 295147905179352825856)))
    (Nat.add (ceilDiv (Nat.mul (Nat.mul 4 e5.c5) G5) 590295810358705651711 590295810358705651712)
      (ceilDiv (Nat.mul (Nat.mul 5 e6.c6) G6) 1180591620717411303423 1180591620717411303424)))
    (Nat.add (ceilDiv (Nat.mul (Nat.mul 6 e7.c7) G7) 2361183241434822606847
        2361183241434822606848)
      (ceilDiv (Nat.mul (Nat.mul 7 e8.c8) G8) 4722366482869645213695 4722366482869645213696))

/-- The bounds at the states `(r, h), (r, h - 1), …` from the window `g8, …, g2, gs` of the
bounds `[g(h+8), g(h+7), …]` at `r + 1` and the window `e8, …, e3, es` of the entries
`[e(h+8), e(h+7), …]`, for `f` steps or until a list runs out. The windows are carried as
arguments and the recursion is the bare recursor on `f`, which the kernel reduces in one step. -/
def rowGoW (ω H : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ →
    Entry → Entry → Entry → Entry → Entry → Entry → List Entry → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ →
    Entry → Entry → Entry → Entry → Entry → Entry → List Entry → List ℕ)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => [])
    (fun _ ih h g8 g7 g6 g5 g4 g3 g2 gs e8 e7 e6 e5 e4 e3 es =>
      nodeB ω H h g8 g7 g6 g5 g4 g3 g2 e8 e7 e6 e5 e4 e3 ::
        List.rec (motive := fun _ => List ℕ) []
          (fun g gs' _ => List.rec (motive := fun _ => List ℕ) []
            (fun e es' _ => ih (Nat.sub h 1) g7 g6 g5 g4 g3 g2 g gs' e7 e6 e5 e4 e3 e es') es)
          gs) f

/-- The bounds at the states `(r, h), (r, h - 1), …` (for `f` states) from the window
`[g(h+8), g(h+7), …]` of the bounds at `r + 1` and the window `[e(h+8), e(h+7), …]` of the
entries. -/
def rowGo (ω H f h : ℕ) (winG : List ℕ) (winE : List Entry) : List ℕ :=
  match winG, winE with
  | g8 :: g7 :: g6 :: g5 :: g4 :: g3 :: g2 :: gs, e8 :: e7 :: e6 :: e5 :: e4 :: e3 :: es =>
    rowGoW ω H f h g8 g7 g6 g5 g4 g3 g2 gs e8 e7 e6 e5 e4 e3 es
  | _, _ => []

/-- One step of `rowGoW`: the bound at `(r, h)` followed by the bounds from the windows shifted
by one. -/
theorem rowGoW_succ (ω H f h : ℕ) (g8 g7 g6 g5 g4 g3 g2 : ℕ) (gs : List ℕ)
    (e8 e7 e6 e5 e4 e3 : Entry) (es : List Entry) :
    rowGoW ω H (f + 1) h g8 g7 g6 g5 g4 g3 g2 gs e8 e7 e6 e5 e4 e3 es =
      nodeB ω H h g8 g7 g6 g5 g4 g3 g2 e8 e7 e6 e5 e4 e3 ::
        rowGo ω H f (h - 1) (g7 :: g6 :: g5 :: g4 :: g3 :: g2 :: gs)
          (e7 :: e6 :: e5 :: e4 :: e3 :: es) := by
  rcases gs with _ | ⟨g, gs⟩ <;> rcases es with _ | ⟨e, es⟩ <;> rfl

/-- The bounds `[g(H+8), …, g(0)]` at the level of the first entry list, the lists being the
entries `[e(H+8), …, e(0)]` at the levels `r, r + 1, …`. -/
def rowsGo (ω H : ℕ) : List (List Entry) → List ℕ
  | [] => List.replicate (H + 9) one
  | l :: ls => List.replicate 8 one ++ rowGo ω H (H + 1) H (rowsGo ω H ls) l

/-- The acceptance test of a cell: `100 T_D (X_D F + L) < 2^64 X_D (77 T_D + 100 T_N)`. -/
def leafB (ω H TN TD LU XD : ℕ) (acc : List (List Entry)) : Bool :=
  Nat.blt (Nat.mul (Nat.mul 100 TD) (Nat.add (Nat.mul XD ((rowsGo ω H acc).getD (H + 8) one)) LU))
    (Nat.mul (Nat.mul one XD) (Nat.add (Nat.mul 77 TD) (Nat.mul 100 TN)))


/-! ### The residue recursion -/

/-- Adds the entries at level `n` to the entry lists of the levels `r, r + 1, …`. -/
def addLevel (X XD n : ℕ) : ℕ → List (List Entry) → List (List Entry)
  | _, [] => []
  | r, L :: Ls => (mkEntry X XD r n (L.headD Entry.zero) :: L) :: addLevel X XD n (r + 1) Ls

/-- The residue recursion: the entries of level `n` depend on `m` modulo `2^{n-ω}`, so they are
computed once for all `m` of a residue class, which is split by the next bit `j` of `m` when
`n > ω`. -/
def resCheck (ω H TN TD LU D k : ℕ) : ℕ → ℕ → ℕ → List ℕ → List (List Entry) → Bool
  | 0, _, _, _, acc => leafB ω H TN TD LU (Nat.mul 3 (Nat.pow 2 D)) acc
  | f + 1, n, j, ms, acc =>
    cond (Nat.ble n ω)
      (resCheck ω H TN TD LU D k f (n + 1) j ms
        (addLevel (cellX ω D k (ms.headD 1)) (Nat.mul 3 (Nat.pow 2 D)) n 0 acc))
      (let ms0 := ms.filter fun m => Nat.beq (Nat.mod (Nat.div m (Nat.pow 2 j)) 2) 0
       let ms1 := ms.filter fun m => Nat.beq (Nat.mod (Nat.div m (Nat.pow 2 j)) 2) 1
       and (or ms0.isEmpty (resCheck ω H TN TD LU D k f (n + 1) (j + 1) ms0
          (addLevel (cellX ω D k (ms0.headD 1)) (Nat.mul 3 (Nat.pow 2 D)) n 0 acc)))
        (or ms1.isEmpty (resCheck ω H TN TD LU D k f (n + 1) (j + 1) ms1
          (addLevel (cellX ω D k (ms1.headD 1)) (Nat.mul 3 (Nat.pow 2 D)) n 0 acc))))

/-- The check of the cell `(D, k)` for every `m` in the list `ms`. -/
def cellCheck (ω p TN TD LU D k : ℕ) (ms : List ℕ) : Bool :=
  resCheck ω (ω + p) TN TD LU D k (ω + p + 9) 0 0 ms (List.replicate ((ω + p) / 2 + 1) [])


/-! ### Covers -/

/-- A bisection shape: a cell is either accepted, or split into its two halves. -/
inductive Shape where
  /-- the cell is accepted -/
  | leaf
  /-- the cell is split into its two halves -/
  | node (l r : Shape)
  deriving DecidableEq

/-- The accepted cells `(D', k')` of a shape rooted at the cell `(D, k)`. -/
def Shape.leaves : Shape → ℕ → ℕ → List (ℕ × ℕ)
  | .leaf, D, k => [(D, k)]
  | .node l r, D, k => l.leaves (D + 1) (2 * k) ++ r.leaves (D + 1) (2 * k + 1)

/-- Whether the cell `q` is an accepted cell of the shape rooted at `(D, k)`. -/
def Shape.hasLeaf : Shape → ℕ → ℕ → ℕ × ℕ → Bool
  | .leaf, D, k, q => and (Nat.beq D q.1) (Nat.beq k q.2)
  | .node l r, D, k, q => or (l.hasLeaf (D + 1) (2 * k) q) (r.hasLeaf (D + 1) (2 * k + 1) q)

/-- The shape listed for `m` in `exc`, if any, by a recursion on the list that the kernel reduces
in one step per entry. -/
def lookupShape (m : ℕ) (l : List (ℕ × Shape)) : Option Shape :=
  List.rec (motive := fun _ => Option Shape) none
    (fun e _ ih => Bool.rec (motive := fun _ => Option Shape) ih (some e.2) (Nat.beq e.1 m)) l

/-- The shape of `m`: the shape listed for `m` in `exc`, and `dflt` otherwise. -/
def shapeOf (dflt : Shape) (exc : List (ℕ × Shape)) (m : ℕ) : Shape :=
  (lookupShape m exc).getD dflt

/-- A list containing every `m < 2^{p+8}` with `m ≡ ρ (mod 2^a)` whose shape has the accepted
cell `q`: the residue class filtered by the shape if `q` is a cell of the default shape, and
otherwise the listed values whose shape has the cell `q`. -/
def mList (p a ρ : ℕ) (q : ℕ × ℕ) (dflt : Shape) (exc : List (ℕ × Shape)) : List ℕ :=
  cond (dflt.hasLeaf 0 0 q)
    (((List.range (2 ^ (p + 8 - a))).map fun i => ρ + 2 ^ a * i).filter fun m =>
      (shapeOf dflt exc m).hasLeaf 0 0 q)
    (((exc.filter fun e => e.2.hasLeaf 0 0 q).map Prod.fst).filter fun m => Nat.ble 1 m)

/-! ### Cells and the white test -/

open Real Finset

/-- The left endpoint `(2k - 2^D) / (3 · 2^D)` of the cell `(D, k)`. -/
noncomputable def cellLo (D k : ℕ) : ℝ := (2 * k - 2 ^ D) / (3 * 2 ^ D)

/-- The right endpoint `(2k + 2 - 2^D) / (3 · 2^D)` of the cell `(D, k)`. -/
noncomputable def cellHi (D k : ℕ) : ℝ := (2 * k + 2 - 2 ^ D) / (3 * 2 ^ D)

/-- For `m ≥ 1`, the cast of `cellX ω D k m` is `3 · 2^{D+ω} m + 2k + 1 - 2^D`. -/
theorem cellX_cast {ω D k m : ℕ} (hm : 1 ≤ m) :
    (cellX ω D k m : ℝ) = 3 * 2 ^ (D + ω) * m + (2 * k + 1) - 2 ^ D := by
  have h : 2 ^ D ≤ 3 * 2 ^ (D + ω) * m + (2 * k + 1) := by
    have h1 : 2 ^ D ≤ 2 ^ (D + ω) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (D + ω) ≤ 2 ^ (D + ω) * (3 * m) := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : 2 ^ (D + ω) * (3 * m) = 3 * 2 ^ (D + ω) * m := by ring
    omega
  simp only [cellX, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq]
  rw [Nat.cast_sub h]
  push_cast
  ring

/-- For `m ≥ 1`, the point `2^ω m + (a + b)/2`, with `[a, b]` the cell `(D, k)`, is
`cellX ω D k m / (3 · 2^D)`. -/
theorem cell_center {ω D k m : ℕ} (hm : 1 ≤ m) :
    (2 : ℝ) ^ ω * m + (cellLo D k + cellHi D k) / 2 = (cellX ω D k m : ℝ) / (3 * 2 ^ D : ℕ) := by
  rw [cellX_cast hm, cellLo, cellHi]
  push_cast
  rw [pow_add]
  field_simp
  ring

/-- The cell `(D, k)` has width `2 / (3 · 2^D)`. -/
theorem cell_width (D k : ℕ) : cellHi D k - cellLo D k = 2 / (3 * 2 ^ D) := by
  rw [cellLo, cellHi]
  field_simp
  ring

/-- The white test of `whiteB` is the white test of `CollatzPosDens.trWhitePolicy` at the point
`Y / Q`, with the radius `z / Q`. -/
theorem whiteB_iff (Y Q z : ℕ) (hQ : 0 < Q) :
    whiteB Y Q z = true ↔
      (epsStar : ℝ) < |(Y : ℝ) / Q - round ((Y : ℝ) / Q)| - (z : ℝ) / Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [whiteB_eq, decide_eq_true_iff, abs_sub_round_div_natCast_eq, epsStar_cast, ← sub_div,
    lt_div_iff₀ hQ']
  set M := min (Y % Q) (Q - Y % Q)
  constructor
  · intro h
    have : ((37037 * Q + 1000000 * z : ℕ) : ℝ) < ((1000000 * M : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  · intro h
    have : ((37037 * Q + 1000000 * z : ℕ) : ℝ) < ((1000000 * M : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this

/-- Membership in the white-test policy of a cell. -/
theorem mem_cellPolicy_iff {ω H D k m r h c : ℕ} (hm : 1 ≤ m) :
    (r, h, c) ∈ trWhitePolicy ω 8 (H : ℕ) (m : ℤ) (cellLo D k) (cellHi D k) ↔
      2 ≤ c ∧ c ≤ 8 ∧ h + c ≤ H ∧ (c ∉ ({4, 5} : Set ℕ) ∨ h + c ≤ ω ∨
        whiteB (9 ^ r * cellX ω D k m) (3 * 2 ^ D * 2 ^ (h + c)) (9 ^ r) = true) := by
  rw [mem_trWhitePolicy, whiteB_iff _ _ _ (by positivity)]
  have hy : (9 : ℝ) ^ r * (2 ^ ω * ((m : ℤ) : ℝ) + (cellLo D k + cellHi D k) / 2) / 2 ^ (h + c) =
      ((9 ^ r * cellX ω D k m : ℕ) : ℝ) / ((3 * 2 ^ D * 2 ^ (h + c) : ℕ) : ℝ) := by
    rw [Int.cast_natCast, cell_center hm]
    push_cast
    field_simp
  have hz : (9 : ℝ) ^ r * (cellHi D k - cellLo D k) / 2 ^ (h + c + 1) =
      ((9 ^ r : ℕ) : ℝ) / ((3 * 2 ^ D * 2 ^ (h + c) : ℕ) : ℝ) := by
    rw [cell_width]
    push_cast
    rw [pow_succ]
    field_simp
  rw [hy, hz]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, by exact_mod_cast h2, by exact_mod_cast h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, by exact_mod_cast h2, by exact_mod_cast h3, h4⟩

/-! ### The bound at a state -/

/-- `ceilDiv x d₁ d` is `(x + d₁) / d`. -/
theorem ceilDiv_eq (x d₁ d : ℕ) : ceilDiv x d₁ d = (x + d₁) / d := rfl

/-- If `d₁ + 1 = d`, then `x / d ≤ ceilDiv x d₁ d` in `ℝ`. -/
theorem div_le_ceilDiv' {x d₁ d : ℕ} (hd : d₁ + 1 = d) : (x : ℝ) / d ≤ ceilDiv x d₁ d := by
  rw [ceilDiv_eq, show x + d₁ = x + d - 1 by omega]
  exact div_le_ceilDiv x d (by omega)

/-- One term of the bound at a state: `w ψ G ≤ ⌈a c G' / d⌉ / 2^64` when `w = a 2^64 / d`,
`ψ ≤ c / 2^64` and `G ≤ G' / 2^64`. -/
theorem node_term {w ψ G : ℝ} {a cap G' d₁ d : ℕ} (hd : d₁ + 1 = d) (hw : w = (a : ℝ) / d * one)
    (hψ0 : 0 ≤ ψ) (hψ : ψ ≤ (cap : ℝ) / one) (hG0 : 0 ≤ G) (hG : G ≤ (G' : ℝ) / one) :
    w * (ψ * G) ≤ (ceilDiv (Nat.mul (Nat.mul a cap) G') d₁ d : ℝ) / one := by
  have hone : (0 : ℝ) < one := by exact_mod_cast one_pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h1 := div_le_ceilDiv' (x := Nat.mul (Nat.mul a cap) G') hd
  have hψG : ψ * G ≤ (cap : ℝ) / one * ((G' : ℝ) / one) :=
    mul_le_mul hψ hG hG0 (hψ0.trans hψ)
  rw [hw]
  calc (a : ℝ) / d * one * (ψ * G) ≤ (a : ℝ) / d * one * ((cap : ℝ) / one * ((G' : ℝ) / one)) := by
        gcongr
    _ = ((Nat.mul (Nat.mul a cap) G' : ℕ) : ℝ) / d / one := by
        simp only [Nat.mul_eq]
        push_cast
        field_simp
    _ ≤ _ := by gcongr

/-- The sum over `2 ≤ c ≤ 8`. -/
theorem sum_Icc_two_eight (f : ℕ → ℝ) :
    ∑ c ∈ Icc 2 8, f c = f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [show Icc 2 8 = {2, 3, 4, 5, 6, 7, 8} by decide]
  simp [sum_insert]
  ring

/-- For `c ≥ 2`, `ϖ(c) = (c - 1) / 2^c`. -/
theorem varpi_natCast_eq (c : ℕ) (hc : 2 ≤ c) : varpi (c : ℤ) = ((c : ℝ) - 1) / 2 ^ c := by
  rw [varpi_of_two_le (by exact_mod_cast hc), zpow_neg, zpow_natCast]
  push_cast
  ring

/-- For `2 ≤ c ≤ 8` and the constant cut `8`, the factor of the tree cost at `(r, h, c)` is the
capped factor `ψ_c` at `9^r x / 2^{h+c}`. -/
theorem trTreeFactor_eight {r h c : ℕ} (hc2 : 2 ≤ c) (hc8 : c ≤ 8) (x : ℝ) :
    trTreeFactor (fun _ => 8) r h (c : ℤ) x = trCapFactor (c : ℤ) (9 ^ r * x / 2 ^ (h + c)) := by
  rw [trTreeFactor_of_mem (by exact_mod_cast hc2) (by push_cast; exact_mod_cast hc8)]
  congr 2

/-- The child bound `condR b g 2^64 / 2^64` of a continuation `p` whose membership in `W` is
decided by `b`: either it is `1`, or `p ∈ W` and it bounds `F`. -/
theorem child_bound {W : Set (ℕ × ℕ × ℕ)} {p : ℕ × ℕ × ℕ} {F : ℝ} {b : Bool} {g : ℕ}
    (hb : p ∈ W ↔ b = true) (hg : p ∈ W → F ≤ (g : ℝ) / one) :
    1 ≤ ((condR b g one : ℕ) : ℝ) / one ∨ (p ∈ W ∧ F ≤ ((condR b g one : ℕ) : ℝ) / one) := by
  cases b
  · left
    have hone : (0 : ℝ) < one := by exact_mod_cast one_pos
    exact (div_self hone.ne').ge
  · exact Or.inr ⟨hb.2 rfl, hg (hb.2 rfl)⟩

/-- `nodeB` as a sum in `ℝ` of its constant term and its seven rounded-up terms. -/
theorem nodeB_eq (ω H h : ℕ) (g8 g7 g6 g5 g4 g3 g2 : ℕ) (e8 e7 e6 e5 e4 e3 : Entry) :
    (nodeB ω H h g8 g7 g6 g5 g4 g3 g2 e8 e7 e6 e5 e4 e3 : ℝ) =
      648518346341351424 + ceilDiv (condR (Nat.ble (Nat.add h 2) H) g2 one) 3 4 +
      ceilDiv (Nat.mul (Nat.mul 2 e3.c3) (condR (Nat.ble (Nat.add h 3) H) g3 one))
        147573952589676412927 147573952589676412928 +
      ceilDiv (Nat.mul (Nat.mul 3 e4.c4)
          (condR (and (Nat.ble (Nat.add h 4) H) (or (Nat.ble (Nat.add h 4) ω) e4.wh)) g4 one))
        295147905179352825855 295147905179352825856 +
      ceilDiv (Nat.mul (Nat.mul 4 e5.c5)
          (condR (and (Nat.ble (Nat.add h 5) H) (or (Nat.ble (Nat.add h 5) ω) e5.wh)) g5 one))
        590295810358705651711 590295810358705651712 +
      ceilDiv (Nat.mul (Nat.mul 5 e6.c6) (condR (Nat.ble (Nat.add h 6) H) g6 one))
        1180591620717411303423 1180591620717411303424 +
      ceilDiv (Nat.mul (Nat.mul 6 e7.c7) (condR (Nat.ble (Nat.add h 7) H) g7 one))
        2361183241434822606847 2361183241434822606848 +
      ceilDiv (Nat.mul (Nat.mul 7 e8.c8) (condR (Nat.ble (Nat.add h 8) H) g8 one))
        4722366482869645213695 4722366482869645213696 := by
  simp only [nodeB, Nat.add_eq]
  push_cast
  ring

/-- **The bound at a state.** If the factors at the children are bounded by the entries and
the tree costs at the children in `W` by the `g_c`, the tree cost at `(r, h)` is bounded by
`nodeB`. -/
theorem trTreeCost_le_nodeB {W : Set (ℕ × ℕ × ℕ)} (hW : IsBoundedPolicy W) {ω H r h : ℕ}
    {x : ℝ} {g8 g7 g6 g5 g4 g3 g2 : ℕ} {e8 e7 e6 e5 e4 e3 : Entry}
    (hc3 : trCapFactor ((3 : ℕ) : ℤ) (9 ^ r * x / 2 ^ (h + 3)) ≤ (e3.c3 : ℝ) / one)
    (hc4 : trCapFactor ((4 : ℕ) : ℤ) (9 ^ r * x / 2 ^ (h + 4)) ≤ (e4.c4 : ℝ) / one)
    (hc5 : trCapFactor ((5 : ℕ) : ℤ) (9 ^ r * x / 2 ^ (h + 5)) ≤ (e5.c5 : ℝ) / one)
    (hc6 : trCapFactor ((6 : ℕ) : ℤ) (9 ^ r * x / 2 ^ (h + 6)) ≤ (e6.c6 : ℝ) / one)
    (hc7 : trCapFactor ((7 : ℕ) : ℤ) (9 ^ r * x / 2 ^ (h + 7)) ≤ (e7.c7 : ℝ) / one)
    (hc8 : trCapFactor ((8 : ℕ) : ℤ) (9 ^ r * x / 2 ^ (h + 8)) ≤ (e8.c8 : ℝ) / one)
    (hm2 : (r, h, 2) ∈ W ↔ Nat.ble (Nat.add h 2) H = true)
    (hm3 : (r, h, 3) ∈ W ↔ Nat.ble (Nat.add h 3) H = true)
    (hm4 : (r, h, 4) ∈ W ↔
      and (Nat.ble (Nat.add h 4) H) (or (Nat.ble (Nat.add h 4) ω) e4.wh) = true)
    (hm5 : (r, h, 5) ∈ W ↔
      and (Nat.ble (Nat.add h 5) H) (or (Nat.ble (Nat.add h 5) ω) e5.wh) = true)
    (hm6 : (r, h, 6) ∈ W ↔ Nat.ble (Nat.add h 6) H = true)
    (hm7 : (r, h, 7) ∈ W ↔ Nat.ble (Nat.add h 7) H = true)
    (hm8 : (r, h, 8) ∈ W ↔ Nat.ble (Nat.add h 8) H = true)
    (hg2 : (r, h, 2) ∈ W → trTreeCost (fun _ => 8) W (r + 1) (h + 2) x ≤ (g2 : ℝ) / one)
    (hg3 : (r, h, 3) ∈ W → trTreeCost (fun _ => 8) W (r + 1) (h + 3) x ≤ (g3 : ℝ) / one)
    (hg4 : (r, h, 4) ∈ W → trTreeCost (fun _ => 8) W (r + 1) (h + 4) x ≤ (g4 : ℝ) / one)
    (hg5 : (r, h, 5) ∈ W → trTreeCost (fun _ => 8) W (r + 1) (h + 5) x ≤ (g5 : ℝ) / one)
    (hg6 : (r, h, 6) ∈ W → trTreeCost (fun _ => 8) W (r + 1) (h + 6) x ≤ (g6 : ℝ) / one)
    (hg7 : (r, h, 7) ∈ W → trTreeCost (fun _ => 8) W (r + 1) (h + 7) x ≤ (g7 : ℝ) / one)
    (hg8 : (r, h, 8) ∈ W → trTreeCost (fun _ => 8) W (r + 1) (h + 8) x ≤ (g8 : ℝ) / one) :
    trTreeCost (fun _ => 8) W r h x ≤
      (nodeB ω H h g8 g7 g6 g5 g4 g3 g2 e8 e7 e6 e5 e4 e3 : ℝ) / one := by
  have hone : (0 : ℝ) < one := by exact_mod_cast one_pos
  set G2 := condR (Nat.ble (Nat.add h 2) H) g2 one
  set G3 := condR (Nat.ble (Nat.add h 3) H) g3 one
  set G4 := condR (and (Nat.ble (Nat.add h 4) H) (or (Nat.ble (Nat.add h 4) ω) e4.wh)) g4 one
  set G5 := condR (and (Nat.ble (Nat.add h 5) H) (or (Nat.ble (Nat.add h 5) ω) e5.wh)) g5 one
  set G6 := condR (Nat.ble (Nat.add h 6) H) g6 one
  set G7 := condR (Nat.ble (Nat.add h 7) H) g7 one
  set G8 := condR (Nat.ble (Nat.add h 8) H) g8 one
  let f : ℕ → ℕ := fun c => match c with
    | 3 => e3.c3 | 4 => e4.c4 | 5 => e5.c5 | 6 => e6.c6 | 7 => e7.c7 | 8 => e8.c8 | _ => one
  let g : ℕ → ℕ := fun c => match c with
    | 2 => G2 | 3 => G3 | 4 => G4 | 5 => G5 | 6 => G6 | 7 => G7 | 8 => G8 | _ => one
  have hnode := trTreeCost_le_of_node_bound hW (cut := fun _ => 8) (r := r) (h := h) (X := x)
    (f := fun c => (f c : ℝ) / one) (g := fun c => (g c : ℝ) / one)
    (fun c hc2 hc8 => by
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
          c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 := by omega
      · rw [trTreeFactor_eight (c := 2) le_rfl (by norm_num),
          trCapFactor_of_not_mem (by norm_num)]
        change (1 : ℝ) ≤ (one : ℝ) / one
        rw [div_self hone.ne']
      all_goals rwa [trTreeFactor_eight (by norm_num) (by norm_num)])
    (fun c hc2 hc8 => by
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
          c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 := by omega
      · exact child_bound hm2 hg2
      · exact child_bound hm3 hg3
      · exact child_bound hm4 hg4
      · exact child_bound hm5 hg5
      · exact child_bound hm6 hg6
      · exact child_bound hm7 hg7
      · exact child_bound hm8 hg8)
  refine hnode.trans ?_
  rw [sum_Icc_two_eight]
  simp only [f, g]
  rw [varpi_natCast_eq 2 le_rfl, varpi_natCast_eq 3 (by norm_num),
    varpi_natCast_eq 4 (by norm_num), varpi_natCast_eq 5 (by norm_num),
    varpi_natCast_eq 6 (by norm_num), varpi_natCast_eq 7 (by norm_num),
    varpi_natCast_eq 8 (by norm_num)]
  have P0 : ∀ a : ℕ, (0 : ℝ) ≤ (a : ℝ) / one := fun a => by positivity
  have t3 := node_term (w := (((3 : ℕ) : ℝ) - 1) / 2 ^ 3) (a := 2) (cap := e3.c3)
    (d₁ := 147573952589676412927) (d := 147573952589676412928) (by norm_num)
    (by norm_num [one]) (P0 _) le_rfl (P0 G3) le_rfl
  have t4 := node_term (w := (((4 : ℕ) : ℝ) - 1) / 2 ^ 4) (a := 3) (cap := e4.c4)
    (d₁ := 295147905179352825855) (d := 295147905179352825856) (by norm_num)
    (by norm_num [one]) (P0 _) le_rfl (P0 G4) le_rfl
  have t5 := node_term (w := (((5 : ℕ) : ℝ) - 1) / 2 ^ 5) (a := 4) (cap := e5.c5)
    (d₁ := 590295810358705651711) (d := 590295810358705651712) (by norm_num)
    (by norm_num [one]) (P0 _) le_rfl (P0 G5) le_rfl
  have t6 := node_term (w := (((6 : ℕ) : ℝ) - 1) / 2 ^ 6) (a := 5) (cap := e6.c6)
    (d₁ := 1180591620717411303423) (d := 1180591620717411303424) (by norm_num)
    (by norm_num [one]) (P0 _) le_rfl (P0 G6) le_rfl
  have t7 := node_term (w := (((7 : ℕ) : ℝ) - 1) / 2 ^ 7) (a := 6) (cap := e7.c7)
    (d₁ := 2361183241434822606847) (d := 2361183241434822606848) (by norm_num)
    (by norm_num [one]) (P0 _) le_rfl (P0 G7) le_rfl
  have t8 := node_term (w := (((8 : ℕ) : ℝ) - 1) / 2 ^ 8) (a := 7) (cap := e8.c8)
    (d₁ := 4722366482869645213695) (d := 4722366482869645213696) (by norm_num)
    (by norm_num [one]) (P0 _) le_rfl (P0 G8) le_rfl
  have t2 : (((2 : ℕ) : ℝ) - 1) / 2 ^ 2 * ((one : ℝ) / one * ((G2 : ℝ) / one)) ≤
      ((ceilDiv G2 3 4 : ℕ) : ℝ) / one := by
    have := div_le_ceilDiv' (x := G2) (d₁ := 3) (d := 4) rfl
    rw [div_self hone.ne', one_mul]
    calc _ = (G2 : ℝ) / 4 / one := by push_cast; ring
      _ ≤ _ := by gcongr; exact_mod_cast this
  rw [nodeB_eq, add_div, add_div, add_div, add_div, add_div, add_div, add_div]
  have hκ : (648518346341351424 : ℝ) / one = 1 - (((2 : ℕ) : ℝ) - 1) / 2 ^ 2 -
      (((3 : ℕ) : ℝ) - 1) / 2 ^ 3 - (((4 : ℕ) : ℝ) - 1) / 2 ^ 4 - (((5 : ℕ) : ℝ) - 1) / 2 ^ 5 -
      (((6 : ℕ) : ℝ) - 1) / 2 ^ 6 - (((7 : ℕ) : ℝ) - 1) / 2 ^ 7 - (((8 : ℕ) : ℝ) - 1) / 2 ^ 8 := by
    norm_num [one]
  rw [hκ]
  linarith

/-! ### The rows -/

/-- `L` bounds `F` at the states `(r, h₀), (r, h₀ - 1), …, (r, 0)`. -/
def RowGood (F : ℕ → ℕ → ℝ) (r h₀ : ℕ) (L : List ℕ) : Prop :=
  ∀ i ≤ h₀, F r (h₀ - i) ≤ (L.getD i one : ℝ) / one

/-- `L` lists the entries at `θ_{h₀}, θ_{h₀ - 1}, …, θ_0`. -/
def EntGood (X XD r h₀ : ℕ) (L : List Entry) : Prop :=
  ∀ i ≤ h₀, L.getD i Entry.zero = specEntry X XD r (h₀ - i)

/-- If `F ≤ 1` everywhere, a list whose entries are all `2^64` bounds `F` on every row. -/
theorem rowGood_of_le_one {F : ℕ → ℕ → ℝ} (hF : ∀ r h, F r h ≤ 1) {r h₀ : ℕ} {L : List ℕ}
    (hL : ∀ i, L.getD i one = one) : RowGood F r h₀ L := by
  intro i _
  have hone : (0 : ℝ) < one := by exact_mod_cast one_pos
  rw [hL, div_self hone.ne']
  exact hF _ _

/-- The cell data: the tree cost `F^{8,W}_{r,h}(X / X_D)` of the white-test policy of the cell
`(D, k)` at `m`. -/
noncomputable def cellCost (ω H D k m r h : ℕ) : ℝ :=
  trTreeCost (fun _ => 8) (trWhitePolicy ω 8 (H : ℕ) (m : ℤ) (cellLo D k) (cellHi D k)) r h
    ((cellX ω D k m : ℝ) / (3 * 2 ^ D : ℕ))

/-- The cell data are at most `1`. -/
theorem cellCost_le_one (ω H D k m r h : ℕ) : cellCost ω H D k m r h ≤ 1 :=
  trTreeCost_le_one _ _ _ _ _

/-- `theta X XD r n` is `9^r (X / X_D) / 2^n`. -/
theorem theta_eq (X XD r n : ℕ) :
    theta X XD r n = 9 ^ r * ((X : ℝ) / (XD : ℕ)) / 2 ^ n := by
  simp only [theta]
  push_cast
  rcases eq_or_ne (XD : ℝ) 0 with h | h
  · simp [h]
  · field_simp

/-- The bound at one state of a cell, from the windows of the row below and of the entries. -/
theorem cellCost_le_nodeB {ω H D k m r h : ℕ} (hm : 1 ≤ m)
    {g8 g7 g6 g5 g4 g3 g2 : ℕ} {gs : List ℕ} {e8 e7 e6 e5 e4 e3 : Entry} {es : List Entry}
    (hG : RowGood (cellCost ω H D k m) (r + 1) (h + 8)
      (g8 :: g7 :: g6 :: g5 :: g4 :: g3 :: g2 :: gs))
    (hE : EntGood (cellX ω D k m) (3 * 2 ^ D) r (h + 8) (e8 :: e7 :: e6 :: e5 :: e4 :: e3 :: es)) :
    cellCost ω H D k m r h ≤ (nodeB ω H h g8 g7 g6 g5 g4 g3 g2 e8 e7 e6 e5 e4 e3 : ℝ) / one := by
  set X := cellX ω D k m
  set XD := 3 * 2 ^ D
  have hXD : 0 < XD := by positivity
  have E : ∀ i (hi : i ≤ 5), (e8 :: e7 :: e6 :: e5 :: e4 :: e3 :: es).getD i Entry.zero =
      specEntry X XD r (h + 8 - i) := fun i hi => hE i (by omega)
  have E3 : e3 = specEntry X XD r (h + 3) := by simpa using E 5 (by norm_num)
  have E4 : e4 = specEntry X XD r (h + 4) := by simpa using E 4 (by norm_num)
  have E5 : e5 = specEntry X XD r (h + 5) := by simpa using E 3 (by norm_num)
  have E6 : e6 = specEntry X XD r (h + 6) := by simpa using E 2 (by norm_num)
  have E7 : e7 = specEntry X XD r (h + 7) := by simpa using E 1 (by norm_num)
  have E8 : e8 = specEntry X XD r (h + 8) := by simpa using E 0 (by norm_num)
  have G : ∀ c : ℕ, 2 ≤ c → c ≤ 8 → cellCost ω H D k m (r + 1) (h + c) ≤
      ((g8 :: g7 :: g6 :: g5 :: g4 :: g3 :: g2 :: gs).getD (8 - c) one : ℝ) / one := by
    intro c hc hc8
    have := hG (8 - c) (by omega)
    rwa [show h + 8 - (8 - c) = h + c by omega] at this
  have hcap : ∀ c : ℕ, 3 ≤ c → c ≤ 8 →
      trCapFactor (c : ℤ) (9 ^ r * ((X : ℝ) / (XD : ℕ)) / 2 ^ (h + c : ℕ)) ≤
        ((specEntry X XD r (h + c)).cap c : ℝ) / one := by
    intro c hc3 hc8
    rw [← theta_eq]
    exact trCapFactor_le_specEntry X XD r (h + c) c hXD hc3 hc8 (by omega)
  have hmem : ∀ c, (r, h, c) ∈ trWhitePolicy ω 8 (H : ℕ) (m : ℤ) (cellLo D k) (cellHi D k) ↔
      2 ≤ c ∧ c ≤ 8 ∧ h + c ≤ H ∧ (c ∉ ({4, 5} : Set ℕ) ∨ h + c ≤ ω ∨
        (specEntry X XD r (h + c)).wh = true) := by
    intro c
    rw [mem_cellPolicy_iff hm, specEntry_wh]
  refine trTreeCost_le_nodeB (isBoundedPolicy_trWhitePolicy _ _ _ _ _ _)
    (by rw [E3]; exact hcap 3 le_rfl (by norm_num))
    (by rw [E4]; exact hcap 4 (by norm_num) (by norm_num))
    (by rw [E5]; exact hcap 5 (by norm_num) (by norm_num))
    (by rw [E6]; exact hcap 6 (by norm_num) (by norm_num))
    (by rw [E7]; exact hcap 7 (by norm_num) (by norm_num))
    (by rw [E8]; exact hcap 8 (by norm_num) (by norm_num))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun _ => G 2 le_rfl (by norm_num))
    (fun _ => G 3 (by norm_num) (by norm_num))
    (fun _ => G 4 (by norm_num) (by norm_num))
    (fun _ => G 5 (by norm_num) (by norm_num))
    (fun _ => G 6 (by norm_num) (by norm_num))
    (fun _ => G 7 (by norm_num) (by norm_num))
    (fun _ => G 8 (by norm_num) le_rfl)
  all_goals
    rw [hmem]
    simp [Nat.ble_eq, Nat.add_eq, E4, E5]

/-- `rowGo` with `f + 1` steps is either empty, or the bound at `(r, h)` followed by `rowGo` with
`f` steps from the windows shifted by one. -/
theorem rowGo_cases (ω H f h : ℕ) (winG : List ℕ) (winE : List Entry) :
    rowGo ω H (f + 1) h winG winE = [] ∨
      ∃ g8 g7 g6 g5 g4 g3 g2 gs e8 e7 e6 e5 e4 e3 es,
        winG = g8 :: g7 :: g6 :: g5 :: g4 :: g3 :: g2 :: gs ∧
        winE = e8 :: e7 :: e6 :: e5 :: e4 :: e3 :: es ∧
        rowGo ω H (f + 1) h winG winE = nodeB ω H h g8 g7 g6 g5 g4 g3 g2 e8 e7 e6 e5 e4 e3 ::
          rowGo ω H f (h - 1) (g7 :: g6 :: g5 :: g4 :: g3 :: g2 :: gs)
            (e7 :: e6 :: e5 :: e4 :: e3 :: es) := by
  rcases winG with _ | ⟨g8, _ | ⟨g7, _ | ⟨g6, _ | ⟨g5, _ | ⟨g4, _ | ⟨g3, _ | ⟨g2, gs⟩⟩⟩⟩⟩⟩⟩ <;>
  rcases winE with _ | ⟨e8, _ | ⟨e7, _ | ⟨e6, _ | ⟨e5, _ | ⟨e4, _ | ⟨e3, es⟩⟩⟩⟩⟩⟩ <;>
  first
  | exact Or.inl rfl
  | exact Or.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rowGoW_succ ..⟩

/-- **One row.** If `winG` bounds the cell data at the level `r + 1` and `winE` lists the entries
at the level `r`, both from `h + 8` down, then `rowGo` bounds the cell data at the states
`(r, h), …, (r, 0)`. -/
theorem rowGo_spec {ω H D k m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    ∀ h (winG : List ℕ) (winE : List Entry),
      RowGood (cellCost ω H D k m) (r + 1) (h + 8) winG →
      EntGood (cellX ω D k m) (3 * 2 ^ D) r (h + 8) winE →
      RowGood (cellCost ω H D k m) r h (rowGo ω H (h + 1) h winG winE) := by
  have hF : ∀ r h, cellCost ω H D k m r h ≤ 1 := fun r h => cellCost_le_one _ _ _ _ _ _ _
  intro h
  induction h with
  | zero =>
    intro winG winE hG hE
    rcases rowGo_cases ω H 0 0 winG winE with h0 | ⟨g8, g7, g6, g5, g4, g3, g2, gs, e8, e7, e6,
      e5, e4, e3, es, rfl, rfl, heq⟩
    · rw [h0]; exact rowGood_of_le_one hF (fun i => by simp)
    · rw [heq]
      intro i hi
      obtain rfl : i = 0 := by omega
      rw [List.getD_cons_zero]
      exact cellCost_le_nodeB hm hG hE
  | succ h ih =>
    intro winG winE hG hE
    rcases rowGo_cases ω H (h + 1) (h + 1) winG winE with h0 | ⟨g8, g7, g6, g5, g4, g3, g2, gs,
      e8, e7, e6, e5, e4, e3, es, rfl, rfl, heq⟩
    · rw [h0]; exact rowGood_of_le_one hF (fun i => by simp)
    · rw [heq]
      have hnode := cellCost_le_nodeB hm hG hE
      have hG' : RowGood (cellCost ω H D k m) (r + 1) (h + 8)
          (g7 :: g6 :: g5 :: g4 :: g3 :: g2 :: gs) := by
        intro i hi
        have := hG (i + 1) (by omega)
        rwa [show h + 1 + 8 - (i + 1) = h + 8 - i by omega] at this
      have hE' : EntGood (cellX ω D k m) (3 * 2 ^ D) r (h + 8)
          (e7 :: e6 :: e5 :: e4 :: e3 :: es) := by
        intro i hi
        have := hE (i + 1) (by omega)
        rwa [show h + 1 + 8 - (i + 1) = h + 8 - i by omega] at this
      have hrest := ih _ _ hG' hE'
      rw [show h + 1 - 1 = h by omega]
      intro i hi
      rcases i with _ | i
      · rw [Nat.sub_zero, List.getD_cons_zero]
        exact hnode
      · have := hrest i (by omega)
        rw [show h + 1 - (i + 1) = h - i by omega]
        exact this

/-- **The rows.** If the lists of `acc` are the entry lists at the levels `r, r + 1, …`, then
`rowsGo` bounds the cell data at the states `(r, H + 8), …, (r, 0)`. -/
theorem rowsGo_spec {ω H D k m : ℕ} (hm : 1 ≤ m) :
    ∀ (acc : List (List Entry)) (r : ℕ),
      (∀ i < acc.length, EntGood (cellX ω D k m) (3 * 2 ^ D) (r + i) (H + 8) (acc.getD i [])) →
      RowGood (cellCost ω H D k m) r (H + 8) (rowsGo ω H acc) := by
  have hF : ∀ r h, cellCost ω H D k m r h ≤ 1 := fun r h => cellCost_le_one _ _ _ _ _ _ _
  intro acc
  induction acc with
  | nil =>
    intro r _
    refine rowGood_of_le_one hF (fun i => ?_)
    simp only [rowsGo, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> simp
  | cons l ls ih =>
    intro r hacc
    have hl : EntGood (cellX ω D k m) (3 * 2 ^ D) r (H + 8) l := by
      simpa using hacc 0 (by simp)
    have hls := ih (r + 1) (fun i hi => by
      have := hacc (i + 1) (by simp; omega)
      simpa [show r + (i + 1) = r + 1 + i by omega] using this)
    have hrow := rowGo_spec hm r H _ _ hls hl
    intro i hi
    simp only [rowsGo]
    rcases Nat.lt_or_ge i 8 with h8 | h8
    · rw [List.getD_append _ _ _ _ (by simpa using h8)]
      have hone : (0 : ℝ) < one := by exact_mod_cast one_pos
      rw [List.getD_replicate _ h8, div_self hone.ne']
      exact hF _ _
    · rw [List.getD_append_right _ _ _ _ (by simpa using h8)]
      have := hrow (i - 8) (by omega)
      simp only [List.length_replicate]
      rwa [show H - (i - 8) = H + 8 - i by omega] at this


/-! ### The Lipschitz constant -/

/-- The policy of all triples `(r, h, c)` with `2 ≤ c ≤ 8` and `h + c ≤ H`. -/
def allPolicy (H : ℕ) : Set (ℕ × ℕ × ℕ) := {p | 2 ≤ p.2.2 ∧ p.2.2 ≤ 8 ∧ p.2.1 + p.2.2 ≤ H}

/-- `allPolicy H` is a bounded policy. -/
theorem isBoundedPolicy_allPolicy (H : ℕ) : IsBoundedPolicy (allPolicy H) :=
  ⟨H, fun _ hp => ⟨hp.1, hp.2.2⟩⟩

/-- The white-test policy `W^{ω,8,H}_{m,a,b}` is contained in `allPolicy H`. -/
theorem trWhitePolicy_subset_allPolicy (ω H : ℕ) (m : ℤ) (a b : ℝ) :
    trWhitePolicy ω 8 (H : ℕ) m a b ⊆ allPolicy H := by
  intro p hp
  obtain ⟨h1, h2, h3, -⟩ := hp
  exact ⟨h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

end TrDirectCertificate

open Finset in
/-- **Monotonicity of the Lipschitz constant in the policy.** Let `cut : ℕ → ℕ` and let
`W ⊆ W'` be bounded policies. Then `L^{cut,W}_{r,h} ≤ L^{cut,W'}_{r,h}` for all `r, h ∈ ℕ`. -/
@[collatz_pos_dens "lem_tr_tree_lip_mono"]
theorem trTreeLip_mono {cut : ℕ → ℕ} {W W' : Set (ℕ × ℕ × ℕ)} (hW : IsBoundedPolicy W)
    (hW' : IsBoundedPolicy W') (hsub : W ⊆ W') (r h : ℕ) :
    trTreeLip cut W r h ≤ trTreeLip cut W' r h := by
  classical
  set K := policyBound W'
  suffices ∀ n r h, K + 1 - h = n → trTreeLip cut W r h ≤ trTreeLip cut W' r h from
    this _ r h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r h hn
    have hs : ∀ c, (r, h, c) ∈ W' → c ∈ range (K + 1) := fun c hc => by
      have := (hW'.le_policyBound hc).2
      simp only at this
      exact mem_range.2 (by omega)
    rw [trTreeLip_eq_sum hW r h (fun c hc => hs c (hsub hc)), trTreeLip_eq_sum hW' r h hs]
    apply add_le_add le_rfl
    calc ∑ c ∈ (range (K + 1)).filter (fun c => (r, h, c) ∈ W),
          varpi (c : ℤ) * trTreeLip cut W (r + 1) (h + c)
        ≤ ∑ c ∈ (range (K + 1)).filter (fun c => (r, h, c) ∈ W),
          varpi (c : ℤ) * trTreeLip cut W' (r + 1) (h + c) := by
          refine sum_le_sum fun c hc => ?_
          have hcW := (mem_filter.1 hc).2
          have := hW'.le_policyBound (hsub hcW)
          simp only at this
          exact mul_le_mul_of_nonneg_left (ih _ (by omega) _ _ rfl) (varpi_nonneg _)
      _ ≤ _ := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ =>
            mul_nonneg (varpi_nonneg _) (trTreeLip_nonneg _ _ _ _)
          intro c hc
          simp only [mem_filter] at hc ⊢
          exact ⟨hc.1, hsub hc.2⟩

namespace TrDirectCertificate

open Real Finset

/-- The sum `∑_{c=3}^{8} ϖ(c) ℓ_c 2^{-c} = 33055/114688`. -/
theorem sum_varpi_trLipConst :
    ∑ c ∈ Icc (3 : ℤ) 8, varpi c * (trLipConst c : ℝ) * (2 : ℝ) ^ (-c) = 33055 / 114688 := by
  have h3 : trLipConst 3 = 22 / 7 := by
    norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]
  have h8 : trLipConst 8 = 660 / 7 := by
    norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]
  rw [show Icc (3 : ℤ) 8 = {3, 4, 5, 6, 7, 8} by decide]
  simp only [sum_insert (by decide : (3 : ℤ) ∉ ({4, 5, 6, 7, 8} : Finset ℤ)),
    sum_insert (by decide : (4 : ℤ) ∉ ({5, 6, 7, 8} : Finset ℤ)),
    sum_insert (by decide : (5 : ℤ) ∉ ({6, 7, 8} : Finset ℤ)),
    sum_insert (by decide : (6 : ℤ) ∉ ({7, 8} : Finset ℤ)),
    sum_insert (by decide : (7 : ℤ) ∉ ({8} : Finset ℤ)), sum_singleton]
  rw [h3, trLipConst_four, trLipConst_five, trLipConst_six, trLipConst_seven, h8]
  simp only [varpi_of_two_le (by norm_num : (2 : ℤ) ≤ 3),
    varpi_of_two_le (by norm_num : (2 : ℤ) ≤ 4),
    varpi_of_two_le (by norm_num : (2 : ℤ) ≤ 5), varpi_of_two_le (by norm_num : (2 : ℤ) ≤ 6),
    varpi_of_two_le (by norm_num : (2 : ℤ) ≤ 7), varpi_of_two_le (by norm_num : (2 : ℤ) ≤ 8)]
  norm_num

/-- `⌈9^r 33055 2^64 / (114688 · 2^h)⌉`. -/
def lipHead (r h : ℕ) : ℕ :=
  (9 ^ r * 33055 * one + 114688 * 2 ^ h - 1) / (114688 * 2 ^ h)

/-- A bound for the Lipschitz constant of the tree cost of `allPolicy H`, by recursion. -/
def lipB (H : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, r, h => lipHead r h
  | f + 1, r, h => lipHead r h + ∑ c ∈ Icc 2 8,
      if h + c ≤ H then ((c - 1) * lipB H f (r + 1) (h + c) + 2 ^ c - 1) / 2 ^ c else 0

/-- If `H < h + f + 1`, the Lipschitz constant of the tree cost of `allPolicy H` at `(r, h)` is
at most `lipB H f r h / 2^64`. -/
theorem trTreeLip_allPolicy_le (H : ℕ) :
    ∀ f r h, H < h + f + 1 →
      trTreeLip (fun _ => 8) (allPolicy H) r h ≤ (lipB H f r h : ℝ) / one := by
  classical
  have hone : (0 : ℝ) < one := by exact_mod_cast one_pos
  have hhead : ∀ r h : ℕ, (9 : ℝ) ^ r * (2 : ℝ) ^ (-(h : ℤ)) *
      ∑ c ∈ Icc (3 : ℤ) ((fun _ => 8) h : ℕ), varpi c * (trLipConst c : ℝ) * (2 : ℝ) ^ (-c) ≤
      (lipHead r h : ℝ) / one := by
    intro r h
    simp only [Nat.cast_ofNat]
    rw [sum_varpi_trLipConst, lipHead]
    have := div_le_ceilDiv (K := ℝ) (9 ^ r * 33055 * one) (114688 * 2 ^ h) (by positivity)
    rw [le_div_iff₀ hone]
    refine le_trans (le_of_eq ?_) this
    rw [zpow_neg, zpow_natCast]
    push_cast
    field_simp
  intro f
  induction f with
  | zero =>
    intro r h hh
    rw [trTreeLip_of_forall_notMem (isBoundedPolicy_allPolicy H) (fun c hc => by
      have h1 := hc.1; have h2 := hc.2.2; simp only at h1 h2; omega)]
    exact hhead r h
  | succ f ih =>
    intro r h hh
    rw [trTreeLip_eq_sum (isBoundedPolicy_allPolicy H) r h (s := Icc 2 8)
      (fun c hc => mem_Icc.2 ⟨hc.1, hc.2.1⟩)]
    rw [lipB, Nat.cast_add, add_div]
    refine add_le_add (hhead r h) ?_
    rw [sum_filter, Nat.cast_sum, Finset.sum_div]
    refine sum_le_sum fun c hc => ?_
    have hc' := mem_Icc.1 hc
    have hmem : (r, h, c) ∈ allPolicy H ↔ h + c ≤ H := by
      simp only [allPolicy, Set.mem_ofPred_eq]
      omega
    by_cases hhc : h + c ≤ H
    · simp only [hmem, hhc, ↓reduceIte]
      have hL := ih (r + 1) (h + c) (by omega)
      have hw : varpi (c : ℤ) = ((c : ℝ) - 1) / 2 ^ c := varpi_natCast_eq c hc'.1
      have hceil := div_le_ceilDiv (K := ℝ) ((c - 1) * lipB H f (r + 1) (h + c)) (2 ^ c)
        (by positivity)
      rw [hw]
      have h1 : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      calc ((c : ℝ) - 1) / 2 ^ c * trTreeLip (fun _ => 8) (allPolicy H) (r + 1) (h + c)
          ≤ ((c : ℝ) - 1) / 2 ^ c * ((lipB H f (r + 1) (h + c) : ℝ) / one) := by
            have : (1 : ℝ) ≤ c := by exact_mod_cast (show 1 ≤ c by omega)
            exact mul_le_mul_of_nonneg_left hL (div_nonneg (by linarith) (by positivity))
        _ = (((c - 1) * lipB H f (r + 1) (h + c) : ℕ) : ℝ) / ((2 ^ c : ℕ) : ℝ) / one := by
            push_cast [h1]
            ring
        _ ≤ _ := by
            gcongr
    · simp only [hmem, hhc, ↓reduceIte]
      simp


/-! ### The entry lists -/

/-- The entry list `[e(n-1), …, e(0)]` at the level `r`. -/
def specRow (X XD r : ℕ) : ℕ → List Entry
  | 0 => []
  | n + 1 => specEntry X XD r n :: specRow X XD r n

/-- The entry lists at the levels `r, r + 1, …, r + R - 1`. -/
def specRows (X XD n : ℕ) : ℕ → ℕ → List (List Entry)
  | _, 0 => []
  | r, R + 1 => specRow X XD r n :: specRows X XD n (r + 1) R

/-- The `i`-th entry of `specRow X XD r (n + 1)` is the entry at `θ_{n-i}`, for `i ≤ n`. -/
theorem specRow_getD (X XD r : ℕ) :
    ∀ n i, i ≤ n → (specRow X XD r (n + 1)).getD i Entry.zero = specEntry X XD r (n - i) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := by omega
    rfl
  | succ n ih =>
    intro i hi
    rcases i with _ | i
    · rfl
    · have := ih i (by omega)
      rw [show n + 1 - (i + 1) = n - i by omega, ← this]
      rfl

/-- `specRow X XD r (H + 9)` lists the entries at `θ_{H+8}, …, θ_0`. -/
theorem entGood_specRow (X XD r H : ℕ) : EntGood X XD r (H + 8) (specRow X XD r (H + 9)) :=
  fun i hi => specRow_getD X XD r (H + 8) i hi

/-- The `i`-th list of `specRows X XD n r R` is the entry list at the level `r + i`, for
`i < R`. -/
theorem specRows_getD (X XD n : ℕ) :
    ∀ R r i, i < R → (specRows X XD n r R).getD i [] = specRow X XD (r + i) n := by
  intro R
  induction R with
  | zero => intro r i hi; omega
  | succ R ih =>
    intro r i hi
    rcases i with _ | i
    · rfl
    · have := ih (r + 1) i (by omega)
      rw [show r + (i + 1) = r + 1 + i by omega, ← this]
      rfl

/-- `specRows X XD n r R` has length `R`. -/
theorem length_specRows (X XD n : ℕ) : ∀ R r, (specRows X XD n r R).length = R := by
  intro R
  induction R with
  | zero => intro r; rfl
  | succ R ih => intro r; simp [specRows, ih]

/-- If `X' ≡ X (mod X_D 2^n)`, the entry computed by `mkEntry` at `X'` from the head of the
entry list at level `r` is the entry of `X` at `θ_n`. -/
theorem mkEntry_headD_specRow {X X' XD r n : ℕ} (h : X' ≡ X [MOD XD * 2 ^ n]) :
    mkEntry X' XD r n ((specRow X XD r n).headD Entry.zero) = specEntry X XD r n := by
  rw [mkEntry_congr h]
  cases n with
  | zero => rfl
  | succ n => rfl

/-- If `X' ≡ X (mod X_D 2^n)`, adding the level `n` at `X'` to the entry lists of `X` with `n`
entries gives the entry lists of `X` with `n + 1` entries. -/
theorem addLevel_specRows {X X' XD n : ℕ} (h : X' ≡ X [MOD XD * 2 ^ n]) :
    ∀ R r, addLevel X' XD n r (specRows X XD n r R) = specRows X XD (n + 1) r R := by
  intro R
  induction R with
  | zero => intro r; rfl
  | succ R ih =>
    intro r
    simp only [specRows, addLevel]
    rw [mkEntry_headD_specRow h, ih (r + 1)]
    rfl

/-! ### Soundness of a cell -/

/-- **Soundness of the acceptance test of a cell.** -/
theorem leafB_sound {ω p D k m TN TD LU R : ℕ} (hm : 1 ≤ m) (hTD : 0 < TD)
    (hT : trTailGain ω 8 = (TN : ℝ) / TD)
    (hL : trTreeLip (fun _ => 8) (allPolicy (ω + p)) 0 0 ≤ (LU : ℝ) / one)
    (hleaf : leafB ω (ω + p) TN TD LU (3 * 2 ^ D)
      (specRows (cellX ω D k m) (3 * 2 ^ D) (ω + p + 9) 0 R) = true)
    (β : ℝ) (hβ₁ : cellLo D k ≤ β) (hβ₂ : β ≤ cellHi D k) :
    trTreeCost (fun _ => 8) (trWhitePolicy ω 8 (ω + p : ℕ) (m : ℤ) (cellLo D k) (cellHi D k)) 0 0
        (2 ^ ω * (m : ℤ) + β) - trTailGain ω 8 < 77 / 100 := by
  set H := ω + p
  set X := cellX ω D k m
  set XD := 3 * 2 ^ D
  set W := trWhitePolicy ω 8 (H : ℕ) (m : ℤ) (cellLo D k) (cellHi D k)
  set acc := specRows X XD (H + 9) 0 R
  have hone : (0 : ℝ) < one := by exact_mod_cast one_pos
  have hXD : (0 : ℝ) < XD := by positivity
  have hrows := rowsGo_spec (ω := ω) (H := H) (D := D) (k := k) hm acc 0 (fun i hi => by
    rw [length_specRows] at hi
    rw [specRows_getD _ _ _ _ _ _ hi]
    exact entGood_specRow X XD (0 + i) H)
  have hF := hrows (H + 8) le_rfl
  rw [Nat.sub_self] at hF
  set FU := (rowsGo ω H acc).getD (H + 8) one
  have hlt : ((100 * TD * (XD * FU + LU) : ℕ) : ℝ) <
      ((one * XD * (77 * TD + 100 * TN) : ℕ) : ℝ) := by
    have := hleaf
    simp only [leafB, Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at this
    exact_mod_cast this
  push_cast at hlt
  have hcentre :
      (2 : ℝ) ^ ω * ((m : ℤ) : ℝ) + (cellLo D k + cellHi D k) / 2 = (X : ℝ) / (XD : ℕ) := by
    rw [Int.cast_natCast]; exact cell_center hm
  have hdist : |(2 ^ ω * ((m : ℤ) : ℝ) + β) - (X : ℝ) / (XD : ℕ)| ≤ 1 / XD := by
    rw [← hcentre, abs_le]
    have hw := cell_width D k
    have : (1 : ℝ) / XD = (cellHi D k - cellLo D k) / 2 := by
      rw [hw]; simp only [XD]; push_cast; field_simp
    rw [this]
    constructor <;> linarith
  have hLip := abs_trTreeCost_sub_le (fun _ => 8) W 0 0 (2 ^ ω * ((m : ℤ) : ℝ) + β)
    ((X : ℝ) / (XD : ℕ))
  have hLW : trTreeLip (fun _ => 8) W 0 0 ≤ (LU : ℝ) / one :=
    (trTreeLip_mono (isBoundedPolicy_trWhitePolicy _ _ _ _ _ _) (isBoundedPolicy_allPolicy _)
      (trWhitePolicy_subset_allPolicy _ _ _ _ _) 0 0).trans hL
  have hL0 : 0 ≤ trTreeLip (fun _ => 8) W 0 0 := trTreeLip_nonneg _ _ _ _
  have h1 : trTreeCost (fun _ => 8) W 0 0 (2 ^ ω * ((m : ℤ) : ℝ) + β) ≤
      (FU : ℝ) / one + (LU : ℝ) / one * (1 / XD) := by
    have := (abs_le.1 hLip).2
    have h2 : trTreeLip (fun _ => 8) W 0 0 * |(2 ^ ω * ((m : ℤ) : ℝ) + β) - (X : ℝ) / (XD : ℕ)| ≤
        (LU : ℝ) / one * (1 / XD) := mul_le_mul hLW hdist (abs_nonneg _) (by positivity)
    have hF' : trTreeCost (fun _ => 8) W 0 0 ((X : ℝ) / (XD : ℕ)) ≤ (FU : ℝ) / one := hF
    linarith
  rw [hT]
  have hTD' : (0 : ℝ) < TD := by exact_mod_cast hTD
  have key : (FU : ℝ) / one + (LU : ℝ) / one * (1 / XD) < 77 / 100 + (TN : ℝ) / TD := by
    have eA : (FU : ℝ) / one + (LU : ℝ) / one * (1 / XD) =
        ((XD : ℝ) * FU + LU) / (one * XD) := by
      field_simp
    have eB : (77 : ℝ) / 100 + (TN : ℝ) / TD = (77 * TD + 100 * TN) / (100 * TD) := by
      field_simp
    rw [eA, eB, div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  linarith


/-! ### Soundness of the residue recursion -/

/-- The statement proved for a cell `(D, k)` and `m`: for every `β` in the cell,
`F^{8,W}_{0,0}(2^ω m + β) - T^{root}_{ω,8} < 77/100`. -/
def CellGood (ω p D k m : ℕ) : Prop :=
  ∀ β : ℝ, cellLo D k ≤ β → β ≤ cellHi D k →
    trTreeCost (fun _ => 8) (trWhitePolicy ω 8 (ω + p : ℕ) (m : ℤ) (cellLo D k) (cellHi D k))
      0 0 (2 ^ ω * (m : ℤ) + β) - trTailGain ω 8 < 77 / 100

/-- For `m ≥ 1`, `cellX ω D k m + 2^D = 3 · 2^{D+ω} m + 2k + 1`. -/
theorem cellX_add_pow {ω D k m : ℕ} (hm : 1 ≤ m) :
    cellX ω D k m + 2 ^ D = 3 * 2 ^ (D + ω) * m + (2 * k + 1) := by
  have h : 2 ^ D ≤ 3 * 2 ^ (D + ω) * m + (2 * k + 1) := by
    have h1 : 2 ^ D ≤ 2 ^ (D + ω) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (D + ω) ≤ 2 ^ (D + ω) * (3 * m) := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : 2 ^ (D + ω) * (3 * m) = 3 * 2 ^ (D + ω) * m := by ring
    omega
  simp only [cellX, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq]
  omega

/-- `cellX` at `m` modulo `3 · 2^D · 2^n` depends only on `m` modulo `2^{n - ω}`. -/
theorem cellX_modEq {ω D k m m' t n : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') (h : m ≡ m' [MOD 2 ^ t])
    (hn : n ≤ ω + t) : cellX ω D k m ≡ cellX ω D k m' [MOD 3 * 2 ^ D * 2 ^ n] := by
  have h1 : 3 * 2 ^ (D + ω) * m ≡ 3 * 2 ^ (D + ω) * m' [MOD 3 * 2 ^ (D + ω) * 2 ^ t] :=
    Nat.ModEq.mul_left' _ h
  have h2 : 3 * 2 ^ D * 2 ^ n ∣ 3 * 2 ^ (D + ω) * 2 ^ t := by
    rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
    exact Nat.mul_dvd_mul_left 3 (pow_dvd_pow 2 (by omega))
  have h3 := (h1.of_dvd h2).add_right (2 * k + 1)
  rw [← cellX_add_pow hm, ← cellX_add_pow hm'] at h3
  exact Nat.ModEq.add_right_cancel' (2 ^ D) h3

/-- If `m ≡ m' (mod 2^j)` and `m` and `m'` have the same bit `j`, then
`m ≡ m' (mod 2^{j+1})`. -/
theorem modEq_two_pow_succ {m m' j : ℕ} (h : m ≡ m' [MOD 2 ^ j])
    (hb : m / 2 ^ j % 2 = m' / 2 ^ j % 2) : m ≡ m' [MOD 2 ^ (j + 1)] := by
  unfold Nat.ModEq at h ⊢
  rw [pow_succ, Nat.mod_mul, Nat.mod_mul, h, hb]

/-- The head of a nonempty list, with any default, is a member of it. -/
theorem headD_mem {ms : List ℕ} {m : ℕ} (hm : m ∈ ms) (d : ℕ) : ms.headD d ∈ ms := by
  cases ms with
  | nil => simp at hm
  | cons a l => simp

/-- **Soundness of the residue recursion.** -/
theorem resCheck_sound {ω p TN TD LU D k : ℕ} (hTD : 0 < TD)
    (hT : trTailGain ω 8 = (TN : ℝ) / TD)
    (hL : trTreeLip (fun _ => 8) (allPolicy (ω + p)) 0 0 ≤ (LU : ℝ) / one) :
    ∀ f n j (ms : List ℕ) (acc : List (List Entry)),
      resCheck ω (ω + p) TN TD LU D k f n j ms acc = true →
      n + f = ω + p + 9 → n ≤ ω + j + 1 → (∀ m ∈ ms, 1 ≤ m) →
      (∀ m ∈ ms, ∀ m' ∈ ms, m ≡ m' [MOD 2 ^ j]) →
      (∀ m ∈ ms, acc = specRows (cellX ω D k m) (3 * 2 ^ D) n 0 ((ω + p) / 2 + 1)) →
      ∀ m ∈ ms, CellGood ω p D k m := by
  intro f
  induction f with
  | zero =>
    intro n j ms acc hres hn _ hpos _ hacc m hm β hβ₁ hβ₂
    obtain rfl : n = ω + p + 9 := by omega
    rw [hacc m hm] at hres
    exact leafB_sound (hpos m hm) hTD hT hL hres β hβ₁ hβ₂
  | succ f ih =>
    intro n j ms acc hres hn hnj hpos hmod hacc
    simp only [resCheck] at hres
    by_cases hnω : n ≤ ω
    · have hb : Nat.ble n ω = true := by rw [Nat.ble_eq]; exact hnω
      rw [hb, Bool.cond_true] at hres
      refine ih (n + 1) j ms _ hres (by omega) (by omega) hpos hmod ?_
      intro m hm
      rw [hacc m hm]
      refine addLevel_specRows ?_ _ _
      exact cellX_modEq (t := 0) (hpos _ (headD_mem hm 1)) (hpos m hm) Nat.modEq_one
        (by omega)
    · have hb : Nat.ble n ω = false := by
        rw [Bool.eq_false_iff]; intro h; rw [Nat.ble_eq] at h; exact hnω h
      rw [hb, Bool.cond_false, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true] at hres
      intro m hm
      have hbit : m / 2 ^ j % 2 = 0 ∨ m / 2 ^ j % 2 = 1 := Nat.mod_two_eq_zero_or_one _
      have key : ∀ b, m / 2 ^ j % 2 = b →
          (ms.filter fun m => Nat.beq (Nat.mod (Nat.div m (Nat.pow 2 j)) 2) b).isEmpty = true ∨
            resCheck ω (ω + p) TN TD LU D k f (n + 1) (j + 1)
              (ms.filter fun m => Nat.beq (Nat.mod (Nat.div m (Nat.pow 2 j)) 2) b)
              (addLevel (cellX ω D k ((ms.filter fun m =>
                Nat.beq (Nat.mod (Nat.div m (Nat.pow 2 j)) 2) b).headD 1))
                (Nat.mul 3 (Nat.pow 2 D)) n 0 acc) = true →
          CellGood ω p D k m := by
        intro b hmb hpart
        set ms' := ms.filter fun m => Nat.beq (Nat.mod (Nat.div m (Nat.pow 2 j)) 2) b
        have hmem : ∀ x, x ∈ ms' ↔ x ∈ ms ∧ x / 2 ^ j % 2 = b := by
          intro x
          simp only [ms', List.mem_filter, Nat.beq_eq, Nat.pow_eq]
          rfl
        have hm' : m ∈ ms' := (hmem m).2 ⟨hm, hmb⟩
        have hne : ms'.isEmpty = false := by
          cases h : ms' with
          | nil => rw [h] at hm'; simp at hm'
          | cons _ _ => rfl
        rw [hne] at hpart
        have hpart' := hpart.resolve_left (by simp)
        refine ih (n + 1) (j + 1) ms' _ hpart' (by omega) (by omega)
          (fun x hx => hpos x ((hmem x).1 hx).1) ?_ ?_ m hm'
        · intro x hx y hy
          have hx' := (hmem x).1 hx
          have hy' := (hmem y).1 hy
          exact modEq_two_pow_succ (hmod x hx'.1 y hy'.1) (hx'.2.trans hy'.2.symm)
        · intro x hx
          have hx' := (hmem x).1 hx
          rw [hacc x hx'.1]
          refine addLevel_specRows ?_ _ _
          have hh := (hmem _).1 (headD_mem hx 1)
          exact cellX_modEq (t := j + 1) (hpos _ hh.1) (hpos x hx'.1)
            (modEq_two_pow_succ (hmod _ hh.1 x hx'.1) (hh.2.trans hx'.2.symm)) (by omega)
      rcases hbit with h0 | h1
      · exact key 0 h0 hres.1
      · exact key 1 h1 hres.2


/-- With no entries, `specRows X XD 0 r R` is the list of `R` empty lists. -/
theorem specRows_zero (X XD : ℕ) : ∀ R r, specRows X XD 0 r R = List.replicate R [] := by
  intro R
  induction R with
  | zero => intro r; rfl
  | succ R ih => intro r; simp only [specRows, ih]; rfl

/-- **Soundness of the check of a cell.** -/
theorem cellGood_of_cellCheck {ω p TN TD LU D k : ℕ} (hTD : 0 < TD)
    (hT : trTailGain ω 8 = (TN : ℝ) / TD)
    (hL : trTreeLip (fun _ => 8) (allPolicy (ω + p)) 0 0 ≤ (LU : ℝ) / one) {ms : List ℕ}
    (h : cellCheck ω p TN TD LU D k ms = true) (hpos : ∀ m ∈ ms, 1 ≤ m) :
    ∀ m ∈ ms, CellGood ω p D k m :=
  resCheck_sound hTD hT hL _ 0 0 ms _ h (by omega) (by omega) hpos
    (fun _ _ _ _ => Nat.modEq_one) (fun m _ => (specRows_zero _ _ _ _).symm)

/-- `Shape.hasLeaf` decides membership in `Shape.leaves`. -/
theorem Shape.hasLeaf_iff (s : Shape) : ∀ D k q, s.hasLeaf D k q = true ↔ q ∈ s.leaves D k := by
  induction s with
  | leaf =>
    intro D k q
    obtain ⟨a, b⟩ := q
    simp only [Shape.hasLeaf, Shape.leaves, Bool.and_eq_true, Nat.beq_eq, List.mem_singleton,
      Prod.mk.injEq]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩
  | node l r ihl ihr =>
    intro D k q
    simp only [Shape.hasLeaf, Bool.or_eq_true, Shape.leaves, List.mem_append, ihl, ihr]

/-- The shape of `m` is either the default shape or listed for `m` in `exc`. -/
theorem shapeOf_eq_or_mem (dflt : Shape) (exc : List (ℕ × Shape)) (m : ℕ) :
    shapeOf dflt exc m = dflt ∨ (m, shapeOf dflt exc m) ∈ exc := by
  unfold shapeOf
  induction exc with
  | nil => left; rfl
  | cons e t ih =>
    obtain ⟨a, b⟩ := e
    change (Bool.rec (motive := fun _ => Option Shape) (lookupShape m t) (some b)
        (Nat.beq a m)).getD dflt = dflt ∨
      (m, (Bool.rec (motive := fun _ => Option Shape) (lookupShape m t) (some b)
        (Nat.beq a m)).getD dflt) ∈ (a, b) :: t
    by_cases h : a = m
    · subst h
      right
      simp [Nat.beq_refl]
    · have : Nat.beq a m = false := by
        rw [Bool.eq_false_iff]; intro h'; exact h (Nat.eq_of_beq_eq_true h')
      simp only [this]
      rcases ih with ih | ih
      · left; exact ih
      · right; exact List.mem_cons_of_mem _ ih

/-- Every `m` with `1 ≤ m < 2^{p+8}` and `m ≡ ρ (mod 2^a)` whose shape has the accepted cell `q`
lies in `mList p a ρ q dflt exc`, for `a ≤ p + 8`. -/
theorem mem_mList {p a ρ m : ℕ} {q : ℕ × ℕ} {dflt : Shape} {exc : List (ℕ × Shape)}
    (ha : a ≤ p + 8) (hm : m < 2 ^ (p + 8)) (hm1 : 1 ≤ m) (hρ : m % 2 ^ a = ρ)
    (hq : q ∈ (shapeOf dflt exc m).leaves 0 0) : m ∈ mList p a ρ q dflt exc := by
  unfold mList
  by_cases hd : dflt.hasLeaf 0 0 q = true
  · rw [hd, Bool.cond_true]
    simp only [List.mem_filter, List.mem_map, List.mem_range]
    refine ⟨⟨m / 2 ^ a, ?_, ?_⟩, (Shape.hasLeaf_iff _ _ _ _).2 hq⟩
    · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show p + 8 - a + a = p + 8 by omega]
      exact hm
    · rw [← hρ]
      exact Nat.mod_add_div m (2 ^ a)
  · rw [Bool.not_eq_true] at hd
    rw [hd, Bool.cond_false]
    rcases shapeOf_eq_or_mem dflt exc m with h | h
    · rw [h, ← Shape.hasLeaf_iff] at hq
      rw [hq] at hd
      exact absurd hd (by decide)
    · simp only [List.mem_filter, List.mem_map, Nat.ble_eq]
      exact ⟨⟨_, ⟨h, (Shape.hasLeaf_iff _ _ _ _).2 hq⟩, rfl⟩, hm1⟩

/-- For `ρ ≥ 1`, every member of `mList p a ρ q dflt exc` is at least `1`. -/
theorem pos_of_mem_mList {p a ρ m : ℕ} {q : ℕ × ℕ} {dflt : Shape} {exc : List (ℕ × Shape)}
    (hρ : 1 ≤ ρ) (hm : m ∈ mList p a ρ q dflt exc) : 1 ≤ m := by
  unfold mList at hm
  cases hd : dflt.hasLeaf 0 0 q
  · rw [hd, Bool.cond_false] at hm
    simp only [List.mem_filter, Nat.ble_eq] at hm
    exact hm.2
  · rw [hd, Bool.cond_true] at hm
    simp only [List.mem_filter, List.mem_map] at hm
    obtain ⟨⟨i, -, rfl⟩, -⟩ := hm
    omega

/-- The left half of the cell `(D, k)` has its left endpoint. -/
theorem cellLo_half_left (D k : ℕ) : cellLo (D + 1) (2 * k) = cellLo D k := by
  simp only [cellLo]; push_cast; rw [pow_succ]; field_simp

/-- The right half of the cell `(D, k)` has its right endpoint. -/
theorem cellHi_half_right (D k : ℕ) : cellHi (D + 1) (2 * k + 1) = cellHi D k := by
  simp only [cellHi]; push_cast; rw [pow_succ]; field_simp; ring

/-- The left half of the cell `(D, k)` ends where its right half begins. -/
theorem cellHi_half_left (D k : ℕ) : cellHi (D + 1) (2 * k) = cellLo (D + 1) (2 * k + 1) := by
  simp only [cellHi, cellLo]; push_cast; ring

/-- The accepted cells of a shape cover its root cell. -/
theorem Shape.exists_mem_leaves (s : Shape) :
    ∀ D k β, cellLo D k ≤ β → β ≤ cellHi D k →
      ∃ q ∈ s.leaves D k, cellLo q.1 q.2 ≤ β ∧ β ≤ cellHi q.1 q.2 := by
  induction s with
  | leaf => intro D k β h₁ h₂; exact ⟨(D, k), by simp [Shape.leaves], h₁, h₂⟩
  | node l r ihl ihr =>
    intro D k β h₁ h₂
    rcases le_total β (cellHi (D + 1) (2 * k)) with h | h
    · obtain ⟨q, hq, hq'⟩ := ihl (D + 1) (2 * k) β (by rw [cellLo_half_left]; exact h₁) h
      exact ⟨q, by simp [Shape.leaves, hq], hq'⟩
    · obtain ⟨q, hq, hq'⟩ := ihr (D + 1) (2 * k + 1) β (by rw [← cellHi_half_left]; exact h)
        (by rw [cellHi_half_right]; exact h₂)
      exact ⟨q, by simp [Shape.leaves, hq], hq'⟩

/-- The accepted cells of a shape lie in its root cell's range of indices. -/
theorem Shape.lt_of_mem_leaves (s : Shape) :
    ∀ D k, k < 2 ^ D → ∀ q ∈ s.leaves D k, q.2 < 2 ^ q.1 := by
  induction s with
  | leaf =>
    intro D k hk q hq
    simp only [Shape.leaves, List.mem_singleton] at hq
    rw [hq]
    exact hk
  | node l r ihl ihr =>
    intro D k hk q hq
    simp only [Shape.leaves, List.mem_append] at hq
    rcases hq with hq | hq
    · exact ihl (D + 1) (2 * k) (by rw [pow_succ]; omega) q hq
    · exact ihr (D + 1) (2 * k + 1) (by rw [pow_succ]; omega) q hq

/-- Every cell begins at or after `-1/3`. -/
theorem neg_one_third_le_cellLo (D k : ℕ) : -1 / 3 ≤ cellLo D k := by
  rw [cellLo, le_div_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ k := by positivity
  nlinarith

/-- For `k < 2^D`, the cell `(D, k)` ends at or before `1/3`. -/
theorem cellHi_le_one_third {D k : ℕ} (hk : k < 2 ^ D) : cellHi D k ≤ 1 / 3 := by
  rw [cellHi, div_le_iff₀ (by positivity)]
  have : (k : ℝ) + 1 ≤ 2 ^ D := by exact_mod_cast hk
  nlinarith

/-- The accepted cells of the shapes of a shape function lie in a list `Q`. -/
theorem mem_of_mem_leaves_shapeOf {dflt : Shape} {exc : List (ℕ × Shape)} {Q : List (ℕ × ℕ)}
    (h₁ : ∀ q ∈ dflt.leaves 0 0, q ∈ Q) (h₂ : ∀ e ∈ exc, ∀ q ∈ e.2.leaves 0 0, q ∈ Q) {m : ℕ}
    {q : ℕ × ℕ} (hq : q ∈ (shapeOf dflt exc m).leaves 0 0) : q ∈ Q := by
  rcases shapeOf_eq_or_mem dflt exc m with h | h
  · rw [h] at hq; exact h₁ q hq
  · exact h₂ _ h q hq

/-- **From covers to the direct-entry bound.** If, for every odd `m < 2^{p+8}`, every accepted
cell of the shape of `m` is good, then the bound of the direct-entry certificate holds. -/
theorem exists_of_cellGood {ω p : ℕ} (sh : ℕ → Shape)
    (hgood : ∀ m : ℕ, m % 2 = 1 → m < 2 ^ (p + 8) → ∀ q ∈ (sh m).leaves 0 0,
      CellGood ω p q.1 q.2 m)
    {m : ℤ} (hm : Odd m) (hm0 : 0 < m) (hm1 : m < 2 ^ (p + 8)) {β : ℝ} (hβ : |β| ≤ 1 / 3) :
    ∃ a b : ℝ, -1 / 3 ≤ a ∧ a ≤ β ∧ β ≤ b ∧ b ≤ 1 / 3 ∧
      trTreeCost (fun _ => 8) (trWhitePolicy ω 8 (ω + p : ℕ) m a b) 0 0 (2 ^ ω * m + β) -
        trTailGain ω 8 < 77 / 100 := by
  lift m to ℕ using hm0.le
  have hodd : m % 2 = 1 := by
    obtain ⟨j, hj⟩ := hm
    omega
  have hlt : m < 2 ^ (p + 8) := by exact_mod_cast hm1
  have h0 : cellLo 0 0 = -1 / 3 := by norm_num [cellLo]
  have h1 : cellHi 0 0 = 1 / 3 := by norm_num [cellHi]
  obtain ⟨q, hq, hβ₁, hβ₂⟩ := (sh m).exists_mem_leaves 0 0 β
    (by rw [h0]; linarith [(abs_le.1 hβ).1]) (by rw [h1]; linarith [(abs_le.1 hβ).2])
  have hk := (sh m).lt_of_mem_leaves 0 0 (by norm_num) q hq
  refine ⟨cellLo q.1 q.2, cellHi q.1 q.2, neg_one_third_le_cellLo _ _, hβ₁, hβ₂,
    cellHi_le_one_third hk, ?_⟩
  exact hgood m hodd hlt q hq β hβ₁ hβ₂

end TrDirectCertificate

end CollatzPosDens
