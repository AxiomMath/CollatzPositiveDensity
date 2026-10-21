/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3StageMap
public import CollatzPosDens.Transfer.S02Schedule

/-!
# The stage deadlines

For a Fourier index `ι`, a gap threshold `G ≥ 0` and a run length `d ≥ 1`, the *stage deadlines*
`𝔱^{G,d}_s(ι)`, `s ∈ ℕ`, are the orbit of the first schedule position `p_0(ι)` under the stage
deadline map `𝔣^{G,d}_ι`:
```
𝔱^{G,d}_0(ι) = p_0(ι),   𝔱^{G,d}_{s+1}(ι) = 𝔣^{G,d}_ι(𝔱^{G,d}_s(ι)).
```
On the survival event, `s` stages of a stopping trace are complete by time `𝔱^{G,d}_s(ι)`.

## Main definitions

* `CollatzPosDens.trStageTime ι G d s`: the stage deadline `𝔱^{G,d}_s(ι)`.

## Main results

* `CollatzPosDens.trStageTime_zero`, `CollatzPosDens.trStageTime_succ`: the recursion.
* `CollatzPosDens.trStageTime_strictMono`: the deadlines increase strictly.

## Implementation notes

The parameters `G` and `d` are natural numbers, and the deadlines are defined for every `d ∈ ℕ`;
only the values with `d ≥ 1` are the stage deadlines described above.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The stage deadlines: `𝔱^{G,d}_0(ι) = p_0(ι)` and
`𝔱^{G,d}_{s+1}(ι) = 𝔣^{G,d}_ι(𝔱^{G,d}_s(ι))`. -/
@[collatz_pos_dens "def_c3_stage_times"]
noncomputable def trStageTime (ι : FIndex) (G d : ℕ) : ℕ → ℕ
  | 0 => schedule ι 0
  | s + 1 => trStageMap ι G d (trStageTime ι G d s)

/-- `𝔱^{G,d}_0(ι) = p_0(ι)`. -/
@[simp]
theorem trStageTime_zero (ι : FIndex) (G d : ℕ) : trStageTime ι G d 0 = schedule ι 0 := rfl

/-- `𝔱^{G,d}_{s+1}(ι) = 𝔣^{G,d}_ι(𝔱^{G,d}_s(ι))`. -/
theorem trStageTime_succ (ι : FIndex) (G d s : ℕ) :
    trStageTime ι G d (s + 1) = trStageMap ι G d (trStageTime ι G d s) := rfl

/-- The stage deadlines increase strictly. -/
theorem trStageTime_strictMono (ι : FIndex) (G d : ℕ) : StrictMono (trStageTime ι G d) :=
  strictMono_nat_of_lt_succ fun _ => lt_trStageMap ι G d _

end CollatzPosDens
