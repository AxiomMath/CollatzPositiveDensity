/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# Appending blocks does not change an earlier path

For a base point `o : ℤ × ℤ` and lists of blocks `u` and `f`, the path `trPath o (u ++ f)` of
the concatenation agrees with the path `trPath o u` at every time `t ≤ u.length`. This follows
from the corresponding statement `chBlockPath_append_of_le` for block paths, together with
`min t (u.length + f.length) = t = min t u.length`.

## Main results

* `CollatzPosDens.trPath_concat`: `trPath o (u ++ f) t = trPath o u t` for `t ≤ u.length`.

## Implementation notes

The statement holds for every base point and every pair of lists of blocks, with no condition
on the closing letters of the blocks.

## References

* [Mazur, *Collatz positive density*], §9.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- Appending blocks does not change the path up to the length of the prefix:
`trPath o (u ++ f) t = trPath o u t` for `t ≤ u.length`. -/
@[collatz_pos_dens "lem_tr_concat"]
theorem trPath_concat (o : ℤ × ℤ) (u f : List (List ℤ × ℤ)) {t : ℕ} (ht : t ≤ u.length) :
    trPath o (u ++ f) t = trPath o u t := by
  rw [trPath_def, trPath_def, List.length_append, min_eq_left ht,
    min_eq_left (ht.trans (Nat.le_add_right _ _)), chBlockPath_append_of_le u f ht]

end CollatzPosDens
