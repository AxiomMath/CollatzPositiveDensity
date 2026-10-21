/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Dsc

/-!
# Scales above the threshold exceed the final time

At every Fourier parameter index `ι`, every real scale above the scale threshold is at least the
final time: for every real `m ≥ D_sc(ι)` we have `P_*(ι) ≤ m`. This holds because
`D_sc(ι) = 2 + P_*(ι) + x_ι ≥ P_*(ι)`, where `x_o = ⌈2 Ω_far(o) / 3⌉` and
`x_b = ⌈Ω_far(b) / 2⌉` are natural numbers.

## Main results

* `CollatzPosDens.pStar_le_of_Dsc_le`: for real `m ≥ D_sc(ι)`, `P_*(ι) ≤ m`.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every index `ι` and every real `m ≥ D_sc(ι)`, `P_*(ι) ≤ m`. Stated over any ordered
semiring. -/
@[collatz_pos_dens "lem_s02_far_B"]
theorem pStar_le_of_Dsc_le {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    (ι : FIndex) {m : R} (hm : (Dsc ι : R) ≤ m) : (pStar ι : R) ≤ m :=
  (Nat.mono_cast (pStar_le_Dsc ι)).trans hm

end CollatzPosDens
