/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr

/-! # The definitions of the challenge statements

The definitions of `Challenge/Basic.lean`, repeated word for word and in the same order, so that
the development and the challenge elaborate to the same constants.
-/

@[expose] public section

open Finset

/-- The Collatz map: `n ↦ n / 2` for even `n`, and `n ↦ 3n + 1` for odd `n`. -/
@[collatz_pos_dens "def_collatz"]
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `n` reaches `1` in at most `steps` applications of the Collatz map. -/
@[reducible, collatz_pos_dens "def_reaches_one"]
def CollatzOneWithin (n steps : ℕ) : Prop :=
  ∃ r ≤ steps, collatz^[r] n = 1

/-- The density constant `c = 1 / 2^2^2^140214`. -/
@[collatz_pos_dens "def_challenge_density"]
def collatzDensity : ℚ :=
  1 / 2 ^ 2 ^ 2 ^ 140214

/-- The cutoff `X₀ = 2^2^2^2^140214`. -/
@[collatz_pos_dens "def_challenge_threshold"]
def collatzDensityThreshold : ℕ :=
  2 ^ 2 ^ 2 ^ 2 ^ 140214

/-- Accelerated Collatz map, aka Syracuse map. Sends odd `n` to `3n + 1` divided by the highest
power of 2 that divides `3n + 1`. -/
@[collatz_pos_dens "def_collatz_accel"]
def collatzAccel (n : ℕ) : ℕ :=
  (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1)

/-- The odd part `n / 2 ^ padicValNat 2 n` of `n` reaches `1` in at most `steps` applications of
the accelerated Collatz map (which fixes `1`). -/
@[reducible, collatz_pos_dens "def_accel_reaches_one"]
def CollatzAccelOneWithin (n steps : ℕ) : Prop :=
  collatzAccel^[steps] (n / 2 ^ padicValNat 2 n) = 1
