/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

import Mathlib
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2005, Problem 1

Legs L₁, L₂, L₃, L₄ of a square table each have length n,
where n is a positive integer.
For how many ordered 4-tuples (k₁, k₂, k₃, k₄) of nonnegative integers
can we cut a piece of length kᵢ from the end of leg Lᵢ
and still have a stable table?

(The table is stable if it can be placed
so that all four of the leg ends touch the floor.
Note that a cut leg of length 0 is permitted.)
-/

namespace Usa2005P4

notation "Pt" => EuclideanSpace ℝ (Fin 3)

def LegEndpointsCoplanar (l₁ l₂ l₃ l₄ : ℕ) : Prop :=
  let P₁ : Pt := !₂[0, 0, l₁]
  let P₂ : Pt := !₂[0, 1, l₂]
  let P₃ : Pt := !₂[1, 0, l₃]
  let P₄ : Pt := !₂[1, 1, l₄]
  Coplanar ℝ {P₁, P₂, P₃, P₄}

snip begin

snip end

determine solution : ℕ → ℕ := fun n ↦ (n+1) * (2*n^2+4*n+3) / 3

def KTuples (n : ℕ) : Set (Fin 4 → ℕ) := { k | ∀ i : Fin 4, (k i) ≤ n }

def CoplanarKTuples (n : ℕ) : Set (Fin 4 → ℕ) :=
  { k | k ∈ KTuples n ∧
    LegEndpointsCoplanar (n - k 0) (n - k 1) (n - k 2) (n - k 3) }

problem usa2005_p4 (n : ℕ) :
    (CoplanarKTuples n).ncard = (solution n) := by
  sorry

end Usa2005P4
