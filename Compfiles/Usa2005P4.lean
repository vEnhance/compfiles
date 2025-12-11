/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau
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

open Finset

notation "Pt" => EuclideanSpace ℝ (Fin 3)

def LegEndpointsCoplanar (l₁ l₂ l₃ l₄ : ℝ) : Prop :=
  let P₁ : Pt := !₂[0, 0, l₁]
  let P₂ : Pt := !₂[0, 1, l₂]
  let P₃ : Pt := !₂[1, 1, l₃]
  let P₄ : Pt := !₂[1, 0, l₄]
  Coplanar ℝ {P₁, P₂, P₃, P₄}

def kTuples (n : ℕ) : Set (Fin 4 → ℕ) := { k | ∀ i : Fin 4, (k i) ≤ n }

def kTuplesCoplanar (n : ℕ) : Set (Fin 4 → ℕ) :=
  { k | k ∈ kTuples n ∧
    LegEndpointsCoplanar (n - k 0) (n - k 1) (n - k 2) (n - k 3) }

snip begin

lemma endpoint_coplanar_iff_l_sum (l₁ l₂ l₃ l₄ : ℝ) :
    LegEndpointsCoplanar l₁ l₂ l₃ l₄ ↔ l₁ + l₃ = l₂ + l₄ := by
  dsimp [LegEndpointsCoplanar]
  set P₁ : Pt := !₂[0, 0, l₁]
  set P₂ : Pt := !₂[0, 1, l₂]
  set P₃ : Pt := !₂[1, 1, l₃]
  set P₄ : Pt := !₂[1, 0, l₄]
  let P : Finset Pt := {P₁, P₂, P₃, P₄}
  rw [coplanar_iff_finrank_le_two]
  rw [show {P₁, P₂, P₃, P₄} = (P : Set Pt) by simp [P]]
  rw [vectorSpan_eq_span_vsub_finset_right_ne ℝ
    (show P₁ ∈ P by simp [P])]
  rw [show P.erase P₁ = {P₂, P₃, P₄} by simp [P, P₁, P₂, P₃, P₄]]
  rw [image_insert, image_insert, image_singleton]
  simp only [vsub_eq_sub]
  -- Define n to be the dimension
  let n : ℕ := ?_
  change n ≤ 2 ↔ _
  have hn : n ≤ 2 ↔ 3 ≠ n := by
    have : n ≤ 3 := (finrank_span_le_card _).trans (by simp [P₂, P₃, P₄])
    omega
  rw [hn]
  -- Type cast like crazy
  let b : Fin 3 → Pt := ![P₂ - P₁, P₃ - P₁, P₄ - P₁]
  have h := linearIndependent_iff_card_eq_finrank_span (b := b) (R := ℝ)
  simp only [Fintype.card_fin] at h
  rw [show Set.range b = ({P₂ - P₁, P₃ - P₁, P₄ - P₁} : Finset Pt) by aesop] at h
  refine h.not.symm.trans ?_
  let isom := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  rw [← LinearMap.linearIndependent_iff isom.toLinearMap (by simp)]
  simp only [LinearEquiv.coe_coe]
  let A : Matrix (Fin 3) (Fin 3) ℝ := .of (isom ∘ b)
  rw [show (isom ∘ b) = A.row by rfl]
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  simp only [ne_eq, Decidable.not_not]
  -- Finally get the explicit matrix
  have hA : A = !![0, 1, l₂ - l₁; 1, 1, l₃ - l₁; 1, 0, l₄ - l₁] := by
    simp [← Matrix.ext_iff, Fin.forall_fin_succ]
    simp [A, isom, b, P₁, P₂, P₃, P₄]
  rw [hA]
  simp [Matrix.det_fin_three]
  grind

lemma endpoint_coplanar_iff_k_sum (k : Fin 4 → ℕ) (n : ℕ) :
    LegEndpointsCoplanar (n - k 0) (n - k 1) (n - k 2) (n - k 3) ↔
    k 0 + k 2 = k 1 + k 3 := by
  rw [endpoint_coplanar_iff_l_sum]
  rify
  grind

abbrev mm (n : ℕ) (s : ℕ) : ℕ := min (s + 1) (1 + 2 * n - s)
abbrev answer (n : ℕ) := (n + 1) * (2 * n ^ 2 + 4 * n + 3) / 3

-- Finset version of {0, 1, ..., n} ^ 4
def kTuplesFinset (n : ℕ) : Finset (Fin 4 → ℕ) := Fintype.piFinset (fun _ ↦ range (n + 1))

lemma k_tuple_finset_conversion (k : Fin 4 → ℕ) (n : ℕ) :
    k ∈ kTuples n ↔ k ∈ kTuplesFinset n := by
  simp [kTuples, kTuplesFinset]
  grind

-- Finset version of {0, 1, ..., n} ^ 4 filtered by equal sum
def kTuplesFinsetCoplanar (n : ℕ) : Finset (Fin 4 → ℕ) :=
  { k ∈ kTuplesFinset n | k 0 + k 2 = k 1 + k 3 }

lemma k_tuple_finset_coplanar_conversion (k : Fin 4 → ℕ) (n : ℕ) :
    k ∈ kTuplesCoplanar n ↔ k ∈ kTuplesFinsetCoplanar n := by
  simp [kTuplesCoplanar, kTuplesFinsetCoplanar, k_tuple_finset_conversion, endpoint_coplanar_iff_k_sum, kTuplesFinset]

#check card_eq_sum_card_image

lemma image_eq (n : ℕ) : image (fun k ↦ k 0 + k 2) (kTuplesFinsetCoplanar n) = range (2 * n + 1) := by
  sorry

lemma count (n : ℕ) : (kTuplesFinsetCoplanar n).card = answer n := by
  rw [card_eq_sum_card_image (fun k ↦ k 0 + k 2) (kTuplesFinsetCoplanar n)]
  sorry

lemma count_layer_pair_low {n : ℕ} {s : ℕ} (hs : s ≤ n):
    { (a,b) : ℕ × ℕ | a ≤ n ∧ b ≤ n ∧ a + b = s }.ncard = s + 1 := by
  sorry

lemma count_layer_pair_high {n : ℕ} {s : ℕ} (hs : s ≥ n):
    { (a,b) : ℕ × ℕ | a ≤ n ∧ b ≤ n ∧ a + b = s }.ncard = (2 * n + 1) - s := by
  sorry

lemma count_layer_pair (n : ℕ) (s : ℕ) :
    { (a,b) : ℕ × ℕ | a ≤ n ∧ b ≤ n ∧ a + b = s }.ncard = mm n s := by
  sorry

lemma count_layer_quadruple (n : ℕ) (s : ℕ) :
    { k | k ∈ kTuples n ∧ k 0 + k 2 = s ∧ k 1 + k 3 = s }.ncard = (mm n s) ^ 2 := by
  sorry

lemma sum_count (n : ℕ) : ∑ s ∈ range (2 * n + 1), (mm n s) ^ 2 = answer n := by
  sorry

snip end

determine solution : ℕ → ℕ := fun n ↦ answer n

problem usa2005_p4 (n : ℕ) :
    (kTuplesCoplanar n).ncard = (solution n) := by
  sorry

end Usa2005P4
