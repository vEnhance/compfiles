/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

import Mathlib.Tactic
import Mathlib.Data.Int.ModEq

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2015, Problem 5

-/

namespace Usa2015P5

snip begin
-- This is the solution at https://web.evanchen.cc/exams/USAMO-2015-notes.pdf

lemma pe_bound {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a ^ 4 + b ^ 4 < (a * c + b * d) ^ 5 := by
  calc
    a ^ 4 + b ^ 4 ≤ a * a ^ 4 + b * b ^ 4 := by
      have : a ^ 4 ≤ a * a ^ 4 := by simp_all; exact ha
      have : b ^ 4 ≤ b * b ^ 4 := by simp_all; exact hb
      linarith
    _ = a ^ 5 + b ^ 5 := by ring
    _ < (a + b) ^ 5 := by ring; simp_all
    _ ≤ (a * c + b * d) ^ 5 := by
      rw [Nat.pow_le_pow_iff_left (show 5 ≠ 0 by omega)]
      nlinarith [show 1 ≤ c by omega, show 1 ≤ d by omega]

lemma mod_divis_Z {a b c d e : ℤ}
    (h1 : a ^ 4 + b ^ 4 = e ^ 5) (h2 : c ^ 4 + d ^ 4 = e ^ 5) :
    (a * c + b * d) ∣ (e ^ 5 * (a - d) * (a + d) * (a ^ 2 + d ^ 2)) := by
  calc
    a * c + b * d ∣ (a * c) ^ 4 - (b * d) ^ 4 := by
      rw [show (a * c) ^ 4 - (b * d) ^ 4
        = (a * c + b * d) * ((a * c - b * d) * (a^2 * c^2 + b^2 * d^2)) by ring]
      exact Int.dvd_mul_right (a * c + b* d) _
    _ = a^4 * c^4 - d^4 * b^4 := by ring
    _ = a^4 * (e^5 - d^4) - d^4 * (e^5 - a^4) := by
      nth_rewrite 1 [← h2]
      nth_rewrite 1 [← h1]
      ring
    _ = _ := by ring

lemma mod_divis_N {a b c d e : ℕ}
    (h1 : a ^ 4 + b ^ 4 = e ^ 5) (h2 : c ^ 4 + d ^ 4 = e ^ 5) :
    (a * c + b * d) ∣ (e ^ 5 * ((a : ℤ) - (d : ℤ)).natAbs * (a + d) * (a ^ 2 + d ^ 2)) := by
  zify at h1
  zify at h2
  convert mod_divis_Z h1 h2
  sorry

lemma main {a b c d e : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (h1 : a ^ 4 + b ^ 4 = e ^ 5) (h2 : c ^ 4 + d ^ 4 = e ^ 5) :
    ¬ Nat.Prime (a * c + b * d) := by
  set p : ℕ := a * c + b * d
  by_contra
  have p_large : e < p := by
    apply (Nat.pow_lt_pow_iff_left (show 5 ≠ 0 by omega)).mp
    calc
      e ^ 5 = a ^ 4 + b ^ 4 := by exact h1.symm
      _ < (a * c + b * d) ^ 5 := by exact pe_bound ha hb hc hd
      _ = p ^ 5 := by trivial
  have h := mod_divis_N h1 h2
  sorry

lemma stupid {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    1 < a * c + b * d := by
  have hac : 0 < a * c := by positivity
  have hbd : 0 < b * d := by positivity
  omega

snip end

problem usa2015_p5 {a b c d e : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (h1 : a ^ 4 + b ^ 4 = e ^ 5) (h2 : c ^ 4 + d ^ 4 = e ^ 5) :
    1 < a * c + b * d ∧ ¬ Nat.Prime (a * c + b * d) := by
  constructor
  · exact stupid ha hb hc hd
  · exact main ha hb hc hd he h1 h2

end Usa2015P5
