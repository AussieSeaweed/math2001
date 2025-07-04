/- Copyright (c) Heather Macbeth, 2024.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 2

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-2,
for clearer statements and any special instructions. -/


@[autograded 5]
theorem problem1 {x : ℚ} (h1 : x ^ 2 = 9) (h2 : 1 < x) : x = 3 := by
  have h3 :=
    calc
      (x - 3) * (x + 3)
        = x ^ 2 - 9 := by ring
      _ = 9 - 9 := by rw [h1]
      _ = 0 := by numbers
  obtain h3 | h3 := eq_zero_or_eq_zero_of_mul_eq_zero h3
  · addarith [h3]
  · have :=
      calc
        1 < x := by rel [h2]
        _ = x + 3 - 3 := by ring
        _ = 0 - 3 := by rw [h3]
        _ = -3 := by numbers
    numbers at this

@[autograded 5]
theorem problem2 {s : ℚ} (h1 : 3 * s ≤ -15) (h2 : 2 * s ≥ -10) : s = -5 := by
  apply le_antisymm
  · calc
      s = 3 * s / 3 := by ring
      _ ≤ -15 / 3 := by rel [h1]
      _ = -5 := by numbers
  · calc
      s = 2 * s / 2 := by ring
      _ ≥ -10 / 2 := by rel [h2]
      _ = -5 := by numbers

@[autograded 4]
theorem problem3 {t : ℚ} (h : t = 2 ∨ t = -3) : t ^ 2 + t - 6 = 0 := by
  obtain h | h := h <;>
  · rw [h]
    numbers

@[autograded 5]
theorem problem4 {x : ℤ} : 3 * x ≠ 10 := by
  obtain h | h := le_or_succ_le x 3
  · apply ne_of_lt
    calc
      3 * x
        ≤ 3 * 3 := by rel [h]
      _ < 10 := by numbers
  · apply ne_of_gt
    calc
      3 * x
        ≥ 3 * 4 := by rel [h]
      _ > 10 := by numbers

@[autograded 6]
theorem problem5 {x y : ℝ} (h1 : 2 ≤ x ∨ 2 ≤ y) (h2 : x ^ 2 + y ^ 2 = 4) :
    x ^ 2 * y ^ 2 = 0 := by
  obtain h1 | h1 := h1
  · have h2 : y ^ 2 = 0
    · apply le_antisymm
      calc
        y ^ 2
          = (x ^ 2 + y ^ 2) - x ^ 2 := by ring
        _ = 4 - x ^ 2 := by rw [h2]
        _ ≤ 4 - 2 ^ 2 := by rel [h1]
        _ = 0 := by numbers
      extra
    rw [h2]
    ring
  · have h2 : x ^ 2 = 0
    · apply le_antisymm
      calc
        x ^ 2
          = (x ^ 2 + y ^ 2) - y ^ 2 := by ring
        _ = 4 - y ^ 2 := by rw [h2]
        _ ≤ 4 - 2 ^ 2 := by rel [h1]
        _ = 0 := by numbers
      extra
    rw [h2]
    ring
