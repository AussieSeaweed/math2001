/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import AutograderLib

math2001_init

open Nat

/-! # Homework 3

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-3,
for clearer statements and any special instructions. -/

@[autograded 2]
theorem problem1 {a b : ℚ} (h : a = 3 - b) : a + b = 3 ∨ a + b = 4 := by
  left
  addarith [h]

@[autograded 5]
theorem problem2 {t : ℚ} (h : t ^ 2 + t - 6 = 0) : t = 2 ∨ t = -3 := by
  have h :=
    calc
      (t - 2) * (t + 3)
        = t ^ 2 + t - 6 := by ring
      _ = 0 := by rw [h]
  obtain h | h := eq_zero_or_eq_zero_of_mul_eq_zero h
  · left
    addarith [h]
  · right
    addarith [h]

@[autograded 3]
theorem problem3 : ∃ a b : ℕ, a ≠ 0 ∧ 2 ^ a = 5 * b + 1 := by
  use 4, 3
  constructor <;> numbers

@[autograded 5]
theorem problem4 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1 / 2
  calc
    (x + 1 / 2) ^ 2
      = x ^ 2 + x + 1 / 4 := by ring
    _ ≥ x + 1 / 4 := by extra
    _ > x := by extra

@[autograded 5]
theorem problem5 {x : ℕ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨k, hx⟩ := hx
  use 4 * k ^ 3 + 6 * k ^ 2 + 3 * k
  calc
    x ^ 3
      = (2 * k + 1) ^ 3 := by rw [hx]
    _ = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by ring

@[autograded 5]
theorem problem6 (n : ℕ) : ∃ m ≥ n, Odd m := by
  obtain h | h := even_or_odd n
  · use n + 1
    constructor
    · extra
    · obtain ⟨k, h⟩ := h
      use k
      addarith [h]
  · use n
    constructor
    · apply ge_of_eq
      ring
    · apply h
