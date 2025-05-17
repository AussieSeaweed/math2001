/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc
      p ^ 2 ≤ 9 := by addarith [hp]
      _ = 3 ^ 2 := by numbers
    numbers
  obtain ⟨hp1, hp2⟩ := hp'
  addarith [hp1]

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0
  · apply le_antisymm
    calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    extra
  cancel 2 at h2
  have h3 :=
    calc
      b ^ 2
        = -a ^ 2 := by addarith [h1]
      _ = -0 ^ 2 := by rw [h2]
      _ = 0 := by numbers
  cancel 2 at h3
  constructor
  apply h2
  apply h3

/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨H1, H2⟩ := H
  calc
    2 * a + b
      = a + (a + b) := by ring
    _ ≤ 1 + 3 := by rel [H1, H2]
    _ = 4 := by numbers

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨H1, H2⟩ := H
  calc
    2 * r
      = (r + s) + (r - s) := by ring
    _ ≤ 1 + 5 := by rel [H1, H2]
    _ = 6 := by numbers

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨H1, H2⟩ := H
  calc
    m = (m + 5) - 5 := by ring
    _ ≤ n - 5 := by rel [H2]
    _ ≤ 8 - 5 := by rel [H1]
    _ = 3 := by numbers

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have hp' : p ≥ 7 := by addarith [hp]
  constructor
  calc
    p ^ 2
      ≥ 7 ^ 2 := by rel [hp']
    _ = 49 := by numbers
  apply hp'

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have h' : a ≥ 6 := by addarith [h]
  constructor
  apply h'
  calc
    3 * a
      ≥ 3 * 6 := by rel [h']
    _ ≥ 10 := by numbers

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  constructor
  calc
    x = 2 * (x + y) - (x + 2 * y) := by ring
    _ = 2 * 5 - 7 := by rw [h1, h2]
    _ = 3 := by numbers
  calc
    y = (x + 2 * y) - (x + y) := by ring
    _ = 7 - 5 := by rw [h1, h2]
    _ = 2 := by numbers

example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  have h3 :=
    calc
      a = (a * b) := by rw [h1]
      _ = b := by rw [h2]
  have h4 :=
    calc
      a * (a - 1)
        = a * a - a := by ring
      _ = a * a - a * b := by rw [h1]
      _ = a * b - a * b := by rw [h3]
      _ = 0 := by ring
  have h5 := eq_zero_or_eq_zero_of_mul_eq_zero h4
  obtain h6 | h6 := h5
  left
  constructor
  · apply h6
  · calc
      b = a * b := by rw [h2]
      _ = a * a := by rw [h3]
      _ = 0 * 0 := by rw [h6]
      _ = 0 := by numbers
  right
  constructor
  · addarith [h6]
  · calc
      b = a * b := by rw [h2]
      _ = a * a := by rw [h3]
      _ = (a - 1) ^ 2 + 2 * (a - 1) + 1 := by ring
      _ = 0 ^ 2 + 2 * 0 + 1 := by rw [h6]
      _ = 1 := by numbers
