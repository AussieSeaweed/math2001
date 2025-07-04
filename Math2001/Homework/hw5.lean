/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init

/-! # Homework 5

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-5,
for clearer statements and any special instructions. -/

@[autograded 2]
theorem problem1 : ∃ k : ℤ, k > 10 ∧ 3 * k ≡ 2 [ZMOD 5] ∧ k ∣ 72 := by
  use 24
  constructor
  · numbers
  · constructor
    · use 14
      numbers
    · use 3
      numbers

@[autograded 3]
theorem problem2 {a : ℤ} (ha : a ≡ 4 [ZMOD 5]) :
    a ^ 3 + 2 * a ^ 2 + 3 ≡ 4 [ZMOD 5] := by
  calc
    a ^ 3 + 2 * a ^ 2 + 3
      ≡ 4 ^ 3 + 2 * 4 ^ 2 + 3 [ZMOD 5] := by rel [ha]
    _ = 4 + 5 * 19 := by numbers
    _ ≡ 4 [ZMOD 5] := by extra

@[autograded 5]
theorem problem3 {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases h : x % 5
  · calc
      x ^ 5
        ≡ 0 ^ 5 [ZMOD 5] := by rel [h]
      _ = 0 := by numbers
      _ ≡ x [ZMOD 5] := by rel [h]
  · calc
      x ^ 5
        ≡ 1 ^ 5 [ZMOD 5] := by rel [h]
      _ = 1 := by numbers
      _ ≡ x [ZMOD 5] := by rel [h]
  · calc
      x ^ 5
        ≡ 2 ^ 5 [ZMOD 5] := by rel [h]
      _ = 2 + 5 * 6 := by numbers
      _ ≡ 2 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [h]
  · calc
      x ^ 5
        ≡ 3 ^ 5 [ZMOD 5] := by rel [h]
      _ = 3 + 5 * 48 := by numbers
      _ ≡ 3 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [h]
  · calc
      x ^ 5
        ≡ 4 ^ 5 [ZMOD 5] := by rel [h]
      _ = 4 + 5 * 204 := by numbers
      _ ≡ 4 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [h]

@[autograded 3]
theorem problem4 {a : ℚ} (h : ∀ b : ℚ, a + b ^ 2 ≥ 0) : a ≥ 0 := by
  calc
    a = a + 0 ^ 2 := by ring
    _ ≥ 0 := h 0

@[autograded 5]
theorem problem5 (n : ℕ) (h : ∀ a : ℕ, 6 ≤ a → a ≤ 10 → a ∣ n) :
    ∀ b : ℕ, 1 ≤ b → b ≤ 5 → b ∣ n := by
  intro b hb1 hb2
  interval_cases hb : b
  · use n
    ring
  · have h : 6 ∣ n
    · apply h 6
      numbers
      numbers
    have ⟨k, h⟩ := h
    use 3 * k
    rw [h]
    ring
  · have h : 6 ∣ n
    · apply h 6
      numbers
      numbers
    have ⟨k, h⟩ := h
    use 2 * k
    rw [h]
    ring
  · have h : 8 ∣ n
    · apply h 8
      numbers
      numbers
    have ⟨k, h⟩ := h
    use 2 * k
    rw [h]
    ring
  · have h : 10 ∣ n
    · apply h 10
      numbers
      numbers
    have ⟨k, h⟩ := h
    use 2 * k
    rw [h]
    ring

@[autograded 3]
theorem problem6 : ∃ a : ℝ, ∀ b : ℝ, a ≤ b ^ 2 := by
  use 0
  intro
  extra

@[autograded 4]
theorem problem7 : forall_sufficiently_large x : ℝ, x ^ 3 - 5 * x ≥ 11 * x ^ 2 := by
  dsimp
  use 12
  intro x h
  calc
    x ^ 3 - 5 * x
      = x * x ^ 2 - 5 * x := by ring
    _ ≥ 12 * x ^ 2 - 5 * x := by rel [h]
    _ = 11 * x ^ 2 + x * x - 5 * x := by ring
    _ ≥ 11 * x ^ 2 + 12 * x - 5 * x := by rel [h]
    _ = 11 * x ^ 2 + 7 * x := by ring
    _ ≥ 11 * x ^ 2 := by extra
