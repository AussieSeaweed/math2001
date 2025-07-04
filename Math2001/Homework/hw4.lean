/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs
import AutograderLib

math2001_init

open Int

/-! # Homework 4

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-4,
for clearer statements and any special instructions. -/

@[autograded 5]
theorem problem1 (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain ⟨k, h⟩ | ⟨k, h⟩ := even_or_odd n
  · use 6 * k ^ 2 + 3 * k - 1
    calc
      3 * n ^ 2 + 3 * n - 1
        = 3 * (2 * k) ^ 2 + 3 * (2 * k) - 1 := by rw [h]
      _ = 2 * (6 * k ^ 2 + 3 * k - 1) + 1 := by ring
  · use 6 * k ^ 2 + 9 * k + 2
    calc
      3 * n ^ 2 + 3 * n - 1
        = 3 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 1 := by rw [h]
      _ = 2 * (6 * k ^ 2 + 9 * k + 2) + 1 := by ring

@[autograded 1]
theorem problem2 : (8 : ℤ) ∣ 96 := by
  use 12
  numbers

@[autograded 2]
theorem problem3 : ¬(8 : ℤ) ∣ -55 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -7
  constructor <;> numbers

@[autograded 4]
theorem problem4 {a b c : ℤ} (hab : a ^ 3 ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 6 ∣ c := by
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hbc
  use m ^ 2 * n
  rw [hn, hm]
  ring

@[autograded 1]
theorem problem5 : 31 ≡ 13 [ZMOD 3] := by
  use 6
  numbers

@[autograded 2]
theorem problem6 : ¬ 51 ≡ 62 [ZMOD 5] := by
  intro h
  have : (5:ℤ) ∣ (51 - 62) := h
  have : ¬ (5:ℤ) ∣ (51 - 62)
  · apply Int.not_dvd_of_exists_lt_and_lt
    use -3
    constructor <;> numbers
  contradiction

@[autograded 5]
theorem problem7 (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  obtain ⟨k, hk⟩ := h
  use k * (a ^ 2 + a * b + b ^ 2)
  calc
    a ^ 3 - b ^ 3
      = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
    _ = (n * k) * (a ^ 2 + a * b + b ^ 2) := by rw [hk]
    _ = n * (k * (a ^ 2 + a * b + b ^ 2)) := by ring

@[autograded 5]
theorem problem8 (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  use (u + v)
  calc
    a - c
      = (a - b) + (b - c) := by ring
    _ = (n * u) + (n * v) := by rw [hu, hv]
    _ = n * (u + v) := by ring
