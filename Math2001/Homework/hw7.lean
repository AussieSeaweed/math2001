/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init


/-! # Homework 7

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-7,
for clearer statements and any special instructions. -/


@[autograded 5]
theorem problem1 (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro h
    by_cases hq : Q
    · have : P → Q
      · intro
        apply hq
      contradiction
    · by_cases hp : P
      · constructor
        · apply hp
        · apply hq
      · have : P → Q
        · intro
          contradiction
        contradiction
  · intro ⟨hp, _⟩ h
    have : Q := h hp
    contradiction

@[autograded 3]
theorem problem2 : ¬ (∀ x : ℚ, 2 * x ^ 2 ≥ x) := by
  push_neg
  use 1 / 4
  numbers

@[autograded 4]
theorem problem3 (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k IH
  · left
    numbers
  · obtain h | h := IH
    · right
      calc
        6 ^ (k + 1)
          = 6 * 6 ^ k := by ring
        _ ≡ 6 * 1 [ZMOD 7] := by rel [h]
        _ = 6 := by numbers
    · left
      calc
        6 ^ (k + 1)
          = 6 * 6 ^ k := by ring
        _ ≡ 6 * 6 [ZMOD 7] := by rel [h]
        _ = 1 + 7 * 5 := by numbers
        _ ≡ 1 [ZMOD 7] := by extra

@[autograded 4]
theorem problem4 (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with k IH
  · left
    numbers
  · obtain h | h | h := IH
    · right
      right
      calc
        4 ^ (k + 1)
          = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 7] := by rel [h]
        _ = 4 := by numbers
    · left
      calc
        4 ^ (k + 1)
          = 4 * 4 ^ k := by ring
        _ ≡ 4 * 2 [ZMOD 7] := by rel [h]
        _ = 1 + 7 * 1 := by numbers
        _ ≡ 1 [ZMOD 7] := by extra
    · right
      left
      calc
        4 ^ (k + 1)
          = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 7] := by rel [h]
        _ = 2 + 7 * 2 := by numbers
        _ ≡ 2 [ZMOD 7] := by extra

@[autograded 5]
theorem problem5 {a : ℝ} (ha : -1 ≤ a) : ¬ ∃ n : ℕ, (1 + a) ^ n < 1 + n * a := by
  push_neg
  intro n
  simple_induction n with k IH
  · apply ge_of_eq
    ring
  · have h : a ≤ a * (1 + a) ^ k
    · have h' : ∀ m, a ≤ a * (1 + a) ^ m
      · intro m
        simple_induction m with k2 IH2
        · apply ge_of_eq
          ring
        · have : 1 + a ≥ 0 := by addarith [ha]
          calc
            a ≤ a * (1 + a) ^ k2 := by rel [IH2]
            _ ≤ a * (1 + a) ^ k2 + a ^ 2 * (1 + a) ^ k2 := by extra
            _ = a * (1 + a) ^ (k2 + 1) := by ring
      apply h'
    calc
      1 + (k + 1) * a
        = (1 + k * a) + a := by ring
      _ ≤ (1 + a) ^ k + a := by rel [IH]
      _ ≤ (1 + a) ^ k + a * (1 + a) ^ k := by rel [h]
      _ = (1 + a) ^ (k + 1) := by ring

@[autograded 4]
theorem problem6 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · calc
      (3:ℤ) ^ (k + 1)
        = 3 * (3 ^ k) := by ring
      _ ≥ 3 * (2 ^ k + 100) := by rel [IH]
      _ = 2 ^ (k + 1) + 2 ^ k + 100 + 200 := by ring
      _ ≥ 2 ^ (k + 1) + 2 ^ k + 100 := by extra
      _ ≥ 2 ^ (k + 1) + 100 := by extra
