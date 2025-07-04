/- Copyright (c) Heather Macbeth, 2024.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

macro_rules | `(tactic| gcongr_discharger) => `(tactic| numbers)
math2001_init

namespace Nat

/-! # Homework 8

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-8,
for clearer statements and any special instructions. -/


def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

@[autograded 4]
theorem problem1 (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  match n with
  | 0 =>
    rw [B]
    numbers
  | n + 1 =>
    have IH := problem1 n
    calc
      B (n + 1)
        = (B n + (n + 1) ^ 2) := by rw [B]
      _ = n * (n + 1) * (2 * n + 1) / 6 + (n + 1) ^ 2 := by rw [IH]
      _ = (n + 1) * ((n + 1) + 1) * (2 * (n + 1) + 1) / 6 := by ring
      _ = (n + 1:ℕ) * ((n + 1:ℕ) + 1) * (2 * (n + 1:ℕ) + 1) / 6 := by norm_cast


def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

@[autograded 4]
theorem problem2 (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  match n with
  | 0 =>
    rw [S]
    numbers
  | n + 1 =>
    have IH := problem2 n
    calc
      S (n + 1)
        = S n + 1 / 2 ^ (n + 1) := by rw [S]
      _ = 2 - 1 / 2 ^ n + 1 / 2 ^ (n + 1) := by rw [IH]
      _ = 2 - 1 / 2 ^ (n + 1) := by ring


def a : ℕ → ℤ
  | 0 => 4
  | n + 1 => 3 * a n - 5

@[autograded 4]
theorem problem3 : forall_sufficiently_large (n : ℕ), a n ≥ 10 * 2 ^ n := by
  use 5
  intro n hn
  induction_from_starting_point n, hn with k IH1 IH2
  · dsimp [a]
    numbers
  · calc
      a (k + 1)
        = 3 * a k - 5 := by rw [a]
      _ ≥ 3 * (10 * 2 ^ k) - 5 := by rel [IH2]
      _ = 10 * 2 ^ (k + 1) + 5 * (2 ^ (k + 1) - 1) := by ring
      _ ≥ 10 * 2 ^ (k + 1) + 5 * (2 ^ (5 + 1) - 1) := by rel [IH1]
      _ ≥ 10 * 2 ^ (k + 1) := by extra


def c : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c n

@[autograded 4]
theorem problem4 (n : ℕ) : c n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [c]
    numbers
  · rw [c]
    numbers
  · calc
      c (k + 1 + 1)
        = 4 * c k := by rw [c]
      _ = 4 * (2 * 2 ^ k + (-2) ^ k) := by rw [IH1]
      _ = 2 * 2 ^ (k + 1 + 1) + (-2) ^ (k + 1 + 1) := by ring


def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

@[autograded 4]
theorem problem5 (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  · rw [q]
    numbers
  · rw [q]
    numbers
  · calc
      q (k + 1 + 1)
        = 2 * q (k + 1) - q k + 6 * k + 6 := by rw [q]
      _ = 2 * ((k + 1) ^ 3 + 1) - (k ^ 3 + 1) + 6 * k + 6 := by rw [IH1, IH2]
      _ = (k + 1 + 1) ^ 3 + 1 := by ring


@[autograded 5]
theorem problem6 (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  match n with
  | 1 =>
    use 0, 1
    constructor
    · use 0
      numbers
    · numbers
  | n + 1 + 1 =>
    obtain ⟨k, hk⟩ | ⟨k, hk⟩ := even_or_odd n
    · have hk2 :=
        calc
          0 < n + 1 + 1 := by rel [hn]
          _ = 2 * k + 1 + 1 := by rw [hk]
          _ = 2 * (k + 1) := by ring
      cancel 2 at hk2
      have ⟨a, x, ⟨hx, h⟩⟩ := problem6 (k + 1) hk2
      use a + 1, x
      constructor
      · apply hx
      · calc
          n + 1 + 1
            = (2 * k) + 1 + 1 := by rw [hk]
          _ = 2 * (k + 1) := by ring
          _ = 2 * (2 ^ a * x) := by rw [h]
          _ = 2 ^ (a + 1) * x := by ring
    · use 0, n + 2
      constructor
      · use k + 1
        rw [hk]
        ring
      · ring
