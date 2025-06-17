/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · intro h1
    intro h2
    obtain ⟨h3, h4⟩ := h2
    obtain h5 | h5 := h1
    · contradiction
    · contradiction

example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=
  calc ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
      ↔ ∃ n : ℤ, ¬(∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_forall]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬(n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_exists]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬n ^ 2 < m ∨ ¬m < (n + 1) ^ 2 := by rel [not_and_or]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by rel [not_lt]

#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc n ^ 2
        ≥ 2 ^ 2 := by rel [hn]
      _ > 2 := by numbers

/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  · intro h1
    by_cases h2 : P
    · apply h2
    · contradiction
  · intro h1 h2
    contradiction

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro h1
    have h2 : ¬Q
    · intro h3
      have : P → Q
      · intro h4
        apply h3
      contradiction
    constructor
    · by_cases h3 : P
      · apply h3
      · have : P → Q
        · intro h4
          contradiction
        contradiction
    · apply h2
  · intro ⟨h1, h2⟩ h3
    have : Q := by apply h3 h1
    contradiction

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro h1
    by_cases h2 : ∃x, ¬P x
    · apply h2
    · have h3 :=
        calc
          (¬∃ x, ¬P x)
            ↔ ∀ x, ¬¬P x := by rel [not_exists]
          _ ↔ ∀ x, P x := by rel [not_not]
      obtain ⟨h4, h5⟩ := h3
      have : ∀ x, P x
      · apply h4
        apply h2
      contradiction
  · intro ⟨a, h1⟩ h3
    have : P a := by apply h3 a
    contradiction

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by
  calc
    (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
      ↔ ∃ a : ℤ, ¬ (∀ b : ℤ, a * b = 1 → a = 1 ∨ b = 1) := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, ¬ (a * b = 1 → a = 1 ∨ b = 1) := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ ¬ (a = 1 ∨ b = 1) := by rel [not_imp]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by rel [not_or]

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) := by
  calc
    (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x)
      ↔ ∀ x : ℝ, ¬ (∀ y : ℝ, y ≤ x) := by rel [not_exists]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, ¬y ≤ x := by rel [not_forall]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, y > x := by rel [not_le]

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by
  calc
    ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5)
      ↔ ∀ m : ℤ, ¬ ∀ n : ℤ, m = n + 5 := by rel [not_exists]
    _ ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by rel [not_forall]

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  numbers

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  obtain h1 | h1 := le_or_lt t 4
  · obtain h2 | h2 := lt_or_le t 5
    · right
      apply h2
    · have :=
        calc
          5 ≤ t := by rel [h2]
          _ ≤ 4 := by rel [h1]
      numbers at this
  · left
    apply h1

example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  intro k
  obtain h | h := le_or_succ_le k 3
  · apply ne_of_gt
    calc
      2 * k
        ≤ 2 * 3 := by rel [h]
      _ < 7 := by numbers
  · apply ne_of_lt
    calc
      7 < 2 * 4 := by numbers
      _ ≤ 2 * k := by rel [h]

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  right
  use k
  constructor
  · apply hk
  · constructor
    · apply hk1
    · apply hkp

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use 2 * a ^ 2
  calc
    2 * a ^ 3
      < 2 * a ^ 3 + 7 := by extra
    _ = 2 * a ^ 2 * a + 7 := by ring

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    have : Prime p
    · dsimp [Prime]
      constructor
      · apply hp2
      · dsimp [Prime] at hp
        push_neg at hp
        obtain hp | hp := hp
        · have :=
            calc
              2 ≤ p := by rel [hp2]
              _ < 2 := by rel [hp]
          numbers at this
        · obtain ⟨m, ⟨hm1, hm2, hm3⟩⟩ := hp
          have hp3 :=
            calc
              0 < 2 := by numbers
              _ ≤ p := by rel [hp2]
          have hm2 : 1 < m
          · apply Ne.lt_of_le'
            apply hm2
            apply Nat.pos_of_dvd_of_pos hm1 hp3
          have hm3 : m < p
          · apply Ne.lt_of_le
            apply hm3
            apply Nat.le_of_dvd hp3
            apply hm1
          have : ¬ ∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p
          · push_neg
            use m
            constructor
            · apply hm2
            · constructor
              · apply hm3
              · apply hm1
          contradiction
    contradiction
  push_neg at H
  apply H
