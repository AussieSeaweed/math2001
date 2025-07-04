/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

/-! # Homework 6

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-6,
for clearer statements and any special instructions. -/

@[autograded 4]
theorem problem1 : ¬ (∃ t : ℝ, t ≤ 5 ∧ 2 * t ≥ 12) := by
  intro ⟨t, ⟨h1, h2⟩⟩
  have :=
    calc
      12
        ≤ 2 * t := by rel [h2]
      _ ≤ 2 * 5 := by rel [h1]
  numbers at this

@[autograded 3]
theorem problem2 : ¬ (∃ x : ℝ, ∀ y : ℝ, y ≤ x) := by
  intro ⟨x, h⟩
  have h2 : 1 + x ≤ x := h (1 + x)
  have :=
    calc
      1 = 1 + x - x := by ring
      _ ≤ x - x := by rel [h2]
      _ ≤ 0 := by ring
  numbers at this

@[autograded 3]
theorem problem3 (a : ℚ) : 3 * a + 2 < 11 ↔ a < 3 := by
  constructor
  · intro h
    calc
      a = ((3 * a + 2) - 2) / 3 := by ring
      _ < (11 - 2) / 3 := by rel [h]
      _ = 3 := by numbers
  · intro h
    calc
      3 * a + 2
        < 3 * 3 + 2 := by rel [h]
      _ = 11 := by numbers

@[autograded 6]
theorem problem4 (t : ℤ) : t ^ 2 + t + 3 ≡ 0 [ZMOD 5] ↔ t ≡ 1 [ZMOD 5] ∨ t ≡ 3 [ZMOD 5] := by
  constructor
  · intro h1
    mod_cases h2 : t % 5
    · have :=
        calc
          0 ≡ t ^ 2 + t + 3 [ZMOD 5] := by rel [h1]
          _ ≡ 0 ^ 2 + 0 + 3 [ZMOD 5] := by rel [h2]
          _ = 3 := by numbers
      numbers at this
    · left
      apply h2
    · have :=
        calc
          0 ≡ t ^ 2 + t + 3 [ZMOD 5] := by rel [h1]
          _ ≡ 2 ^ 2 + 2 + 3 [ZMOD 5] := by rel [h2]
          _ = 4 + 5 * 1 := by numbers
          _ ≡ 4 [ZMOD 5] := by extra
      numbers at this
    · right
      apply h2
    · have :=
        calc
          0 ≡ t ^ 2 + t + 3 [ZMOD 5] := by rel [h1]
          _ ≡ 4 ^ 2 + 4 + 3 [ZMOD 5] := by rel [h2]
          _ = 3 + 5 * 4 := by numbers
          _ ≡ 3 [ZMOD 5] := by extra
      numbers at this
  · intro h
    obtain h | h := h
    · calc
        t ^ 2 + t + 3
          ≡ 1 ^ 2 + 1 + 3 [ZMOD 5] := by rel [h]
        _ = 0 + 5 * 1 := by numbers
        _ ≡ 0 [ZMOD 5] := by extra
    · calc
        t ^ 2 + t + 3
          ≡ 3 ^ 2 + 3 + 3 [ZMOD 5] := by rel [h]
        _ = 0 + 5 * 3 := by numbers
        _ ≡ 0 [ZMOD 5] := by extra

@[autograded 4]
theorem problem5 (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) := by
  constructor <;>
  · intro ⟨h1, h2⟩
    constructor
    · apply h2
    · apply h1

@[autograded 5]
theorem problem6 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro ⟨⟨x, hp⟩, hq⟩
    use x
    constructor
    · apply hp
    · apply hq
  · intro ⟨x, ⟨hp, hq⟩⟩
    constructor
    · use x
      apply hp
    · apply hq
