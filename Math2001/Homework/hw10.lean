/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option quotPrecheck false


/-! # Homework 10

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-10,
for clearer statements and any special instructions. -/


/- Problem 1: prove one of these, delete the other -/

@[autograded 4]
theorem problem1a : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 6 * n ^ 2 ≥ 4 * n } := by
  dsimp [Set.subset_def]
  intro m h
  calc
    m ^ 3 - 6 * m ^ 2
      = m * m ^ 2 - 6 * m ^ 2 := by ring
    _ ≥ 10 * m ^ 2 - 6 * m ^ 2 := by rel [h]
    _ = 4 * m * m := by ring
    _ ≥ 4 * 10 * m := by rel [h]
    _ = 4 * m + 36 * m := by ring
    _ ≥ 4 * m := by extra

-- @[autograded 4]
-- theorem problem1b : { m : ℤ | m ≥ 10 } ⊈ { n : ℤ | n ^ 3 - 6 * n ^ 2 ≥ 4 * n } := by
--   sorry


/- Problem 2: prove one of these, delete the other -/

-- @[autograded 3]
-- theorem problem2a : { t : ℝ | t ^ 2 - 3 * t + 2 = 0 } = { s : ℝ | s = 2 } := by
--   sorry

@[autograded 3]
theorem problem2b : { t : ℝ | t ^ 2 - 3 * t + 2 = 0 } ≠ { s : ℝ | s = 2 } := by
  ext
  dsimp
  push_neg
  use 1
  left
  constructor <;> numbers


/- Problem 3: prove one of these, delete the other -/

@[autograded 3]
theorem problem3a : {1, 2, 3} ∩ {2, 3, 4} ⊆ {2, 3, 6} := by
  dsimp [Set.subset_def]
  intro x ⟨h1, h2⟩
  obtain h1 | h1 | h1 := h1
  · obtain h2 | h2 | h2 := h2 <;>
    · rw [h1] at h2
      numbers at h2
  · obtain h2 | h2 | h2 := h2
    · left
      apply h1
    · rw [h1] at h2
      numbers at h2
    · rw [h1] at h2
      numbers at h2
  · obtain h2 | h2 | h2 := h2
    · rw [h1] at h2
      numbers at h2
    · right
      left
      apply h1
    · rw [h1] at h2
      numbers at h2


-- @[autograded 3]
-- theorem problem3b : ¬ {1, 2, 3} ∩ {2, 3, 4} ⊆ {2, 3, 6} := by
--   sorry


/- Problem 4 -/

@[autograded 4]
theorem problem4 : { r : ℤ | r ≡ 11 [ZMOD 15] }
    = { s : ℤ | s ≡ 2 [ZMOD 3] } ∩ { t : ℤ | t ≡ 1 [ZMOD 5] } := by
  ext r
  dsimp
  constructor
  · intro ⟨k, h⟩
    constructor
    · use 5 * k + 3
      calc
        r - 2
          = (r - 11) + 9 := by ring
        _ = 15 * k + 9 := by rw [h]
        _ = 3 * (5 * k + 3) := by ring
    · use 3 * k + 2
      calc
        r - 1
          = (r - 11) + 10 := by ring
        _ = 15 * k + 10 := by rw [h]
        _ = 5 * (3 * k + 2) := by ring
  · intro ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩
    use 2 * k1 - 3 * k2
    calc
      r - 11
        = 10 * (r - 2) - 9 * (r - 1) := by ring
      _ = 10 * (3 * k1) - 9 * (5 * k2) := by rw [h1, h2]
      _ = 15 * (2 * k1 - 3 * k2) := by ring



/-! ### Problem 5 starts here -/


local infix:50 "∼" => fun (a b : ℤ) ↦ ∃ m n, m > 0 ∧ n > 0 ∧ a * m = b * n


/- Problem 5.1: prove one of these, delete the other -/

@[autograded 2]
theorem problem51a : Reflexive (· ∼ ·) := by
  intro
  use 1, 1
  constructor
  · numbers
  · constructor
    · numbers
    · ring

-- @[autograded 2]
-- theorem problem51b : ¬ Reflexive (· ∼ ·) := by
--   sorry


/- Problem 5.2: prove one of these, delete the other -/

@[autograded 2]
theorem problem52a : Symmetric (· ∼ ·) := by
  intro _ _ ⟨m, n, ⟨hm, hn, h⟩⟩
  dsimp
  use n, m
  constructor
  · apply hn
  · constructor
    · apply hm
    · rw [h]

-- @[autograded 2]
-- theorem problem52b : ¬ Symmetric (· ∼ ·) := by
--   sorry


/- Problem 5.3: prove one of these, delete the other -/

-- @[autograded 2]
-- theorem problem53a : AntiSymmetric (· ∼ ·) := by
--   sorry

@[autograded 2]
theorem problem53b : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1, 2
  constructor
  · use 2, 1
    constructor
    · numbers
    · constructor <;> numbers
  · constructor
    · use 1, 2
      constructor
      · numbers
      · constructor <;> numbers
    · numbers


/- Problem 5.4: prove one of these, delete the other -/

@[autograded 2]
theorem problem54a : Transitive (· ∼ ·) := by
  intro x y z ⟨m1, n1, ⟨hm1, hn1, h1⟩⟩ ⟨m2, n2, ⟨hm2, hn2, h2⟩⟩
  use m1 * m2, n1 * n2
  constructor
  · calc
      m1 * m2
        > 0 * 0 := by rel [hm1, hm2]
      _ = 0 := by numbers
  · constructor
    · calc
        n1 * n2
          > 0 * 0 := by rel [hn1, hn2]
        _ = 0 := by numbers
    · calc
        x * (m1 * m2)
          = (x * m1) * m2 := by ring
        _ = (y * n1) * m2 := by rw [h1]
        _ = (y * m2) * n1 := by ring
        _ = (z * n2) * n1 := by rw [h2]
        _ = z * (n1 * n2) := by ring

-- @[autograded 2]
-- theorem problem54b : ¬ Transitive (· ∼ ·) := by
--   sorry



/-! ### Problem 6 starts here -/

infix:50 "≺" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)


/- Problem 6.1: prove one of these, delete the other -/

@[autograded 2]
theorem problem61a : Reflexive (· ≺ ·) := by
  intro
  constructor <;>
  · apply ge_of_eq
    ring

-- @[autograded 2]
-- theorem problem61b : ¬ Reflexive (· ≺ ·) := by
--   sorry


/- Problem 6.2: prove one of these, delete the other -/

-- @[autograded 2]
-- theorem problem62a : Symmetric (· ≺ ·) := by
--   sorry

@[autograded 2]
theorem problem62b : ¬ Symmetric (· ≺ ·) := by
  dsimp [Symmetric]
  push_neg
  use (0, 0), (1, 1)
  constructor
  · constructor <;> numbers
  · left
    numbers


/- Problem 6.3: prove one of these, delete the other -/

@[autograded 2]
theorem problem63a : AntiSymmetric (· ≺ ·) := by
  intro _ _ ⟨h1x, h1y⟩ ⟨h2x, h2y⟩
  constructor
  · apply le_antisymm
    apply h1x
    apply h2x
  · apply le_antisymm
    apply h1y
    apply h2y

-- @[autograded 2]
-- theorem problem63b : ¬ AntiSymmetric (· ≺ ·) := by
--   sorry


/- Problem 6.4: prove one of these, delete the other -/

@[autograded 2]
theorem problem64a : Transitive (· ≺ ·) := by
  intro _ _ _ ⟨h12x, h12y⟩ ⟨h23x, h23y⟩
  constructor
  · addarith [h12x, h23x]
  · addarith [h12y, h23y]

-- @[autograded 2]
-- theorem problem64b : ¬ Transitive (· ≺ ·) := by
--   sorry
