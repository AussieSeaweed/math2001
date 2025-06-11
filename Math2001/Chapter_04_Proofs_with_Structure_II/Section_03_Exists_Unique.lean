/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  constructor
  · intro y hy1 hy2
    have hy3 : (y - 2) ^ 2 ≤ 1 ^ 2
    · apply sq_le_sq'
      addarith [hy1]
      addarith [hy2]
    addarith [hy3]
  intro y hy1
  have hy2 : (1 - y) ^ 2 ≤ 1
  · apply hy1
    numbers
    numbers
  have hy3 : (3 - y) ^ 2 ≤ 1
  · apply hy1
    numbers
    numbers
  have hy4 : (y - 2) ^ 2 = 0
  · apply le_antisymm
    calc
      (y - 2) ^ 2
        = (((1 - y) ^ 2) + ((3 - y) ^ 2) - 2) / 2 := by ring
      _ ≤ (1 + 1 - 2) / 2 := by rel [hy2, hy3]
      _ = 0 := by numbers
    apply sq_nonneg
  cancel 2 at hy4
  addarith [hy4]

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  constructor
  · numbers
  intro y hy
  calc
    y = ((4 * y - 3) + 3) / 4 := by ring
    _ = (9 + 3) / 4 := by rw [hy]
    _ = 3 := by numbers

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  constructor
  · apply Nat.zero_le
  intro y hy1
  apply le_antisymm
  apply hy1
  apply Nat.zero_le

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 3
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      3 * q
        = 11 - r := by rw [hr3]
      _ ≤ 11 - 0 := by rel [hr1]
      _ < 3 * 4 := by numbers
  cancel 3 at this
  have :=
    calc
      3 * q
        = 11 - r := by rw [hr3]
      _ > 11 - 3 := by rel [hr2]
      _ > 3 * 2 := by numbers
  cancel 3 at this
  interval_cases q
  addarith [hr3]
