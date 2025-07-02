/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

open Set



example (t : ℝ) : t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} := by
  dsimp
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]


example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · sorry
    · sorry
  · sorry


example : {2, 1} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  exhaust


example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  dsimp [Set.subset_def]
  intro t h
  obtain ⟨(h1 | h1), h2⟩ := h
  · have :=
    calc (-2) ^ 2 = t ^ 2 := by rw [h1]
      _ = 9 := by rw [h2]
    numbers at this
  · addarith [h1]


example : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  interval_cases n <;> exhaust


namespace Int
example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := by
  ext n
  dsimp
  rw [odd_iff_not_even]
end Int


example (x : ℤ) : x ∉ ∅ := by
  dsimp
  exhaust

example (U : Set ℤ) : ∅ ⊆ U := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := hx
    have :=
    calc 1 ≡ x [ZMOD 5] := by rel [hx1]
      _ ≡ 2 [ZMOD 5] := by rel [hx2]
    numbers at this
  · intro hx
    contradiction


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  suffices ¬(x ≡ 1 [ZMOD 5] ∧ x ≡ 2 [ZMOD 5]) by exhaust
  intro hx
  obtain ⟨hx1, hx2⟩ := hx
  have :=
  calc 1 ≡ x [ZMOD 5] := by rel [hx1]
    _ ≡ 2 [ZMOD 5] := by rel [hx2]
  numbers at this


example (x : ℤ) : x ∈ univ := by dsimp

example (U : Set ℤ) : U ⊆ univ := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} = univ := by
  ext t
  dsimp
  suffices -1 < t ∨ t < 1 by exhaust
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]

/-! # Exercises -/


macro "check_equality_of_explicit_sets" : tactic => `(tactic| (ext; dsimp; exhaust))


example : {-1, 2, 4, 4} ∪ {3, -2, 2} = {-2, -1, 2, 3, 4} := by check_equality_of_explicit_sets

example : {0, 1, 2, 3, 4} ∩ {0, 2, 4, 6, 8} = {0, 2, 4} := by
  check_equality_of_explicit_sets

example : {1, 2} ∩ {3} = ∅ := by check_equality_of_explicit_sets

example : {3, 4, 5}ᶜ ∩ {1, 3, 5, 7, 9} = {1, 7, 9} := by
  check_equality_of_explicit_sets

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intro r ⟨k, h⟩
  constructor
  · use 5 * k + 3
    calc
      r - 1
        = (r - 7) + 6 := by ring
      _ = (10 * k) + 6 := by rw [h]
      _ = 2 * (5 * k + 3) := by ring
  · use 2 * k + 1
    calc
      r - 2
        = (r - 7) + 5 := by ring
      _ = (10 * k) + 5 := by rw [h]
      _ = 5 * (2 * k + 1) := by ring

example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp [Set.subset_def]
  intro n ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  use 2 * a - 3 * b
  calc
    n = 16 * n - 15 * n := by ring
    _ = 16 * (5 * a) - 15 * n := by rw [ha]
    _ = 16 * (5 * a) - 15 * (8 * b) := by rw [hb]
    _ = 40 * (2 * a - 3 * b) := by ring

example :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp [Set.subset_def]
  intro n h
  obtain h1 | h1 := h
  · intro h2
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ | ⟨b, hb⟩ := Int.even_or_odd a
    · rw [hb] at ha
      have h3 : n ≡ 0 [ZMOD 6]
      · use b
        rw [ha]
        ring
      have :=
        calc
          0 ≡ 0 ^ 2 [ZMOD 6] := by numbers
          _ ≡ n ^ 2 [ZMOD 6] := by rel [h3]
          _ ≡ 1 [ZMOD 6] := by rel [h2]
      numbers at this
    · rw [hb] at ha
      have h3 : n ≡ 3 [ZMOD 6]
      · use b
        rw [ha]
        ring
      have :=
        calc
          3 ≡ 3 + 6 * 1 [ZMOD 6] := by extra
          _ ≡ 3 ^ 2 [ZMOD 6] := by numbers
          _ ≡ n ^ 2 [ZMOD 6] := by rel [h3]
          _ ≡ 1 [ZMOD 6] := by rel [h2]
      numbers at this
  · intro h2
    obtain ⟨a, ha⟩ := h1
    mod_cases h : a % 3
    · obtain ⟨b, hb⟩ := h
      have hb : a = 3 * b := by addarith [hb]
      rw [hb] at ha
      have h3 : n ≡ 0 [ZMOD 6]
      · use b
        rw [ha]
        ring
      have :=
        calc
          0 ≡ 0 ^ 2 [ZMOD 6] := by numbers
          _ ≡ n ^ 2 [ZMOD 6] := by rel [h3]
          _ ≡ 1 [ZMOD 6] := by rel [h2]
      numbers at this
    · obtain ⟨b, hb⟩ := h
      have hb : a = 3 * b + 1 := by addarith [hb]
      rw [hb] at ha
      have h3 : n ≡ 2 [ZMOD 6]
      · use b
        rw [ha]
        ring
      have :=
        calc
          4 ≡ 2 ^ 2 [ZMOD 6] := by numbers
          _ ≡ n ^ 2 [ZMOD 6] := by rel [h3]
          _ ≡ 1 [ZMOD 6] := by rel [h2]
      numbers at this
    · obtain ⟨b, hb⟩ := h
      have hb : a = 3 * b + 2 := by addarith [hb]
      rw [hb] at ha
      have h3 : n ≡ 4 [ZMOD 6]
      · use b
        rw [ha]
        ring
      have :=
        calc
          4 ≡ 4 + 6 * 2 [ZMOD 6] := by extra
          _ ≡ 4 ^ 2 [ZMOD 6] := by numbers
          _ ≡ n ^ 2 [ZMOD 6] := by rel [h3]
          _ ≡ 1 [ZMOD 6] := by rel [h2]
      numbers at this

def SizeAtLeastTwo (s : Set X) : Prop := ∃ x1 x2 : X, x1 ≠ x2 ∧ x1 ∈ s ∧ x2 ∈ s
def SizeAtLeastThree (s : Set X) : Prop :=
  ∃ x1 x2 x3 : X, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 ∧ x1 ∈ s ∧ x2 ∈ s ∧ x3 ∈ s

example {s t : Set X} (hs : SizeAtLeastTwo s) (ht : SizeAtLeastTwo t)
    (hst : ¬ SizeAtLeastTwo (s ∩ t)) :
    SizeAtLeastThree (s ∪ t) := by
  obtain ⟨a, b, hab, has, hbs⟩ := hs
  obtain ⟨c, d, hcd, hct, hdt⟩ := ht
  dsimp [SizeAtLeastTwo] at hst
  push_neg at hst
  dsimp [SizeAtLeastThree]
  obtain _ | _ | _ | _ := hst a c
  · obtain _ | _ | _ | _ := hst a d
    · exhaust
    · exhaust
    · use a, b, d
      exhaust
    · exhaust
  · use a, c, d
    exhaust
  · use a, b, c
    exhaust
  · exhaust
