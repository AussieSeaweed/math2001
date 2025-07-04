/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

#eval F 5 -- infoview displays `8`


#check @F -- infoview displays `F : ℕ → ℤ`


def q (x : ℝ) : ℝ := x + 3


#check @q -- infoview displays `q : ℝ → ℝ`


#check fun (x : ℝ) ↦ x ^ 2 -- infoview displays `fun x ↦ x ^ 2 : ℝ → ℝ`


example : Injective q := by
  dsimp [Injective]
  intro x1 x2 h
  dsimp [q] at h
  addarith [h]


example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Injective]
  push_neg
  use -1, 1
  constructor
  · numbers
  · numbers


def s (a : ℚ) : ℚ := 3 * a + 2

example : Surjective s := by
  dsimp [Surjective]
  intro y
  use (y - 2) / 3
  calc s ((y - 2) / 3) = 3 * ((y - 2) / 3) + 2 := by rw [s]
    _ = y := by ring


example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro x
  apply ne_of_gt
  calc -1 < 0 := by numbers
    _ ≤ x ^ 2 := by extra


inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer


def f : Musketeer → Musketeer
  | athos => aramis
  | porthos => aramis
  | aramis => athos


example : ¬ Injective f := by
  dsimp [Injective]
  push_neg
  use athos, porthos
  dsimp [f] -- optional
  exhaust


example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a
  · exhaust
  · exhaust
  · exhaust


-- better (more automated) version of the previous proof
example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a <;> exhaust


def g : Musketeer → Musketeer
  | athos => porthos
  | porthos => aramis
  | aramis => athos


example : Injective g := by
  dsimp [Injective]
  intro x1 x2 hx
  cases x1 <;> cases x2 <;> exhaust


example : Surjective g := by
  dsimp [Surjective]
  intro y
  cases y
  · use aramis
    exhaust
  · use athos
    exhaust
  · use porthos
    exhaust



example : Injective (fun (x:ℝ) ↦ x ^ 3) := by
  intro x1 x2 hx
  dsimp at hx
  have H : (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = 0
  · calc (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = x1 ^ 3 - x2 ^ 3 := by ring
      _ = x1 ^ 3 - x1 ^ 3 := by rw [hx]
      _ = 0 := by ring
  rw [mul_eq_zero] at H
  obtain H1 | H2 := H
  · -- case 1: x1 - x2 = 0
    addarith [H1]
  · -- case 2: x1 ^2 + x1 * x2 + x2 ^ 2  = 0
    by_cases hx1 : x1 = 0
    · -- case 2a: x1 = 0
      have hx2 :=
      calc x2 ^ 3 = x1 ^ 3 := by rw [hx]
        _ = 0 ^ 3 := by rw [hx1]
        _ = 0 := by numbers
      cancel 3 at hx2
      calc x1 = 0 := by rw [hx1]
        _ = x2 := by rw [hx2]
    · -- case 2b: x1 ≠ 0
      have :=
      calc 0 < x1 ^ 2 + ((x1 + x2) ^ 2 + x2 ^ 2) := by extra
          _ = 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) := by ring
          _ = 2 * 0 := by rw [H2]
          _ = 0 := by ring
      numbers at this -- contradiction!

/-! # Exercises -/


example : Injective (fun (x : ℚ) ↦ x - 12) := by
  dsimp [Injective]
  intro x1 x2 h
  addarith [h]

-- example : ¬ Injective (fun (x : ℚ) ↦ x - 12) := by
--   sorry


-- example : Injective (fun (x : ℝ) ↦ 3) := by
--   sorry

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 0, 1
  constructor
  · numbers
  · numbers

example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x1 x2 h
  calc
    x1
      = ((3 * x1 - 1) + 1) / 3 := by ring
    _ = ((3 * x2 - 1) + 1) / 3 := by rw [h]
    _ = x2 := by ring

-- example : ¬ Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
--   sorry


example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x1 x2 h1
  have h2 :=
    calc
      3 * x1
        = 3 * x1 - 1 + 1 := by ring
      _ = 3 * x2 - 1 + 1 := by rw [h1]
      _ = 3 * x2 := by ring
  cancel 3 at h2

-- example : ¬ Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
--   sorry


example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp [Surjective]
  intro y
  use y / 2
  ring

-- example : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
--   sorry


-- example : Surjective (fun (x : ℤ) ↦ 2 * x) := by
--   sorry

example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  dsimp [Surjective]
  push_neg
  use 1
  intro x
  obtain h | h := le_or_succ_le x 0
  · apply ne_of_lt
    addarith [h]
  · apply ne_of_gt
    calc
      1 < 2 * 1 := by numbers
      _ ≤ 2 * x := by rel [h]

-- example : Surjective (fun (n : ℕ) ↦ n ^ 2) := by
--   sorry

example : ¬ Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  dsimp [Surjective]
  push_neg
  use 2
  intro x
  obtain h | h := le_or_succ_le x 1
  · apply ne_of_lt
    calc
      x ^ 2
        ≤ 1 ^ 2 := by rel [h]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      2 < 2 ^ 2 := by numbers
      _ ≤ x ^ 2 := by rel [h]

inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

-- example : Injective h := by
--   sorry

example : ¬ Injective h := by
  dsimp [Injective]
  push_neg
  use athos, aramis
  exhaust

example : Surjective h := by
  dsimp [Surjective]
  intro y
  cases y
  · use porthos
    exhaust
  · use athos
    exhaust

-- example : ¬ Surjective h := by
--   sorry


def l : White → Musketeer
  | meg => aramis
  | jack => porthos

example : Injective l := by
  dsimp [Injective]
  intro x1 x2 h
  cases x1 <;> cases x2 <;> exhaust

-- example : ¬ Injective l := by
--   sorry


-- example : Surjective l := by
--   sorry

example : ¬ Surjective l := by
  dsimp [Surjective]
  push_neg
  use athos
  intro x
  cases x <;> exhaust

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  dsimp [Injective]
  constructor
  · intro h1
    intro x1 x2 h2
    by_cases h3 : f x1 = f x2
    · push_neg at h3
      have : x1 = x2 := by apply h1 h3
      contradiction
    · apply h3
  · intro h1
    intro x1 x2 h2
    by_cases h3 : x1 = x2
    · apply h3
    · push_neg at h3
      have : f x1 ≠ f x2 := by apply h1 x1 x2 h3
      contradiction

example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  dsimp [Injective]
  intro f h1 x1 x2 h2
  apply h1
  addarith [h2]

-- example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
--   sorry


-- example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
--   sorry

example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  dsimp [Injective]
  push_neg
  use fun x ↦ -x
  constructor
  · intro x1 x2 h
    addarith [h]
  · use -1, 1
    constructor <;> numbers

-- example : ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
--   sorry

example : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  dsimp [Surjective]
  push_neg
  use fun x ↦ x
  constructor
  · intro x
    use x
    ring
  · use 1
    intro x
    obtain h | h := le_or_succ_le x 0
    · apply ne_of_lt
      addarith [h]
    · apply ne_of_gt
      calc
        1 < 2 * 1 := by numbers
        _ ≤ 2 * x := by rel [h]

-- example : ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
--   sorry

example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  dsimp [Surjective]
  push_neg
  use 0, 1
  intro x
  have h : 0 * x = 0 := by ring
  rw [h]
  numbers

example {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  dsimp [Injective]
  intro x y h1
  obtain h2 | h2 | h2 := lt_trichotomy x y
  · have : f x ≠ f y
    · apply ne_of_lt
      apply hf
      apply h2
    contradiction
  · apply h2
  · have : f x ≠ f y
    · apply ne_of_gt
      apply hf
      apply h2
    contradiction

example {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp [Surjective]
  intro y
  simple_induction y with k IH
  · use x0
    apply h0
  · obtain ⟨x, h1⟩ := IH
    use i x
    rw [← h1]
    apply hi
