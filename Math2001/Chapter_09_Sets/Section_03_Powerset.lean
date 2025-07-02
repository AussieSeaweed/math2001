/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Tactic.Exhaust

math2001_init

open Set Function


#check {3, 4, 5} -- `{3, 4, 5} : Set ℕ`
#check {n : ℕ | 8 < n} -- `{n | 8 < n} : Set ℕ`
#check {k : ℕ | ∃ a, a ^ 2 = k} -- `{k | ∃ a, a ^ 2 = k} : Set ℕ`


#check {{3, 4}, {4, 5, 6}} -- `{{3, 4}, {4, 5, 6}} : Set (Set ℕ)`
#check {s : Set ℕ | 3 ∈ s} -- `{s | 3 ∈ s} : Set (Set ℕ)`
#check {{{}, {0, 1, 2}}, {}, {{3, 4}, {5, 6, 7, 8}}, {{9}}}



example : {n : ℕ | Nat.Even n} ∉ {s : Set ℕ | 3 ∈ s} := by
  dsimp
  rw [← Nat.odd_iff_not_even]
  use 1
  numbers


def p (s : Set ℕ) : Set ℕ := {n : ℕ | n + 1 ∈ s}

#check @p -- `p : Set ℕ → Set ℕ`


example : ¬ Injective p := by
  dsimp [Injective, p]
  push_neg
  use {0}, ∅
  dsimp
  constructor
  · ext x
    dsimp
    suffices x + 1 ≠ 0 by exhaust
    apply ne_of_gt
    extra
  · ext
    push_neg
    use 0
    dsimp
    exhaust


def q (s : Set ℤ) : Set ℤ := {n : ℤ | n + 1 ∈ s}

example : Injective q := by
  dsimp [Injective, q]
  intro s t hst
  ext k
  have hk : k - 1 ∈ {n | n + 1 ∈ s} ↔ k - 1 ∈ {n | n + 1 ∈ t} := by rw [hst]
  dsimp at hk
  conv at hk => ring
  apply hk



example : ¬ ∃ f : X → Set X, Surjective f := by
  intro h
  obtain ⟨f, hf⟩ := h
  let s : Set X := {x | x ∉ f x}
  obtain ⟨x, hx⟩ := hf s
  by_cases hxs : x ∈ s
  · have hfx : x ∉ f x := hxs
    rw [hx] at hfx
    contradiction
  · have hfx : ¬ x ∉ f x := hxs
    rw [hx] at hfx
    contradiction

/-! # Exercises -/


def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬ Injective r := by
  dsimp [Injective]
  push_neg
  use {}, {3}
  constructor
  · dsimp [r]
    ext x
    constructor <;>
    · dsimp
      exhaust
  · ext
    push_neg
    dsimp
    use 3
    exhaust

namespace Int

def U : ℕ → Set ℤ
  | 0 => univ
  | n + 1 => {x : ℤ | ∃ y ∈ U n, x = 2 * y}

example (n : ℕ) : U n = {x : ℤ | (2:ℤ) ^ n ∣ x} := by
  simple_induction n with k hk
  · rw [U]
    ext x
    constructor
    · intro
      use x
      ring
    · intro
      dsimp
  · rw [U]
    ext x
    dsimp
    constructor
    · intro ⟨y, ⟨h1, h2⟩⟩
      rw [hk] at h1
      obtain ⟨z, h3⟩ := h1
      use z
      rw [h2]
      rw [h3]
      ring
    · intro ⟨y, h⟩
      use 2 ^ k * y
      constructor
      · rw [hk]
        use y
        ring
      · rw [h]
        ring
