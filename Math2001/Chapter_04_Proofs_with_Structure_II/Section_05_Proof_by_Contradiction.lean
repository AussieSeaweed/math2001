/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
      calc
        13
          = 3 * k := hk
        _ ≥ 3 * 5 := by rel [h5]
    numbers at h 

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n, hn⟩ := h
  obtain hn2 | hn2 := le_or_succ_le n 1
  · have :=
      calc
        2 = n ^ 2 := by rw [hn]
        _ ≤ 1 ^ 2 := by rel [hn2]
    numbers at this
  · have :=
      calc
        2 = n ^ 2 := by rw [hn]
        _ ≥ 2 ^ 2 := by rel [hn2]
    numbers at this

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro h1 h2
    rw [Int.odd_iff_modEq] at h1
    rw [Int.even_iff_modEq] at h2
    have :=
      calc
        1 ≡ n [ZMOD 2] := by rel [h1]
        _ ≡ 0 [ZMOD 2] := by rel [h2]
    numbers at this
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · apply h2

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
      calc
        (1:ℤ)
          = 1 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h
  · have h :=
      calc
        1 ≡ 1 + 3 * 1 [ZMOD 3] := by extra
        _ ≡ 2 ^ 2 [ZMOD 3] := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  have h2 :=
  calc
    b * q
      < a := by rel [hq₁]
    _ = b * k := by rw [hk]
  cancel b at h2
  have : ¬k < q + 1
  · apply not_lt_of_le
    apply h2
  contradiction

example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · use m
    calc
      p = m * l := by rw [hl]
      _ = l * m := by ring
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · have :=
      calc
        T * l
          ≤ m * l := by rel [hmT]
        _ = p := by rw [hl]
        _ < T ^ 2 := by rel [hTp]
        _ = T * T := by ring
    cancel T at this
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  obtain ⟨t, h1, h2⟩ := h
  have :=
    calc
      4 ≥ t := by rel [h1]
      _ ≥ 5 := by rel [h2]
  numbers at this

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro h
  obtain ⟨a, h1, h2⟩ := h
  have :=
    calc
      8 ^ 3
        ≥ (a ^ 2) ^ 3 := by rel [h1]
      _ = (a ^ 3) ^ 2 := by ring
      _ ≥ 30 ^ 2 := by rel [h2]
  numbers at this

example : ¬ Int.Even 7 := by
  intro h
  obtain ⟨k, hk⟩ := h
  obtain h' | h' := le_or_succ_le k 3
  · have :=
      calc
        2 * 3
          ≥ 2 * k := by rel [h']
        _ = 7 := by rw [hk]
    numbers at this
  · have :=
      calc
        2 * 4
          ≤ 2 * k := by rel [h']
        _ = 7 := by rw [hk]
    numbers at this

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  have hn : n = 4 := by addarith [hn]
  intro h
  obtain ⟨h1, h2⟩ := h
  have :=
    calc
      4 ^ 2
        = n ^ 2 := by rw [hn]
      _ = 10 := by rw [h2]
  numbers at this

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  have hx' : -3 < x ∧ x < 3
  · apply abs_lt_of_sq_lt_sq'
    addarith [hx]
    numbers
  obtain ⟨hx1, hx2⟩ := hx'
  intro h
  obtain h' | h' := h
  · have :=
      calc
        -3
          < x := by rel [hx1]
        _ ≤ -3 := by rel [h']
    numbers at this
  · have :=
      calc
        3 ≤ x := by rel [h']
        _ < 3 := by rel [hx2]
    numbers at this

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro h
  obtain ⟨N, h⟩ := h
  obtain hN | hN := even_or_odd N
  · obtain ⟨i, hi⟩ := hN
    have hN2 : Nat.Even (N + 1)
    · apply h
      addarith []
    obtain ⟨j, hj⟩ := hN2
    have hN2' : Int.Even (N + 1)
    · use j
      addarith [hj]
    rw [Int.even_iff_modEq] at hN2'
    have hN3 : Int.Odd (N + 1)
    · use i
      rw [hi]
    rw [Int.odd_iff_modEq] at hN3
    have :=
      calc
        0 ≡ N + 1 [ZMOD 2] := by rel [hN2']
        _ ≡ 1 [ZMOD 2] := by rel [hN3]
    numbers at this
  · obtain ⟨i, hi⟩ := hN
    have hN2 : Nat.Even (N + 2)
    · apply h
      addarith []
    obtain ⟨j, hj⟩ := hN2
    have hN2' : Int.Even (N + 2)
    · use j
      addarith [hj]
    rw [Int.even_iff_modEq] at hN2'
    have hN3 : Int.Odd (N + 2)
    · use i + 1
      calc
        N + 2
          = 2 * i + 1 + 2 := by rw [hi]
        _ = 2 * (i + 1) + 1 := by ring
    rw [Int.odd_iff_modEq] at hN3
    have :=
      calc
        0 ≡ N + 2 [ZMOD 2] := by rel [hN2']
        _ ≡ 1 [ZMOD 2] := by rel [hN3]
    numbers at this

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro h
  mod_cases hn : n % 4
  · have :=
      calc
        0 ≡ 0 ^ 2 [ZMOD 4] := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
        _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at this
  · have :=
      calc
        1 ≡ 1 ^ 2 [ZMOD 4] := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
        _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at this
  · have :=
      calc
        0 ≡ 0 + 4 * 1 [ZMOD 4] := by extra
        _ ≡ 2 ^ 2 [ZMOD 4] := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
        _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at this
  · have :=
      calc
        1 ≡ 1 + 4 * 2 [ZMOD 4] := by extra
        _ ≡ 3 ^ 2 [ZMOD 4] := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
        _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at this

example : ¬ Prime 1 := by
  intro h
  obtain ⟨h1, h2⟩ := h
  numbers at h1

example : Prime 97 := by
  apply better_prime_test (T := 10)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 48
    constructor <;> numbers
  · use 32
    constructor <;> numbers
  · use 24
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 16
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 12
    constructor <;> numbers
  · use 10
    constructor <;> numbers
