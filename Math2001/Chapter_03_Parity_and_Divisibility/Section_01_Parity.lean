/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc
    7 * n - 4
      = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + 3 * b + a + 1
  calc
    x * y + 2 * y
      = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2 * a * b + 3 * b + a + 1) + 1 := by ring

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨t, ht⟩ := hm
  use 3 * t - 1
  calc
    3 * m - 5
      = 3 * (2 * t + 1) - 5 := by rw [ht]
    _ = 2 * (3 * t - 1) := by ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨x, hx⟩ := hn
  use 2 * x ^ 2 + 2 * x - 3
  calc
    n ^ 2 + 2 * n - 5
      = (2 * x) ^ 2 + 2 * (2 * x) - 5 := by rw [hx]
    _ = 2 * (2 * x ^ 2 + 2 * x - 3) + 1 := by ring

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  use -5
  numbers

example : Even (26 : ℤ) := by
  use 13
  numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  use a + b
  calc
    n + m
      = (2 * b) + (2 * a + 1) := by rw [ha, hb]
    _ = 2 * (a + b) + 1 := by ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  use a - b - 2
  calc
    p - q - 4
      = (2 * a + 1) - (2 * b) - 4 := by rw [ha, hb]
    _ = 2 * (a - b - 2) + 1 := by ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  use 3 * i + j - 1
  calc
    3 * a + b - 3
      = 3 * (2 * i) + (2 * j + 1) - 3 := by rw [hi, hj]
    _ = 2 * (3 * i + j - 1) := by ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := hs
  use 3 * a - 5 * b - 1
  calc
    3 * r - 5 * s
      = 3 * (2 * a + 1) - 5 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (3 * a - 5 * b - 1) := by ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨y, hy⟩ := hx
  use 4 * y ^ 3 + 6 * y ^ 2 + 3 * y
  calc
    x ^ 3
      = (2 * y + 1) ^ 3 := by rw [hy]
    _ = 2 * (4 * y ^ 3 + 6 * y ^ 2 + 3 * y) + 1 := by ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨x, hx⟩ := hn
  use 2 * x ^ 2 - x
  calc
    n ^ 2 - 3 * n + 2
      = (2 * x + 1) ^ 2 - 3 * (2 * x + 1) + 2 := by rw [hx]
    _ = 2 * (2 * x ^ 2 - x) := by ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨x, hx⟩ := ha
  use 2 * x ^ 2 + 4 * x - 1
  calc
    a ^ 2 + 2 * a - 4
      = (2 * x + 1) ^ 2 + 2 * (2 * x + 1) - 4 := by rw [hx]
    _ = 2 * (2 * x ^ 2 + 4 * x - 1) + 1 := by ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨x, hx⟩ := hp
  use 2 * x ^ 2 + 5 * x - 1
  calc
    p ^ 2 + 3 * p - 5
      = (2 * x + 1) ^ 2 + 3 * (2 * x + 1) - 5 := by rw [hx]
    _ = 2 * (2 * x ^ 2 + 5 * x - 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + b
  calc
    x * y
      = (2 * a + 1) * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2 * a * b + a + b) + 1 := by ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 6 * x ^ 2 + 3 * x - 1
    calc
      3 * n ^ 2 + 3 * n - 1
        = 3 * (2 * x) ^ 2 + 3 * (2 * x) - 1 := by rw [hx]
      _ = 2 * (6 * x ^ 2 + 3 * x - 1) + 1 := by ring
  · obtain ⟨x, hx⟩ := hn
    use 6 * x ^ 2 + 9 * x + 2
    calc
      3 * n ^ 2 + 3 * n - 1
        = 3 * (2 * x + 1) ^ 2 + 3 * (2 * x + 1) - 1 := by rw [hx]
      _ = 2 * (6 * x ^ 2 + 9 * x + 2) + 1 := by ring

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  obtain hn | hn := Int.even_or_odd n
  · use n + 1
    constructor
    · extra
    · obtain ⟨x, hx⟩ := hn
      use x
      rw [hx]
  · use n
    constructor
    · extra
    · obtain ⟨x, hx⟩ := hn
      use x
      rw [hx]
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha | ha := Int.even_or_odd a
  · obtain ⟨x, hx⟩ := ha
    obtain hb | hb := Int.even_or_odd b
    · obtain ⟨y, hy⟩ := hb
      left
      use x - y
      calc
        a - b
          = (2 * x) - (2 * y) := by rw [hx, hy]
        _ = 2 * (x - y) := by ring
    · obtain ⟨y, hy⟩ := hb
      obtain hc | hc := Int.even_or_odd c
      · obtain ⟨z, hz⟩ := hc
        right
        left
        use x + z
        calc
          a + c
            = (2 * x) + (2 * z) := by rw [hx, hz]
          _ = 2 * (x + z) := by ring
      · obtain ⟨z, hz⟩ := hc
        right
        right
        use y - z
        calc
          b - c
            = (2 * y + 1) - (2 * z + 1) := by rw [hy, hz]
          _ = 2 * (y - z) := by ring
  · obtain ⟨x, hx⟩ := ha
    obtain hb | hb := Int.even_or_odd b
    · obtain ⟨y, hy⟩ := hb
      obtain hc | hc := Int.even_or_odd c
      · obtain ⟨z, hz⟩ := hc
        right
        right
        use y - z
        calc
          b - c
            = (2 * y) - (2 * z) := by rw [hy, hz]
          _ = 2 * (y - z) := by ring
      · obtain ⟨z, hz⟩ := hc
        right
        left
        use x + z + 1
        calc
          a + c
            = (2 * x + 1) + (2 * z + 1) := by rw [hx, hz]
          _ = 2 * (x + z + 1) := by ring
    · obtain ⟨y, hy⟩ := hb
      left
      use x - y
      calc
        a - b
          = (2 * x + 1) - (2 * y + 1) := by rw [hx, hy]
        _ = 2 * (x - y) := by ring
