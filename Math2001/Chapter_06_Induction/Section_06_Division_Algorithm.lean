/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs
import Mathlib.Data.Real.Basic
import Library.Tactic.ModEq

math2001_init


def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d


#eval fmod 11 4 -- infoview displays `3`
#eval fdiv 11 4 -- infoview displays `2`


theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by _ n d => 2 * n - d



theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by _ n d hd => 2 * n - d


theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by _ n d hd => 2 * n - d


example (a b : ℤ) (h : 0 < b) : ∃ r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · apply fmod_nonneg_of_pos a h
  constructor
  · apply fmod_lt_of_pos a h
  · use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]

/-! # Exercises -/


theorem lt_fmod_of_neg (n : ℤ) {d : ℤ} (hd : d < 0) : d < fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · apply lt_fmod_of_neg (n + d) hd
  · apply lt_fmod_of_neg (n - d) hd
  · apply hd
  · have h4 :=
      calc
        -d * 0
          = 0 := by ring
        _ ≥ d * (n - d) := by rel [h2]
        _ = -d * (d - n) := by ring
    have h5 : 0 < -d := by addarith [hd]
    cancel -d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply Ne.symm
      apply h3
termination_by _ n d hd => 2 * n - d

def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

theorem T_eq (n : ℤ) : T n = n ^ 2 := by
  rw [T]
  split_ifs with h1 h2 <;> push_neg at *
  · rw [T_eq (1 - n)]
    ring
  · rw [T_eq (-n)]
    ring
  · have h2 : n ≥ 0 := by addarith [h2]
    have h4 : n = 0 := le_antisymm h1 h2
    calc
      0 = 0 ^ 2 := by numbers
      _ = n ^ 2 := by rw [h4]
termination_by _ n => 3 * n - 1

theorem uniqueness (a b : ℤ) (h : 0 < b) {r s : ℤ}
    (hr : 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
    (hs : 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b]) : r = s := by
  obtain ⟨hr1, hr2, ⟨m, hr3⟩⟩ := hr
  obtain ⟨hs1, hs2, ⟨n, hs3⟩⟩ := hs
  have h2 : n = m
  · obtain h2 | h2 := le_or_succ_le (m - n) 0
    · obtain h3 | h3 := le_or_succ_le (n - m) 0
      · have : m - n ≥ 0 := by addarith [h3]
        interval_cases h4 : m - n
        · addarith [h4]
      · have :=
          calc
            r - s
              < b - s := by rel [hr2]
            _ ≤ b - 0 := by rel [hs1]
            _ = b := by ring
        have : ¬r - s < b
        · push_neg
          calc
            r - s
              = a - s - (a - r) := by ring
            _ = b * n - b * m := by rw [hs3, hr3]
            _ = b * (n - m) := by ring
            _ ≥ b * 1 := by rel [h3]
            _ = b := by ring
        contradiction
    · have :=
        calc
          s - r
            < b - r := by rel [hs2]
          _ ≤ b - 0 := by rel [hr1]
          _ = b := by ring
      have : ¬s - r < b
      · push_neg
        calc
          s - r
            = a - r - (a - s) := by ring
          _ = b * m - b * n := by rw [hr3, hs3]
          _ = b * (m - n) := by ring
          _ ≥ b * 1 := by rel [h2]
          _ = b := by ring
      contradiction
  calc
    r = -(a - r) + a := by ring
    _ = -(b * m) + a := by rw [hr3]
    _ = -(b * n) + a := by rw [h2]
    _ = -(a - s) + a := by rw [hs3]
    _ = s := by ring

example (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · rw [fmod]
    split_ifs with h1 h2 h3 <;> push_neg at *
    · constructor
      · apply fmod_nonneg_of_pos (a + b) h
      · constructor
        · apply fmod_lt_of_pos (a + b) h
        · have h2 : fmod (a + b) b + b * fdiv (a + b) b = a + b := fmod_add_fdiv (a + b) b
          calc
            a ≡ a + b * 1 [ZMOD b] := by extra
            _ = a + b := by ring
            _ = fmod (a + b) b + b * fdiv (a + b) b := by rw [h2]
            _ ≡ fmod (a + b) b [ZMOD b] := by extra
    · constructor
      · apply fmod_nonneg_of_pos (a - b) h
      · constructor
        · apply fmod_lt_of_pos (a - b) h
        · have h3 : fmod (a - b) b + b * fdiv (a - b) b = a - b := fmod_add_fdiv (a - b) b
          calc
            a ≡ a + b * -1 [ZMOD b] := by extra
            _ = a - b := by ring
            _ = fmod (a - b) b + b * fdiv (a - b) b := by rw [h3]
            _ ≡ fmod (a - b) b [ZMOD b] := by extra
    · constructor
      · numbers
      · constructor
        · apply h
        · use 1
          rw [h3]
          ring
    · constructor
      · cancel b at h1
      · constructor
        · apply Ne.lt_of_le
          exact h3
          have h4 :=
            calc
              b * (a - b)
                ≤ 0 := by rel [h2]
              _ = b * 0 := by ring
          cancel b at h4
          addarith [h4]
        · use 0
          ring
  · intro c hc
    apply uniqueness a b h
    exact hc
    constructor
    · apply fmod_nonneg_of_pos a h
    · constructor
      · apply fmod_lt_of_pos a h
      · use fdiv a b
        have hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
        addarith [hab]
