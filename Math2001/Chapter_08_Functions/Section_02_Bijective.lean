/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust

math2001_init

open Function


def p (x : ℝ) : ℝ := 2 * x - 5

example : Bijective p := by
  dsimp [Bijective]
  constructor
  · dsimp [Injective]
    intro x1 x2 hx
    dsimp [p] at hx
    calc x1 = ((2 * x1 - 5) + 5) / 2 := by ring
      _ = ((2 * x2 - 5) + 5) / 2 := by rw [hx]
      _ = x2 := by ring
  · dsimp [Surjective]
    intro y
    use (y + 5) / 2
    calc p ((y + 5) / 2) = 2 * ((y + 5) / 2) - 5 := by rfl
      _ = y := by ring



def a (t : ℝ) : ℝ := t ^ 3 - t

example : ¬ Bijective a := by
  dsimp [Bijective]
  push_neg
  left
  dsimp [Injective]
  push_neg
  use 0, 1
  constructor
  · calc a 0 = 0 ^ 3 - 0 := by rfl
      _ = 1 ^ 3 - 1 := by numbers
      _ = a 1 := by rfl
  · numbers


inductive Celestial
  | sun
  | moon
  deriving DecidableEq

inductive Subatomic
  | proton
  | neutron
  | electron
  deriving DecidableEq

open Celestial Subatomic


def f : Celestial → Subatomic
  | sun => proton
  | moon => electron


example : ¬ Bijective f := by
  dsimp [Bijective]
  push_neg
  right
  dsimp [Surjective]
  push_neg
  use neutron
  intro x
  cases x <;> exhaust


example {f : X → Y} : Bijective f ↔ ∀ y, ∃! x, f x = y := by
  constructor
  · -- if `f` is bijective then `∀ y, ∃! x, f x = y`
    intro h y
    obtain ⟨h_inj, h_surj⟩ := h
    obtain ⟨x, hx⟩ := h_surj y
    use x
    dsimp
    constructor
    · apply hx
    · intro x' hx'
      apply h_inj
      calc f x' = y := by rw [hx']
        _ = f x := by rw [hx]
  · -- if `∀ y, ∃! x, f x = y` then `f` is bijective
    intro h
    constructor
    · -- `f` is injective
      intro x1 x2 hx1x2
      obtain ⟨x, hx, hx'⟩ := h (f x1)
      have hxx1 : x1 = x
      · apply hx'
        rfl
      have hxx2 : x2 = x
      · apply hx'
        rw [hx1x2]
      calc x1 = x := by rw [hxx1]
        _ = x2 := by rw [hxx2]
    · -- `f` is surjective
      intro y
      obtain ⟨x, hx, hx'⟩ := h y
      use x
      apply hx


example : ∀ f : Celestial → Celestial, Injective f → Bijective f := by
  intro f hf
  constructor
  · -- `f` is injective by assumption
    apply hf
  -- show that `f` is surjective
  match h_sun : f sun, h_moon : f moon with
  | sun, sun =>
    have : sun = moon
    · apply hf
      rw [h_sun, h_moon]
    contradiction
  | sun, moon =>
    intro y
    cases y
    · use sun
      apply h_sun
    · use moon
      apply h_moon
  | moon, sun =>
    intro y
    cases y
    · use moon
      apply h_moon
    · use sun
      apply h_sun
  | moon, moon =>
    have : sun = moon
    · apply hf
      rw [h_sun, h_moon]
    contradiction


example : ¬ ∀ f : ℕ → ℕ, Injective f → Bijective f := by
  push_neg
  use fun n ↦ n + 1
  constructor
  · -- the function is injective
    intro n1 n2 hn
    addarith [hn]
  · -- the function is not bijective
    dsimp [Bijective]
    push_neg
    right
    -- specifically, it's not surjective
    dsimp [Surjective]
    push_neg
    use 0
    intro n
    apply ne_of_gt
    extra

/-! # Exercises -/


example : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  constructor
  · dsimp [Injective]
    intro x1 x2 h
    calc
      x1
        = ((4 - 3 * x1) - 4) / -3 := by ring
      _ = ((4 - 3 * x2) - 4) / -3 := by rw [h]
      _ = x2 := by ring
  · dsimp [Surjective]
    intro y
    use (4 - y) / 3
    ring

-- example : ¬ Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
--   sorry


-- example : Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
--   sorry

example : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp [Bijective, Surjective]
  push_neg
  right
  use -2
  intro x
  apply ne_of_gt
  calc
    -2
      < -1 := by numbers
    _ ≤ -1 + (x + 1) ^ 2 := by extra
    _ = x ^ 2 + 2 * x := by ring

inductive Element
  | fire
  | water
  | earth
  | air
  deriving DecidableEq

open Element

def e : Element → Element
  | fire => earth
  | water => air
  | earth => fire
  | air => water

example : Bijective e := by
  constructor
  · dsimp [Injective]
    intro x1 x2
    cases x1 <;> cases x2 <;> exhaust
  · dsimp [Surjective]
    intro x
    cases x
    · use earth
      exhaust
    · use air
      exhaust
    · use fire
      exhaust
    · use water
      exhaust

-- example : ¬ Bijective e := by
--   sorry


example : ∀ f : Subatomic → Subatomic, Injective f → Bijective f := by
  intro f h
  constructor
  · apply h
  · match h_proton : f proton, h_neutron : f neutron, h_electron : f electron with
    | proton, proton, proton =>
      have : proton = neutron
      · apply h
        rw [h_proton]
        rw [h_neutron]
      exhaust
    | proton, proton, neutron =>
      have : proton = neutron
      · apply h
        rw [h_proton]
        rw [h_neutron]
      exhaust
    | proton, proton, electron =>
      have : proton = neutron
      · apply h
        rw [h_proton]
        rw [h_neutron]
      exhaust
    | proton, neutron, proton =>
      have : proton = electron
      · apply h
        rw [h_proton]
        rw [h_electron]
      exhaust
    | proton, neutron, neutron =>
      have : neutron = electron
      · apply h
        rw [h_neutron]
        rw [h_electron]
      exhaust
    | proton, neutron, electron =>
      intro y
      cases y
      · use proton
        exhaust
      · use neutron
        exhaust
      · use electron
        exhaust
    | proton, electron, proton =>
      have : proton = electron
      · apply h
        rw [h_proton]
        rw [h_electron]
      exhaust
    | proton, electron, neutron =>
      intro y
      cases y
      · use proton
        exhaust
      · use electron
        exhaust
      · use neutron
        exhaust
    | proton, electron, electron =>
      have : neutron = electron
      · apply h
        rw [h_neutron]
        rw [h_electron]
      exhaust
    | neutron, proton, proton =>
      have : neutron = electron
      · apply h
        rw [h_neutron]
        rw [h_electron]
      exhaust
    | neutron, proton, neutron =>
      have : proton = electron
      · apply h
        rw [h_proton]
        rw [h_electron]
      exhaust
    | neutron, proton, electron =>
      intro y
      cases y
      · use neutron
        exhaust
      · use proton
        exhaust
      · use electron
        exhaust
    | neutron, neutron, proton =>
      have : proton = neutron
      · apply h
        rw [h_proton]
        rw [h_neutron]
      exhaust
    | neutron, neutron, neutron =>
      have : proton = neutron
      · apply h
        rw [h_proton]
        rw [h_neutron]
      exhaust
    | neutron, neutron, electron =>
      have : proton = neutron
      · apply h
        rw [h_proton]
        rw [h_neutron]
      exhaust
    | neutron, electron, proton =>
      intro y
      cases y
      · use electron
        exhaust
      · use proton
        exhaust
      · use neutron
        exhaust
    | neutron, electron, neutron =>
      have : proton = electron
      · apply h
        rw [h_proton]
        rw [h_electron]
      exhaust
    | neutron, electron, electron =>
      have : neutron = electron
      · apply h
        rw [h_neutron]
        rw [h_electron]
      exhaust
    | electron, proton, proton =>
      have : neutron = electron
      · apply h
        rw [h_neutron]
        rw [h_electron]
      exhaust
    | electron, proton, neutron =>
      intro y
      cases y
      · use neutron
        exhaust
      · use electron
        exhaust
      · use proton
        exhaust
    | electron, proton, electron =>
      have : proton = electron
      · apply h
        rw [h_proton]
        rw [h_electron]
      exhaust
    | electron, neutron, proton =>
      intro y
      cases y
      · use electron
        exhaust
      · use neutron
        exhaust
      · use proton
        exhaust
    | electron, neutron, neutron =>
      have : neutron = electron
      · apply h
        rw [h_neutron]
        rw [h_electron]
      exhaust
    | electron, neutron, electron =>
      have : proton = electron
      · apply h
        rw [h_proton]
        rw [h_electron]
      exhaust
    | electron, electron, proton =>
      have : proton = neutron
      · apply h
        rw [h_proton]
        rw [h_neutron]
      exhaust
    | electron, electron, neutron =>
      have : proton = neutron
      · apply h
        rw [h_proton]
        rw [h_neutron]
      exhaust
    | electron, electron, electron =>
      have : proton = neutron
      · apply h
        rw [h_proton]
        rw [h_neutron]
      exhaust


example : ∀ f : Element → Element, Injective f → Bijective f := by
  intro f h
  constructor
  · apply h
  · match h_fire : f fire, h_water : f water, h_earth : f earth, h_air : f air with
    | fire, fire, fire, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, fire, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, fire, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, fire, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, water, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, water, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, water, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, water, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, earth, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, earth, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, earth, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, earth, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, air, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, air, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, air, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, fire, air, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | fire, water, fire, fire =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | fire, water, fire, water =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | fire, water, fire, earth =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | fire, water, fire, air =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | fire, water, water, fire =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | fire, water, water, water =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | fire, water, water, earth =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | fire, water, water, air =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | fire, water, earth, fire =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | fire, water, earth, water =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | fire, water, earth, earth =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | fire, water, earth, air =>
      intro y
      use y
      cases y <;> exhaust
    | fire, water, air, fire =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | fire, water, air, water =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | fire, water, air, earth =>
      intro y
      cases y
      · use fire
        exhaust
      · use water
        exhaust
      · use air
        exhaust
      · use earth
        exhaust
    | fire, water, air, air =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | fire, earth, fire, fire =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | fire, earth, fire, water =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | fire, earth, fire, earth =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | fire, earth, fire, air =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | fire, earth, water, fire =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | fire, earth, water, water =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | fire, earth, water, earth =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | fire, earth, water, air =>
      intro y
      cases y
      · use fire
        exhaust
      · use earth
        exhaust
      · use water
        exhaust
      · use air
        exhaust
    | fire, earth, earth, fire =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | fire, earth, earth, water =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | fire, earth, earth, earth =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | fire, earth, earth, air =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | fire, earth, air, fire =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | fire, earth, air, water =>
      intro y
      cases y
      · use fire
        exhaust
      · use air
        exhaust
      · use water
        exhaust
      · use earth
        exhaust
    | fire, earth, air, earth =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | fire, earth, air, air =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | fire, air, fire, fire =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | fire, air, fire, water =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | fire, air, fire, earth =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | fire, air, fire, air =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | fire, air, water, fire =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | fire, air, water, water =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | fire, air, water, earth =>
      intro y
      cases y
      · use fire
        exhaust
      · use earth
        exhaust
      · use air
        exhaust
      · use water
        exhaust
    | fire, air, water, air =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | fire, air, earth, fire =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | fire, air, earth, water =>
      intro y
      cases y
      · use fire
        exhaust
      · use air
        exhaust
      · use earth
        exhaust
      · use water
        exhaust
    | fire, air, earth, earth =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | fire, air, earth, air =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | fire, air, air, fire =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | fire, air, air, water =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | fire, air, air, earth =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | fire, air, air, air =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | water, fire, fire, fire =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | water, fire, fire, water =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | water, fire, fire, earth =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | water, fire, fire, air =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | water, fire, water, fire =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | water, fire, water, water =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | water, fire, water, earth =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | water, fire, water, air =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | water, fire, earth, fire =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | water, fire, earth, water =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | water, fire, earth, earth =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | water, fire, earth, air =>
      intro y
      cases y
      · use water
        exhaust
      · use fire
        exhaust
      · use earth
        exhaust
      · use air
        exhaust
    | water, fire, air, fire =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | water, fire, air, water =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | water, fire, air, earth =>
      intro y
      cases y
      · use water
        exhaust
      · use fire
        exhaust
      · use air
        exhaust
      · use earth
        exhaust
    | water, fire, air, air =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | water, water, fire, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, fire, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, fire, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, fire, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, water, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, water, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, water, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, water, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, earth, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, earth, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, earth, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, earth, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, air, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, air, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, air, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, water, air, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | water, earth, fire, fire =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | water, earth, fire, water =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | water, earth, fire, earth =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | water, earth, fire, air =>
      intro y
      cases y
      · use earth
        exhaust
      · use fire
        exhaust
      · use water
        exhaust
      · use air
        exhaust
    | water, earth, water, fire =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | water, earth, water, water =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | water, earth, water, earth =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | water, earth, water, air =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | water, earth, earth, fire =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | water, earth, earth, water =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | water, earth, earth, earth =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | water, earth, earth, air =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | water, earth, air, fire =>
      intro y
      cases y
      · use air
        exhaust
      · use fire
        exhaust
      · use water
        exhaust
      · use earth
        exhaust
    | water, earth, air, water =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | water, earth, air, earth =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | water, earth, air, air =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | water, air, fire, fire =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | water, air, fire, water =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | water, air, fire, earth =>
      intro y
      cases y
      · use earth
        exhaust
      · use fire
        exhaust
      · use air
        exhaust
      · use water
        exhaust
    | water, air, fire, air =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | water, air, water, fire =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | water, air, water, water =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | water, air, water, earth =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | water, air, water, air =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | water, air, earth, fire =>
      intro y
      cases y
      · use air
        exhaust
      · use fire
        exhaust
      · use earth
        exhaust
      · use water
        exhaust
    | water, air, earth, water =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | water, air, earth, earth =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | water, air, earth, air =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | water, air, air, fire =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | water, air, air, water =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | water, air, air, earth =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | water, air, air, air =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | earth, fire, fire, fire =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | earth, fire, fire, water =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | earth, fire, fire, earth =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | earth, fire, fire, air =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | earth, fire, water, fire =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | earth, fire, water, water =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | earth, fire, water, earth =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | earth, fire, water, air =>
      intro y
      cases y
      · use water
        exhaust
      · use earth
        exhaust
      · use fire
        exhaust
      · use air
        exhaust
    | earth, fire, earth, fire =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | earth, fire, earth, water =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | earth, fire, earth, earth =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | earth, fire, earth, air =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | earth, fire, air, fire =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | earth, fire, air, water =>
      intro y
      cases y
      · use water
        exhaust
      · use air
        exhaust
      · use fire
        exhaust
      · use earth
        exhaust
    | earth, fire, air, earth =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | earth, fire, air, air =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | earth, water, fire, fire =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | earth, water, fire, water =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | earth, water, fire, earth =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | earth, water, fire, air =>
      intro y
      cases y
      · use earth
        exhaust
      · use water
        exhaust
      · use fire
        exhaust
      · use air
        exhaust
    | earth, water, water, fire =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | earth, water, water, water =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | earth, water, water, earth =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | earth, water, water, air =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | earth, water, earth, fire =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | earth, water, earth, water =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | earth, water, earth, earth =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | earth, water, earth, air =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | earth, water, air, fire =>
      intro y
      cases y
      · use air
        exhaust
      · use water
        exhaust
      · use fire
        exhaust
      · use earth
        exhaust
    | earth, water, air, water =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | earth, water, air, earth =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | earth, water, air, air =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | earth, earth, fire, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, fire, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, fire, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, fire, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, water, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, water, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, water, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, water, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, earth, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, earth, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, earth, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, earth, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, air, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, air, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, air, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, earth, air, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | earth, air, fire, fire =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | earth, air, fire, water =>
      intro y
      cases y
      · use earth
        exhaust
      · use air
        exhaust
      · use fire
        exhaust
      · use water
        exhaust
    | earth, air, fire, earth =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | earth, air, fire, air =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | earth, air, water, fire =>
      intro y
      cases y
      · use air
        exhaust
      · use earth
        exhaust
      · use fire
        exhaust
      · use water
        exhaust
    | earth, air, water, water =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | earth, air, water, earth =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | earth, air, water, air =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | earth, air, earth, fire =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | earth, air, earth, water =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | earth, air, earth, earth =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | earth, air, earth, air =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | earth, air, air, fire =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | earth, air, air, water =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | earth, air, air, earth =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | earth, air, air, air =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, fire, fire, fire =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, fire, fire, water =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, fire, fire, earth =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, fire, fire, air =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, fire, water, fire =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | air, fire, water, water =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | air, fire, water, earth =>
      intro y
      cases y
      · use water
        exhaust
      · use earth
        exhaust
      · use air
        exhaust
      · use fire
        exhaust
    | air, fire, water, air =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | air, fire, earth, fire =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | air, fire, earth, water =>
      intro y
      cases y
      · use water
        exhaust
      · use air
        exhaust
      · use earth
        exhaust
      · use fire
        exhaust
    | air, fire, earth, earth =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | air, fire, earth, air =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | air, fire, air, fire =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | air, fire, air, water =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | air, fire, air, earth =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | air, fire, air, air =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | air, water, fire, fire =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | air, water, fire, water =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | air, water, fire, earth =>
      intro y
      cases y
      · use earth
        exhaust
      · use water
        exhaust
      · use air
        exhaust
      · use fire
        exhaust
    | air, water, fire, air =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | air, water, water, fire =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, water, water, water =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, water, water, earth =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, water, water, air =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, water, earth, fire =>
      intro y
      cases y
      · use air
        exhaust
      · use water
        exhaust
      · use earth
        exhaust
      · use fire
        exhaust
    | air, water, earth, water =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | air, water, earth, earth =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | air, water, earth, air =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | air, water, air, fire =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | air, water, air, water =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | air, water, air, earth =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | air, water, air, air =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | air, earth, fire, fire =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | air, earth, fire, water =>
      intro y
      cases y
      · use earth
        exhaust
      · use air
        exhaust
      · use water
        exhaust
      · use fire
        exhaust
    | air, earth, fire, earth =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | air, earth, fire, air =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | air, earth, water, fire =>
      intro y
      cases y
      · use air
        exhaust
      · use earth
        exhaust
      · use water
        exhaust
      · use fire
        exhaust
    | air, earth, water, water =>
      have : earth = air
      · apply h
        rw [h_earth]
        rw [h_air]
      exhaust
    | air, earth, water, earth =>
      have : water = air
      · apply h
        rw [h_water]
        rw [h_air]
      exhaust
    | air, earth, water, air =>
      have : fire = air
      · apply h
        rw [h_fire]
        rw [h_air]
      exhaust
    | air, earth, earth, fire =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, earth, earth, water =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, earth, earth, earth =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, earth, earth, air =>
      have : water = earth
      · apply h
        rw [h_water]
        rw [h_earth]
      exhaust
    | air, earth, air, fire =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | air, earth, air, water =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | air, earth, air, earth =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | air, earth, air, air =>
      have : fire = earth
      · apply h
        rw [h_fire]
        rw [h_earth]
      exhaust
    | air, air, fire, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, fire, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, fire, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, fire, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, water, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, water, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, water, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, water, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, earth, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, earth, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, earth, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, earth, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, air, fire =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, air, water =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, air, earth =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
    | air, air, air, air =>
      have : fire = water
      · apply h
        rw [h_fire]
        rw [h_water]
      exhaust
