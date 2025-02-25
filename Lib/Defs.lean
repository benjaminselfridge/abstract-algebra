-- import Mathlib.Algebra.Group.Defs
import Lib.One
import Lib.Inv
import Mathlib.Data.Set.Basic

namespace AbstractAlgebra

open Lib

/- Minimal definition of a group -/

class Group (G : Type u) extends Mul G, One G, Inv G where

  -- Group axioms

  -- 1. Associativity of multiplication
  mul_assoc (a b c : G) : a * b * c = a * (b * c)

  -- 2. Identity law
  one_mul (a : G) : 1 * a = a

  -- 3. Inverse law
  inv_mul_cancel (a : G) : a⁻¹ * a = 1

open Group

namespace Group

section

variable {G : Type u} [Group G]
variable (a b c : G)

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  calc a * a⁻¹ = a⁻¹⁻¹ * a⁻¹ * a * a⁻¹ := by rw [inv_mul_cancel, one_mul]
       _       = a⁻¹⁻¹ * a⁻¹           := by rw [mul_assoc a⁻¹⁻¹, inv_mul_cancel, mul_assoc, one_mul]
       _       = 1                     := by rw [inv_mul_cancel]

theorem mul_one (a : G) : a * 1 = a := by
  calc a * 1 = a * a⁻¹ * a := by rw [mul_assoc, inv_mul_cancel]
       _     = 1 * a       := by rw [mul_inv_cancel]
       _     = a           := by rw [one_mul]


theorem id_unique : (∀ x : G, a * x = 1) → a = 1 := by
  intro h
  calc a = a * 1 := by rw [mul_one]
       _ = 1     := by rw [h 1]

theorem inv_unique : a * b = 1 → b = a⁻¹ := by
  intro h
  calc b = a⁻¹ * a * b := by rw [inv_mul_cancel, one_mul]
       _ = a⁻¹ * 1     := by rw [mul_assoc, h]
       _ = a⁻¹         := by rw [mul_one]

theorem inv_inv : a⁻¹⁻¹ = a := by
  calc a⁻¹⁻¹ = a⁻¹⁻¹ * 1       := by rw [mul_one]
       _     = a⁻¹⁻¹ * a⁻¹ * a := by rw [mul_assoc, inv_mul_cancel]
       _     = 1 * a           := by rw [inv_mul_cancel]
       _     = a               := by rw [one_mul]

theorem mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  calc (a * b)⁻¹ = (a * b)⁻¹ * a * a⁻¹           := by rw [mul_assoc, mul_inv_cancel, mul_one]
       _         = (a * b)⁻¹ * a * b * b⁻¹ * a⁻¹ := by rw [mul_assoc ((a * b)⁻¹ * a) b, mul_inv_cancel, mul_one];
       _         = b⁻¹ * a⁻¹                     := by rw [mul_assoc (a*b)⁻¹, inv_mul_cancel, one_mul]

-- Proposition 1.1.5 could sort of be demonstrated by doing a tactic.

theorem mul_left_cancel : a * b = a * c → b = c := by
  intro h
  calc b = a⁻¹ * a * b := by rw [inv_mul_cancel, one_mul]
       _ = a⁻¹ * a * c := by rw [mul_assoc, h, ← mul_assoc]
       _ = c           := by rw [inv_mul_cancel, one_mul]

theorem mul_right_cancel : a * c = b * c → a = b := by
  intro h
  calc a = a * c * c⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
       _ = b * c * c⁻¹ := by rw [h]
       _ = b           := by rw [mul_assoc, mul_inv_cancel, mul_one]
end
end Group

variable {G H : Type u} [Group G] [Group H]

variable {A B : Set α}

def IsHom (φ : G → H) : Prop :=  ∀ a b : G, φ (a * b) = φ a * φ b

theorem hom_one (φ : G → H) (h : IsHom φ): φ 1 = 1 := by
  have h' : φ 1 * φ 1 = φ 1 * 1 := by rw [← h, mul_one, mul_one]
  apply mul_left_cancel (φ 1)
  exact h'

/-
theorem hom_inv (φ : G → H) (h : IsHom φ) : φ a⁻¹ = (φ a)⁻¹ := by
-/

structure GroupAction (G:Type*) (A : Set G) [Group G] where
  apply : G → A → A
  one_action (a : A) : apply 1 a = a
  action_assoc (g₁ g₂ : G) (a : A) : apply g₁ (apply g₂ a) = apply (g₁ * g₂) a

structure Subgroup (G:Type*) [Group G] where
  carrier : Set G
  mul_mem : ∀ a b, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem : 1 ∈ carrier
  inv_mem : ∀ a, a ∈ carrier → a⁻¹ ∈ carrier

def subgroup_criterion {G} [Group G] (Hₛ : Set G) : Prop :=
  (1 ∈ Hₛ) ∧
  (∀ h₁ h₂ : G, h₁ ∈ Hₛ ∧ h₂ ∈ Hₛ → h₁⁻¹ * h₂ ∈ Hₛ)

def Subgroup_of_subgroup_criterion {G} [Group G] (Hₛ : Set G)
   (sc : subgroup_criterion Hₛ) : Subgroup G :=
   have inv_mem : ∀ a : G, a ∈ Hₛ → a⁻¹ ∈ Hₛ := by
     intro a h
     rw [← mul_one a⁻¹]
     apply sc.right
     exact ⟨h, sc.left⟩
   Subgroup.mk
    Hₛ
    (by intros a b
        show a ∈ Hₛ → b ∈ Hₛ → a * b ∈ Hₛ
        intros hp₁ hp₂
        have : a * b = a⁻¹⁻¹ * b := by rw [inv_inv]
        rw [this]
        apply sc.right
        exact ⟨inv_mem a hp₁, hp₂⟩
    )
    sc.left
    inv_mem

theorem subgroup_criterion_of_Subgroup {G} [Group G]
  (Hₛ : Subgroup G) : subgroup_criterion (Hₛ.carrier) := by
  constructor
  . exact Hₛ.one_mem
  . intro a b h
    apply Hₛ.mul_mem
    . apply Hₛ.inv_mem; exact h.left
    . exact h.right

def kernel [Group G] [Group H] (φ : G → H) := {a : G | φ a = 1}

def kernel_subgroup (φ : G → H) (h : IsHom φ) : Subgroup G :=
  Subgroup.mk
  { g : G | φ g = 1 }
  ( by intro a b h₁ h₂
       calc φ (a * b) = φ a * φ b := by apply h
            _         = 1 * 1     := by rw [h₁, h₂]
            _         = 1         := one_mul 1
  )
  (hom_one φ h)
  (by intro a h₁
      sorry
  )
