import Mathlib.Algebra.Group.Defs

namespace AbstractAlgebra

/- Minimal definition of a set -/
def Set (α : Type u) := α → Prop

/-- Turn a predicate `p : α → Prop` into a set, also written as `{x | p x}` -/
def setOf {α : Type u} (p : α → Prop) : Set α :=
  p

namespace Set

protected def Mem (s : Set α) (a : α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

end Set

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

variable {G : Type u} [Group G]
variable (a b c : G)

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  calc a * a⁻¹ = 1 * a * a⁻¹             := by rw [one_mul]
       _       = (a⁻¹)⁻¹ * a⁻¹ * a * a⁻¹ := by rw [inv_mul_cancel]
       _       = (a⁻¹)⁻¹ * 1 * a⁻¹       := by rw [mul_assoc (a⁻¹)⁻¹, inv_mul_cancel]
       _       = (a⁻¹)⁻¹ * a⁻¹           := by rw [mul_assoc, one_mul]
       _       = 1                       := by rw [inv_mul_cancel]

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
  calc b = 1 * b       := by rw [one_mul]
       _ = a⁻¹ * a * b := by rw [inv_mul_cancel]
       _ = a⁻¹ * 1     := by rw [mul_assoc, h]
       _ = a⁻¹         := by rw [mul_one]

theorem inv_inv : (a⁻¹)⁻¹ = a := by
  calc (a⁻¹)⁻¹ = (a⁻¹)⁻¹ * 1       := by rw [mul_one]
       _       = (a⁻¹)⁻¹ * a⁻¹ * a := by rw [mul_assoc, inv_mul_cancel]
       _       = 1 * a             := by rw [inv_mul_cancel]
       _       = a                 := by rw [one_mul]

theorem mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  calc (a * b)⁻¹ = (a * b)⁻¹ * 1                 := by rw [mul_one]
       _         = (a * b)⁻¹ * a * a⁻¹           := by rw [mul_assoc, mul_inv_cancel]
       _         = (a * b)⁻¹ * a * 1 * a⁻¹       := by rw [mul_one]
       _         = (a * b)⁻¹ * a * b * b⁻¹ * a⁻¹ := by rw [mul_assoc ((a * b)⁻¹ * a) b, mul_inv_cancel];
       _         = 1 * b⁻¹ * a⁻¹                 := by rw [mul_assoc (a * b)⁻¹, inv_mul_cancel]
       _         = b⁻¹ * a⁻¹                     := by rw [one_mul]

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

end Group

variable {G H : Type u} [Group G] [Group H]
variable (a b c : G)
variable (x y z : H)

/-
instance : Group ℤ where
  inv x := -x
  mul x y := x + y
  one := 0

  mul_assoc a b c := Int.add_assoc a b c
  one_mul a := Int.zero_add a
  inv_mul_cancel a := Int.add_left_neg a

end AbstractAlgebra
-/

def IsHom (φ : G → H) : Prop :=  ∀ a b : G, φ (a * b) = φ a * φ b
