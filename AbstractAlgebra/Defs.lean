-- import Mathlib.Algebra.Group.Defs
import AbstractAlgebra.One
import AbstractAlgebra.Inv
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Defs

namespace AbstractAlgebra

open One
open Inv

class Group (G : Type u) extends Mul G, One G, Inv G where

  -- Group axioms

  -- 1. Associativity of multiplication
  protected mul_assoc (a b c : G) : a * b * c = a * (b * c)

  -- 2. Identity law
  protected one_mul (a : G) : 1 * a = a

  -- 3. Inverse law
  protected inv_mul_cancel (a : G) : a⁻¹ * a = 1

section

theorem mul_assoc [Group G] (a b c : G) : a * b * c = a * (b * c) :=
  Group.mul_assoc a b c

theorem one_mul [Group G] (a : G) : 1 * a = a :=
  Group.one_mul a

theorem inv_mul_cancel [Group G] (a : G) : a⁻¹ * a = 1 :=
  Group.inv_mul_cancel a

def npowRec [Mul G] [One G] (n : ℕ) (a : G) := match n with
  | 0 => 1
  | Nat.succ k => a * npowRec k a
def npow [Group G] (n : ℕ) (a : G) : G := npowRec n a
def npow_zero [Group G] (a : G) : npow 0 a = 1 := by
  simp [npow, npowRec]
def npow_succ [Group G] (n : ℕ) (a : G) : npow (n+1) a = a * npow n a := by
  simp [npow, npowRec]

instance Group.toNatPow [Group G] : NatPow G :=
  ⟨fun n a => npow a n⟩

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

theorem inv_one : (1 : G)⁻¹ = 1 := by
  calc (1 : G)⁻¹ = 1 * 1⁻¹      := by rw [one_mul]
       _         = 1            := by rw [mul_inv_cancel]

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

structure Hom (G H : Type*) [Group G] [Group H] where
  map : G → H
  map_mul_eq_mul_map' : map (a * b) = map a * map b

theorem map_mul_eq_mul_map (φ : Hom G H): φ.map (a * b) = φ.map a * φ.map b :=
  φ.map_mul_eq_mul_map'

infixr:34 " ↠ "  => Hom

theorem hom_one (φ : G ↠ H) : φ.map 1 = 1 := by
  have h' : φ.map 1 * φ.map 1 = φ.map 1 * 1 := by
    rw [← map_mul_eq_mul_map, mul_one, mul_one]
  apply mul_left_cancel (φ.map 1)
  exact h'

theorem hom_inv (φ : G ↠ H) : φ.map a⁻¹ = (φ.map a)⁻¹ := by
  have h' : φ.map a * φ.map a⁻¹ = φ.map a * (φ.map a)⁻¹ := by
    rw [mul_inv_cancel, ← map_mul_eq_mul_map, mul_inv_cancel, hom_one φ]
  apply mul_left_cancel (φ.map a)
  exact h'

structure Subgroup (G:Type*) [Group G] where
  carrier : Set G
  mul_mem' : ∀ a b, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem' : 1 ∈ carrier
  inv_mem' : ∀ a, a ∈ carrier → a⁻¹ ∈ carrier

theorem mul_mem (H : Subgroup G) (a b : G) :
  a ∈ H.carrier → b ∈ H.carrier → a * b ∈ H.carrier :=
  H.mul_mem' a b

theorem one_mem (H : Subgroup G) : 1 ∈ H.carrier := H.one_mem'

theorem inv_mem (H : Subgroup G) (a : G) : a ∈ H.carrier → a⁻¹ ∈ H.carrier :=
  H.inv_mem' a

def kernel [Group G] [Group H] (φ : G → H) := {a : G | φ a = 1}

def kernel_subgroup (φ : G ↠ H) : Subgroup G :=
  Subgroup.mk
  { g : G | φ.map g = 1 }
  ( by  intro a b h₁ h₂
        show φ.map (a * b) = 1
        calc  φ.map (a * b) = φ.map a * φ.map b := by
                apply map_mul_eq_mul_map
              _             = 1 * 1             := by rw [h₁, h₂]
              _             = 1                 := one_mul 1
  )
  ( show φ.map 1 = 1 from hom_one φ )
  ( by  intro a h₁
        show φ.map a⁻¹ = 1
        calc  φ.map a⁻¹ = (φ.map a)⁻¹ := by rw [hom_inv φ]
              _         = 1           := by rw [h₁, inv_one]
  )

structure Perm (α : Type u) where
  toFun : α → α
  invFun : α → α
  left_inv : invFun ∘ toFun = id
  right_inv: toFun ∘ invFun = id

instance: Group (Perm α) where
  mul σ τ := Perm.mk
    (σ.toFun ∘ τ.toFun)
    (τ.invFun ∘ σ.invFun)
    (by rw [Function.comp_assoc, ← Function.comp_assoc σ.invFun]
        rw [σ.left_inv]
        simp
        rw [τ.left_inv]
    )
    (by rw [Function.comp_assoc, ← Function.comp_assoc τ.toFun]
        rw [τ.right_inv]
        simp
        rw [σ.right_inv]
    )
  one := Perm.mk id id rfl rfl
  inv σ := Perm.mk σ.invFun σ.toFun σ.right_inv σ.left_inv
  mul_assoc := by
    intro a b c
    simp [(· * ·)]
    constructor <;> rfl
  one_mul :=  by intro a; rfl
  inv_mul_cancel := by
    intro σ
    simp [(· * ·), σ.left_inv]
    rfl

structure GroupAction (G:Type*) (A : Set G) [Group G] where
  apply : G → A → A
  one_action' (a : A) : apply 1 a = a
  action_assoc' (g₁ g₂ : G) (a : A) : apply g₁ (apply g₂ a) = apply (g₁ * g₂) a

theorem one_action (ρ : GroupAction G A) : ρ.apply 1 a = a :=
  ρ.one_action' a

theorem action_assoc (ρ : GroupAction G A) (g₁ g₂ : G) (a : A) :
  ρ.apply g₁ (ρ.apply g₂ a) = ρ.apply (g₁ * g₂) a :=
  ρ.action_assoc' g₁ g₂ a

/--
  A group action is a homomorphism from G to Perm A.
-/
def groupActionHom (ρ : GroupAction G A) : G ↠ Perm A :=
  Hom.mk
  (fun g => Perm.mk
    (ρ.apply g)
    (ρ.apply g⁻¹)
    (by apply funext; intro a; simp
        rw [action_assoc, inv_mul_cancel, one_action]
    )
    (by apply funext; intro a; simp
        rw [action_assoc, mul_inv_cancel, one_action]
    )
  )
  (by intro g₁ g₂
      simp [(· * ·), Mul.mul]
      constructor
      . apply funext; intro a; simp
        rw [action_assoc]
        simp [(· * ·)]
      . apply funext; intro a; simp
        rw [action_assoc, ← mul_inv_rev]
        simp [(· * ·)]
  )
