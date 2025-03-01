import AbstractAlgebra.One
import AbstractAlgebra.Inv
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Defs

namespace AbstractAlgebra

open One
open Inv

/- Definition.

(1) A *group* is an ordered pair (G, *) where G is a set and * is a binary operation on G satisfying the following axioms:

  (i)   (a * b) * c = a * (b * c), for all a, b, c ∈ G, i. e., * is *associative*,
  (ii)  there exists an element 1 in G, called an *identity* of G, such that for all a ∈ G
        we have a * 1 = 1 * a = a,
  (iii) for each a ∈ G there is an element a⁻¹ of G, called an *inverse* of a, such that a * a⁻¹ =
        a⁻¹ * a = 1.
-/
class Group (G : Type u) extends Mul G, One G, Inv G where

  -- Group axioms

  -- 1. Associativity of multiplication
  protected mul_assoc (a b c : G) : a * b * c = a * (b * c)

  -- 2. Identity law
  protected one_mul (a : G) : 1 * a = a

  -- 3. Inverse law
  protected inv_mul_cancel (a : G) : a⁻¹ * a = 1

section

class AddGroup (G : Type u) extends Add G, Zero G, Neg G where

  -- Group axioms

  -- 1. Associativity of addition
  protected add_assoc (a b c : G) : a + b + c = a + (b + c)

  -- 2. Identity/Zero law
  protected zero_add (a : G) : 0 + a = a

  -- 3. Negative law
  protected neg_add_cancel (a : G) : (-a) + a = 0

section

/-
...

(2) The group (G) is called *abelian* (or *commutative*) if a * b = b * a for all a, b ∈ G.
-/

class AbelianGroup (G: Type u) extends Group G where
  protected mul_comm (a b : G) : a * b = b * a

class AddAbelianGroup (G: Type u) extends AddGroup G where
  protected add_com (a b : G) : a + b = b + a

/- Examples
(1) ℤ, ℚ, ℝ and ℂ are groups under + with 1 = 0 and a⁻¹ = -a, for all a.
...
-/

instance: AddGroup ℤ where
  add_assoc := add_assoc
  zero_add := zero_add
  neg_add_cancel := neg_add_cancel

instance: AddGroup ℚ where
  add_assoc := add_assoc
  zero_add := zero_add
  neg_add_cancel := neg_add_cancel

instance: AddGroup ℝ where
  add_assoc := add_assoc
  zero_add := zero_add
  neg_add_cancel := neg_add_cancel

instance: AddGroup ℂ where
  add_assoc := add_assoc
  zero_add := zero_add
  neg_add_cancel := neg_add_cancel

/- [UNFINISHED]
...

(2) ℚ - {0}, R - {0}, C - {0}, ℚ+, ℝ+ are groups under * with 1 = 1 and a⁻¹ = 1/a, for all a.
-/

structure Nonzero (α : Type u) [Zero α] where
  protected elt : α
  protected elt_is_nonzero' : elt ≠ 0

theorem elt_is_nonzero [Zero α] (x : Nonzero α) : x.elt ≠ 0 := x.elt_is_nonzero'

theorem eq_nonzero [Zero α] (a b : Nonzero α) : a = b ↔ a.elt = b.elt := by
  constructor
  . intro h; rw [h]
  . intro h
    calc a = ⟨a.elt, a.elt_is_nonzero'⟩ := by rfl
         _ = ⟨b.elt, b.elt_is_nonzero'⟩ := by simp [h]
         _ = b                         := by rfl

instance instMulNonzero [Mul α] [Zero α] [NoZeroDivisors α]: Mul (Nonzero α) where
  mul x y :=
    Nonzero.mk
      (x.elt * y.elt)
      (by apply mul_ne_zero <;> apply elt_is_nonzero)

#check one_ne_zero
#check NeZero

instance instOneNonzero [Zero α] [One α] [NeZero (1:α)]: One (Nonzero α) where
  one := ⟨1, one_ne_zero⟩

#check inv_ne_zero

instance instInvNonzeroℚ : Inv (Nonzero ℚ) where
  inv x := Nonzero.mk x.elt⁻¹ (inv_ne_zero (elt_is_nonzero x))

instance : Group (Nonzero ℚ) where
  mul_assoc a b c := by
    rw [eq_nonzero]
    calc  (a * b * c).elt = (a * b).elt * c.elt := by rfl
          _               = a.elt * b.elt * c.elt := by rfl
          _               = a.elt * (b.elt * c.elt) := by apply Rat.mul_assoc
  one_mul a := by
    rw [eq_nonzero]
    calc  (1 * a).elt = 1 * a.elt := by rfl
          _           = a.elt := Rat.one_mul a.elt
  inv_mul_cancel a := by
    rw [eq_nonzero]
    calc  (a⁻¹ * a).elt = a⁻¹.elt * a.elt := by rfl
          _             = (a.elt)⁻¹ * a.elt := by rfl
          _             = 1 := Rat.inv_mul_cancel a.elt (elt_is_nonzero a)

instance : Mul (Nonzero ℝ) where
  mul x y :=
    Nonzero.mk
      (x.elt * y.elt)
      (by apply mul_ne_zero <;> apply elt_is_nonzero)

instance: One (Nonzero ℝ) where
  one := ⟨1, by simp [one_ne_zero]⟩

noncomputable instance : Inv (Nonzero ℝ) where
  inv x := Nonzero.mk x.elt⁻¹
    (by apply inv_ne_zero; exact elt_is_nonzero x)

instance [Inv G] [Inv H]: Inv (G × H) where
  inv p := ⟨p.fst⁻¹, p.snd⁻¹⟩

instance [Group G] [Group H]: Group (G × H) where
  mul_assoc a b c := by
    calc  a * b * c = ⟨(a.fst * b.fst) * c.fst, (a.snd * b.snd) * c.snd⟩ := by rfl
          _         = ⟨a.fst * (b.fst * c.fst), a.snd * (b.snd * c.snd)⟩ := by
            rw [Group.mul_assoc, Group.mul_assoc]
          _         = a * (b * c) := by rfl
  one_mul a := by
    calc  1 * a = ⟨1 * a.fst, 1 * a.snd⟩ := by rfl
          _     = ⟨a.fst, a.snd⟩ := by simp [Group.one_mul]
          _     = a := by rfl
  inv_mul_cancel a := by
    calc  a⁻¹ * a = ⟨a.fst⁻¹ * a.fst, a.snd⁻¹ * a.snd⟩ := by rfl
          _       = 1 := by simp [Group.inv_mul_cancel]
