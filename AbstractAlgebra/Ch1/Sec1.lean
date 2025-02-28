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

example : (-a : ℝ) + a = 0 := by exact neg_add_cancel a

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

structure ℚnz where
  elt : ℚ
  elt_is_nonzero : elt ≠ 0

#check ℚnz.elt_is_nonzero

example : (1:ℚ) ≠ 0 := by apply?

instance: Group ℚnz where
  mul x y :=
    ℚnz.mk (x.elt * y.elt)
      (by rw [mul_ne_zero_iff_right] <;> apply ℚnz.elt_is_nonzero)
  one := ℚnz.mk 1 (Ne.symm Rat.zero_ne_one)
  inv := sorry
  mul_assoc := sorry
  one_mul := sorry
  inv_mul_cancel := sorry
