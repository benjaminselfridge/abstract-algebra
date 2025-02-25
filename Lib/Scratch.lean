import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Group

#check Group

variable {G : Type u} [Group G]
variable (a b c : G)

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group

#check mul_inv_rev

#check mul_left_cancel

#check MonoidHom
