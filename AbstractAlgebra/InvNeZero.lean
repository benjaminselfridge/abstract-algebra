import AbstractAlgebra.Inv

namespace AbstractAlgebra

class InvNeZero (α : Type u) extends Zero α, Inv α where
  inv_ne_zero {a : α} (h : a ≠ 0): a⁻¹ ≠ 0

/- [UNFINISHED]
 * The idea here was to create a typeclass for the knowledge that x ≠ 0 → x⁻¹ ≠ 0.
instance instInvNonzero [Zero α] [Inv α] [InvNeZero α]: Inv (Nonzero α) where
  inv x := Nonzero.mk x.elt⁻¹
    (by have h : x.elt ≠ 0 := elt_is_nonzero x
        apply inv_ne_zero x.elt
    )
    --(by apply inv_ne_zero x.elt; exact elt_is_nonzero x)
-/
