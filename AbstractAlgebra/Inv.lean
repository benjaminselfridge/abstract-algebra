namespace AbstractAlgebra
/-- Class of types that have an inversion operation. -/

class Inv (α : Type u) where
  /-- Invert an element of α, denoted by `a⁻¹`. -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv.inv

end AbstractAlgebra
