/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
/-!
## Typeclass `One`

`Zero` has already been defined in Lean.
-/

namespace AbstractAlgebra

universe u

class One (α : Type u) where
  one : α

instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

instance (priority := 200) One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

variable {α : Type u}

instance (priority := 20) Zero.instNonempty [Zero α] : Nonempty α :=
  ⟨0⟩

instance (priority := 20) One.instNonempty [One α] : Nonempty α :=
  ⟨1⟩

theorem Subsingleton.eq_one [One α] [Subsingleton α] (a : α) : a = 1 :=
  Subsingleton.elim _ _

end AbstractAlgebra
