import Mathlib

variable {V : Type*} (s : Setoid V)
#check Sigma
def iso : V ≃ Sigma (fun (c : Quotient s) => { x // s.r c.out x}) where
  toFun := fun v =>  ⟨⟦v⟧,⟨v, Quotient.mk_out v⟩⟩
  invFun := fun ⟨c, ⟨x, hx⟩⟩ => x
  left_inv := fun v => rfl
  right_inv := fun ⟨c,x⟩ => by
    ext
    · rw [Quotient.mk_eq_iff_out]
      exact s.symm x.2
    · rfl
