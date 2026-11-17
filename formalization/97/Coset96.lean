import Extension96
import Coset97

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem d96_no_coset (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι=96) (hk : Module.finrank F₂ D=7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D)
    (c : Word ι) (ε : ℕ) (hε : ε≤1)
    (hcoset : ∀ x∈D,46≤weight (c+x)+ε ∧ (weight (c+x)+ε)%4=2) : False := by
  obtain ⟨e,ρ,hρ⟩ := d96_columns D hlen hk hD hd hfull
  let z : Word Index96 := fun j => c (ρ.symm j)
  apply no_standard96 z (4+2*(ε : ℤ)) (by omega)
  intro τ β
  obtain ⟨x,hx⟩ := row_realization D e (standardForm96 τ β)
  have hsum : standardSum96 z τ β=∑ i,sign ((c+x.val) i) := by
    symm
    apply Fintype.sum_equiv ρ
    intro i
    simp only [z,ρ.symm_apply_apply,hρ i,← hx,coordinateForms,
      LinearMap.comp_apply,LinearMap.proj_apply,Submodule.subtype_apply,Pi.add_apply,sign_add]
  have hs := sign_sum_weight (c+x.val)
  change (∑ i,sign ((c+x.val) i))=(Fintype.card ι : ℤ)-2*(weight (c+x.val) : ℤ) at hs
  rw [hlen] at hs
  have hw := hcoset x.val x.property
  rw [hsum,hs]
  constructor <;> omega

#print axioms d96_no_coset
end
end Binary97
