import Extension97

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every functional on the chosen column space comes from an actual message in D. -/
theorem row_realization {V : Type*} [AddCommGroup V] [Module F₂ V]
    (D : Code ι) (e : (D →ₗ[F₂] F₂) ≃ₗ[F₂] V) (l : V →ₗ[F₂] F₂) :
    ∃ x : D,∀ g : D →ₗ[F₂] F₂,g x=l (e g) := by
  let f := l.comp e.toLinearMap
  let x := (Module.evalEquiv F₂ D).symm f
  refine ⟨x,?_⟩
  intro g
  have h := (Module.evalEquiv F₂ D).apply_symm_apply f
  exact LinearMap.congr_fun h g

theorem d97_no_coset (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι=97) (hk : Module.finrank F₂ D=7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D)
    (c : Word ι) (hcoset : ∀ x∈D,46≤weight (c+x) ∧ weight (c+x)%4=2) : False := by
  obtain ⟨e,ρ,hρ⟩ := d97_columns hWard D hlen hk hD hd hfull
  let z : Word Index97 := fun j => c (ρ.symm j)
  apply no_standard97 z
  intro α τ β
  obtain ⟨x,hx⟩ := row_realization D e (standardForm α τ β)
  have hsum : standardSum z α τ β=∑ i,sign ((c+x.val) i) := by
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

#print axioms d97_no_coset
end
end Binary97
