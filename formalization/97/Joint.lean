import Affine

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module F₂ V] [Module.Finite F₂ V]

def jointEvaluation (S T : Finset V) : (V →ₗ[F₂] F₂) →ₗ[F₂]
    evaluationCode S × evaluationCode T :=
  (evaluationMap S).rangeRestrict.prod (evaluationMap T).rangeRestrict

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem d97_joint_injective (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι=97) (hk : Module.finrank F₂ D=7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D) :
    Function.Injective (jointEvaluation (weightWords D 52) (weightWords D 64)) := by
  intro g h he
  by_contra hne
  have hbound := (d97_auxiliary_weights hWard D hlen hk hD hd hfull).2 (g-h) (sub_ne_zero.mpr hne)
  have he1 : evaluationMap (weightWords D 52) g=evaluationMap (weightWords D 52) h :=
    congrArg (fun p => p.1.val) he
  have he2 : evaluationMap (weightWords D 64) g=evaluationMap (weightWords D 64) h :=
    congrArg (fun p => p.2.val) he
  rw [map_sub,map_sub,he1,he2,sub_self,sub_self,weight_zero,weight_zero] at hbound
  omega

/-- The two projections in section 5.3 are independent: the joint map is an isomorphism. -/
def d97_joint_equiv (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι=97) (hk : Module.finrank F₂ D=7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D) :
    (D →ₗ[F₂] F₂) ≃ₗ[F₂]
      evaluationCode (weightWords D 52) × evaluationCode (weightWords D 64) :=
  (jointEvaluation (weightWords D 52) (weightWords D 64)).linearEquivOfInjective
    (d97_joint_injective hWard D hlen hk hD hd hfull) (by
      rw [Subspace.dual_finrank_eq,hk,Module.finrank_prod,
        (d97_V_parameters hWard D hlen hk hD hd hfull).2.1,
        d97_W_parameters hWard D hlen hk hD hd hfull])

/-- Equal column multiplicities give an actual permutation of coordinates. -/
theorem coordinate_equiv_of_multiplicity {α β γ : Type*} [Fintype α] [Fintype β]
    (f : α → γ) (g : β → γ)
    (hc : ∀ c,(Finset.univ.filter fun a => f a=c).card=
      (Finset.univ.filter fun b => g b=c).card) :
    ∃ e : α ≃ β,∀ a,g (e a)=f a := by
  have he (c : γ) : {a // f a=c} ≃ {b // g b=c} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype] using hc c)
  exact ⟨Equiv.ofFiberEquiv he,Equiv.ofFiberEquiv_map he⟩

#print axioms d97_joint_equiv
#print axioms coordinate_equiv_of_multiplicity
end
end Binary97
