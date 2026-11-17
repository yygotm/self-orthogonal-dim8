import Evaluation

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module F₂ V] [Module.Finite F₂ V]

theorem evaluation_kernel (S : Finset V) :
    LinearMap.ker (evaluationMap S)=(Submodule.span F₂ (S : Set V)).dualAnnihilator := by
  ext g
  constructor
  · intro hg
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    have hle : Submodule.span F₂ (S : Set V) ≤ LinearMap.ker g := by
      apply Submodule.span_le.mpr
      intro y hy
      exact congrFun hg ⟨y,hy⟩
    exact hle hx
  · intro hg
    ext x
    rw [Submodule.mem_dualAnnihilator] at hg
    exact hg x.val (Submodule.subset_span x.property)

theorem evaluation_finrank (S : Finset V) :
    Module.finrank F₂ (evaluationCode S)=Module.finrank F₂ (Submodule.span F₂ (S : Set V)) := by
  have h := (evaluationMap S).finrank_range_add_finrank_ker
  rw [evaluation_kernel,Subspace.dual_finrank_eq] at h
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span F₂ (S : Set V))
  change Module.finrank F₂ (LinearMap.range (evaluationMap S)) = _
  exact Nat.add_right_cancel (h.trans h2.symm)

/-- Full-weight words of an evaluation code are affine hyperplane witnesses. -/
theorem full_weight_evaluation (S : Finset V) (g : V →ₗ[F₂] F₂)
    (hg : weight (evaluationMap S g)=S.card) : ∀ x∈S,g x=1 := by
  rw [evaluation_weight] at hg
  have hs : S.filter (fun x => g x≠0)=S := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  intro x hx
  have hxS : x∈S.filter (fun x => g x≠0) := by rw [hs]; exact hx
  have hx' : g x≠0 := (Finset.mem_filter.mp hxS).2
  exact (by decide : ∀ a : F₂,a≠0 → a=1) (g x) hx'

#print axioms evaluation_finrank
end
end Binary97
