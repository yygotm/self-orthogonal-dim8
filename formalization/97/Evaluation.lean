import Geometry
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module F₂ V]

/-- The binary code obtained by evaluating all dual vectors on a set of points. -/
def evaluationMap (S : Finset V) : (V →ₗ[F₂] F₂) →ₗ[F₂] (S → F₂) where
  toFun g x := g x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evaluationCode (S : Finset V) : Code S := LinearMap.range (evaluationMap S)

theorem evaluation_weight (S : Finset V) (g : V →ₗ[F₂] F₂) :
    weight (evaluationMap S g) = (S.filter fun x => g x ≠ 0).card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨x.property,(Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    exact ⟨⟨x,(Finset.mem_filter.mp hx).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩,rfl⟩

theorem evaluation_full (S : Finset V) (hzero : (0 : V) ∉ S) :
    FullLength (evaluationCode S) := by
  intro i
  have hi : i.val ≠ 0 := by intro h; exact hzero (h ▸ i.property)
  obtain ⟨g,hg⟩ := Module.Projective.exists_dual_ne_zero F₂ hi
  exact ⟨⟨evaluationMap S g,⟨g,rfl⟩⟩,hg⟩

theorem evaluation_projective (S : Finset V) :
    Function.Injective (coordinateForms (evaluationCode S)) := by
  intro i j hij
  apply Subtype.ext
  apply Module.eval_apply_injective F₂
  ext g
  exact LinearMap.congr_fun hij ⟨evaluationMap S g,⟨g,rfl⟩⟩

#print axioms evaluation_projective
end
end Binary97
