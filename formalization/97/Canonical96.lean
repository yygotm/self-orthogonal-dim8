import StandardWeights
import BlockTypes
import Mathlib.LinearAlgebra.Projection

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module F₂ V] [Module.Finite F₂ V]

theorem subspace_coordinates (A : Submodule F₂ V) (a b : ℕ)
    (hA : Module.finrank F₂ A=a) (hV : Module.finrank F₂ V=a+b) :
    ∃ e : V ≃ₗ[F₂] (Word (Fin a) × Word (Fin b)),∀ x,(e x).2=0 ↔ x∈A := by
  obtain ⟨B,hB⟩ := A.exists_isCompl
  let j := Submodule.prodEquivOfIsCompl A B hB
  have hr := j.finrank_eq
  rw [Module.finrank_prod,hA,hV] at hr
  have hdB : Module.finrank F₂ B=b := by omega
  let ea : A ≃ₗ[F₂] Word (Fin a) := LinearEquiv.ofFinrankEq _ _ (by simpa [Word] using hA)
  let eb : B ≃ₗ[F₂] Word (Fin b) := LinearEquiv.ofFinrankEq _ _ (by simpa [Word] using hdB)
  refine ⟨j.symm.trans (ea.prodCongr eb),?_⟩
  intro x
  change eb (j.symm x).2=0 ↔ x∈A
  have hz : eb (j.symm x).2=0 ↔ (j.symm x).2=0 := by
    constructor
    · intro h; apply eb.injective; simpa using h
    · intro h; simp [h]
  rw [hz]
  exact Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero A B hB

abbrev StandardSpace96 := Word (Fin 5) × Word (Fin 2)
abbrev Index96 := NonzeroTwo × Word (Fin 5)

def standardColumn96 (i : Index96) : StandardSpace96 := (i.2,i.1.val)

/-- The length-96 geometry: all vectors outside one codimension-two subspace. -/
theorem d96_column_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Code ι) [Fintype D] (hlen : Fintype.card ι=96)
    (hk : Module.finrank F₂ D=7) (hD : DoublyEven D) (hd : MinWeight D 48)
    (hfull : FullLength D) :
    ∃ e : (D →ₗ[F₂] F₂) ≃ₗ[F₂] StandardSpace96,∀ g,
      (Finset.univ.filter fun i => coordinateForms D i=g).card=if (e g).2=0 then 0 else 1 := by
  let S := weightWords D 64
  let E := evaluationCode S
  letI : Fintype E := Fintype.ofFinite E
  have hs : S.card=3 := (d96_counts D hlen hk hD hd hfull).1
  have heven : ∀x∈E,weight x%2=0 := by
    rintro x ⟨g,rfl⟩
    have h := d96_inverse D hlen hk hD hd hfull g
    rw [evaluation_weight]
    change classWeight D 64 g%2=0
    omega
  have hE : Module.finrank F₂ E=2 := even3_parameters E (by simpa using hs)
    (evaluation_full S (by simp [S,weightWords,weight_zero])) heven
  let f : (D →ₗ[F₂] F₂) →ₗ[F₂] E := (evaluationMap S).rangeRestrict
  have hr := (evaluationMap S).finrank_range_add_finrank_ker
  change Module.finrank F₂ E + Module.finrank F₂ (LinearMap.ker (evaluationMap S))=
    Module.finrank F₂ (D →ₗ[F₂] F₂) at hr
  rw [hE,Subspace.dual_finrank_eq,hk] at hr
  obtain ⟨e,he⟩ := subspace_coordinates (LinearMap.ker (evaluationMap S)) 5 2 (by omega)
    (by rw [Subspace.dual_finrank_eq,hk])
  refine ⟨e,?_⟩
  intro g
  have hi := d96_inverse D hlen hk hD hd hfull g
  have hw := even3_weight E (by simpa using hs) heven (f g)
  have hweight : weight (f g).val=classWeight D 64 g := by exact evaluation_weight S g
  rw [hweight] at hw
  have hz : (e g).2=0 ↔ f g=0 := by
    rw [he]
    exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
  by_cases hb : (e g).2=0
  · have hf : f g=0 := hz.mp hb
    rw [if_pos hf] at hw
    rw [if_pos hb]
    omega
  · have hf : f g≠0 := fun h => hb (hz.mpr h)
    rw [if_neg hf] at hw
    rw [if_neg hb]
    omega

#print axioms d96_column_coordinates
end
end Binary97
