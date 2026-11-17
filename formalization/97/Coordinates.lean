import Geometry
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Abel

namespace Binary97
noncomputable section
open Classical
variable {V : Type*} [AddCommGroup V] [Module F₂ V]

/-- Explicitly split off a vector on which a functional has value one. -/
def splitOff (f : V →ₗ[F₂] F₂) (v : V) (hv : f v=1) :
    V ≃ₗ[F₂] (F₂ × LinearMap.ker f) where
  toFun x := (f x,⟨x-f x • v,by simp [hv]⟩)
  invFun p := p.1 • v + p.2.val
  left_inv x := by simp
  right_inv p := by
    obtain ⟨a,u⟩ := p
    have hu : f u.val=0 := u.property
    apply Prod.ext
    · simp [hv,hu]
    · apply Subtype.ext
      simp [hv,hu]
  map_add' x y := by
    apply Prod.ext
    · exact map_add f x y
    · apply Subtype.ext
      change x+y-f (x+y) • v=(x-f x • v)+(y-f y • v)
      rw [map_add,add_smul]
      abel
  map_smul' a x := by
    apply Prod.ext
    · exact map_smul f a x
    · apply Subtype.ext
      change a • x-f (a • x) • v=a • (x-f x • v)
      simp [smul_sub,smul_smul]

theorem splitOff_self (f : V →ₗ[F₂] F₂) (v : V) (hv : f v=1) :
    splitOff f v hv v=(1,0) := by
  apply Prod.ext
  · exact hv
  · apply Subtype.ext
    simp [splitOff,hv]

/-- A chosen nonzero vector can be made the first coordinate in dimension m+1. -/
theorem exists_coordinates_with_first [Module.Finite F₂ V] (m : ℕ)
    (hk : Module.finrank F₂ V=m+1) (v : V) (hv : v≠0) :
    ∃ e : V ≃ₗ[F₂] (F₂ × Word (Fin m)),e v=(1,0) := by
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero F₂ hv
  have hf1 : f v=1 := (by decide : ∀ a : F₂,a≠0 → a=1) (f v) hf
  have hfn : f≠0 := by intro h; simp [h] at hf
  have hr := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (functional_surjective f hfn),finrank_top,
    Module.finrank_self,hk] at hr
  have hker : Module.finrank F₂ (LinearMap.ker f)=m := by omega
  let eker : LinearMap.ker f ≃ₗ[F₂] Word (Fin m) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [Word] using hker)
  refine ⟨(splitOff f v hf1).trans ((LinearEquiv.refl F₂ F₂).prodCongr eker),?_⟩
  simp [splitOff_self]

#print axioms exists_coordinates_with_first
end
end Binary97
