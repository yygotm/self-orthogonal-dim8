import Basics

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators

/-- Internal interface, definitionally identical to the self-contained WardBinary in Main. -/
def WardAssumption : Prop :=
  ∀ (n k d r : ℕ) (C : Code (Fin n)),
    1 ≤ k → 1 ≤ d → Module.finrank F₂ C = k → n = griesmer k d →
    MinWeight C d → 2 ^ r ∣ d → ∀ x ∈ C, 2 ^ r ∣ weight x

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Transport along a coordinate bijection, including the residual subtype case. -/
def reindex (e : ι ≃ κ) : Word ι ≃ₗ[F₂] Word κ where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by ext i; simp
  right_inv y := by ext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem weight_reindex (e : ι ≃ κ) (x : Word ι) : weight (reindex e x) = weight x := by
  have h := Fintype.sum_equiv e (fun i => sign (x i))
    (fun j => sign ((reindex e x) j)) (by intro i; simp [reindex])
  rw [sign_sum_weight,sign_sum_weight] at h
  change (Fintype.card ι : ℤ) - 2 * (weight x : ℤ) =
    (Fintype.card κ : ℤ) - 2 * (weight (reindex e x) : ℤ) at h
  have hc := Fintype.card_congr e
  rw [hc] at h
  omega

/-- Ward applies to any finite coordinate type, by relabeling it with Fin(card). -/
theorem ward_finite (hWard : WardAssumption) (C : Code ι) {k d r : ℕ}
    (hkpos : 1 ≤ k) (hdpos : 1 ≤ d) (hk : Module.finrank F₂ C = k)
    (heq : Fintype.card ι = griesmer k d) (hd : MinWeight C d) (hdiv : 2^r ∣ d) :
    ∀ x ∈ C, 2^r ∣ weight x := by
  let e := reindex (Fintype.equivFin ι)
  let E := C.map e.toLinearMap
  have hr : Module.finrank F₂ E = k := by
    exact (e.finrank_map_eq C).trans hk
  have hm : MinWeight E d := by
    rintro y ⟨x,hx,rfl⟩ hn
    have hx0 : x ≠ 0 := by intro h; apply hn; simp [h]
    change d ≤ weight (e x)
    rw [show weight (e x) = weight x from weight_reindex _ _]
    exact hd x hx hx0
  have hv := hWard (Fintype.card ι) k d r E hkpos hdpos hr heq hm hdiv
  intro x hx
  have h := hv (e x) ⟨x,hx,rfl⟩
  rwa [show weight (e x) = weight x from weight_reindex _ _] at h

#print axioms ward_finite
end
end Binary97
