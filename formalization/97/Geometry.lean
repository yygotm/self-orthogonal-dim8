import Basics

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Any nonzero binary linear functional is surjective.
Source: So52/Kernel.lean q_surjective, generalized from q to an arbitrary map. -/
theorem functional_surjective {V : Type*} [AddCommGroup V] [Module F₂ V]
    (f : V →ₗ[F₂] F₂) (hf : f ≠ 0) : Function.Surjective f := by
  obtain ⟨x,hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  have hx1 : f x = 1 := (by decide : ∀ a : F₂, a ≠ 0 → a = 1) _ hx
  intro a
  fin_cases a
  · exact ⟨0,map_zero _⟩
  · exact ⟨x,hx1⟩

/-- Source: So52/Kernel.lean doublyEvenKernel_finrank. -/
theorem doublyEvenKernel_finrank {k : ℕ} {C : Code ι} (hC : SelfOrthogonal C)
    (hk : Module.finrank F₂ C = k+1) (hq : q C hC ≠ 0) :
    Module.finrank F₂ (doublyEvenKernel C hC) = k := by
  have hr := (q C hC).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (functional_surjective _ hq), finrank_top,
    Module.finrank_self,hk] at hr
  rw [doublyEvenKernel,Submodule.finrank_map_subtype_eq]
  omega

/-- Shortening at a coordinate, still represented at the original length with zeros. -/
def shortened (C : Code ι) (i : ι) : Code ι :=
  (LinearMap.ker (coordinateForms C i)).map C.subtype

theorem shortened_le (C : Code ι) (i : ι) : shortened C i ≤ C := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

theorem shortened_zero (C : Code ι) (i j : ι)
    (hij : coordinateForms C j = coordinateForms C i) {x : Word ι}
    (hx : x ∈ shortened C i) : x j = 0 := by
  obtain ⟨y,hy,rfl⟩ := hx
  change coordinateForms C j y = 0
  rw [hij]
  exact hy

theorem shortened_finrank {C : Code ι} {k : ℕ} (hk : Module.finrank F₂ C = k+1)
    (i : ι) (hi : coordinateForms C i ≠ 0) :
    Module.finrank F₂ (shortened C i) = k := by
  have hr := (coordinateForms C i).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (functional_surjective _ hi),finrank_top,
    Module.finrank_self,hk] at hr
  rw [shortened,Submodule.finrank_map_subtype_eq]
  omega

/-- If shortening twice would violate Griesmer, two columns cannot be equal. -/
theorem projective_of_shortening_bound {C : Code ι} {k d : ℕ}
    (hk : Module.finrank F₂ C = k+1) (hd : MinWeight C d) (hdpos : 1 ≤ d)
    (hfull : FullLength C) (hbound : Fintype.card ι < griesmer k d + 2) :
    Function.Injective (coordinateForms C) := by
  intro i j hij
  by_contra hne
  let D := shortened C i
  let s := ((Finset.univ : Finset ι).erase i).erase j
  have hkD : Module.finrank F₂ D = k :=
    shortened_finrank hk i ((fullLength_iff_forms C).mp hfull i)
  have hdD : MinWeight D d := by
    intro x hx hn
    exact hd x (shortened_le C i hx) hn
  have hz : ∀ x : D, ∀ a, a ∉ s → x.val a = 0 := by
    intro x a ha
    have haa : a = i ∨ a = j := by
      by_cases haj : a = j
      · exact Or.inr haj
      · exact Or.inl (by simpa [s,haj] using ha)
    rcases haa with ha | ha
    · rw [ha]
      exact shortened_zero C i i rfl x.property
    · rw [ha]
      exact shortened_zero C i j hij.symm x.property
  have hg := restrict_griesmer D s hkD hdD hdpos hz
  have hs1 : ((Finset.univ : Finset ι).erase i).card + 1 = Fintype.card ι :=
    Finset.card_erase_add_one (Finset.mem_univ i)
  have hj : j ∈ ((Finset.univ : Finset ι).erase i) := by simp [Ne.symm hne]
  have hs2 : s.card + 1 = ((Finset.univ : Finset ι).erase i).card :=
    Finset.card_erase_add_one hj
  omega

/-- Coordinates on which at least one word is nonzero. -/
def activeCoordinates (C : Code ι) : Finset ι :=
  Finset.univ.filter fun i => ∃ x : C, x.val i ≠ 0

theorem inactive_zero (C : Code ι) (x : C) (i : ι) (hi : i ∉ activeCoordinates C) :
    x.val i = 0 := by
  by_contra hx
  apply hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hx⟩

theorem effective_griesmer {C : Code ι} {k d : ℕ}
    (hk : Module.finrank F₂ C = k) (hd : MinWeight C d) (hp : 1 ≤ d) :
    griesmer k d ≤ (activeCoordinates C).card :=
  restrict_griesmer C (activeCoordinates C) hk hd hp (inactive_zero C)

theorem active_mono {C D : Code ι} (h : D ≤ C) : activeCoordinates D ⊆ activeCoordinates C := by
  intro i hi
  obtain ⟨x,hx⟩ := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨x.val,h x.property⟩,hx⟩

#print axioms projective_of_shortening_bound
end
end Binary97
