import Coset96

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weight_restriction_card (s : Finset ι) (x : Word ι) :
    weight (fun i : s => x i.val)=(s.filter fun i => x i≠0).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨i.property,(Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj he
    exact Subtype.ext he
  · intro i hi
    exact ⟨⟨i,(Finset.mem_filter.mp hi).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩,rfl⟩

theorem weight_partition (s : Finset ι) (x : Word ι) :
    weight x=weight (fun i : s => x i.val)+weight (fun i : ↥(sᶜ) => x i.val) := by
  rw [weight_restriction_card,weight_restriction_card]
  have hs := Finset.card_filter_add_card_filter_not (s := support x) (fun i => i∈s)
  have h1 : (support x).filter (fun i => i∈s)=s.filter (fun i => x i≠0) := by
    ext i
    simp [support,and_comm]
  have h2 : (support x).filter (fun i => ¬i∈s)=sᶜ.filter (fun i => x i≠0) := by
    ext i
    simp [support,and_comm]
  rw [h1,h2] at hs
  exact hs.symm

def effectiveCode (D : Code ι) : Code (activeCoordinates D) :=
  LinearMap.range (restrictMap D (activeCoordinates D))

theorem effectiveCode_parameters (D : Code ι) {k d : ℕ}
    (hk : Module.finrank F₂ D=k) (hD : DoublyEven D) (hd : MinWeight D d) :
    Module.finrank F₂ (effectiveCode D)=k ∧ DoublyEven (effectiveCode D) ∧
    MinWeight (effectiveCode D) d ∧ FullLength (effectiveCode D) := by
  have hw (x : D) : weight (restrictMap D (activeCoordinates D) x)=weight x.val :=
    weight_restrict (activeCoordinates D) x.val (inactive_zero D x)
  refine ⟨?_,?_,?_,?_⟩
  · rw [effectiveCode,LinearMap.finrank_range_of_inj (restrictMap_injective D _ (inactive_zero D)),hk]
  · rintro y ⟨x,rfl⟩
    rw [hw]
    exact hD x.val x.property
  · rintro y ⟨x,rfl⟩ hy
    rw [hw]
    apply hd x.val x.property
    intro he
    apply hy
    funext i
    exact congrFun he i.val
  · intro i
    obtain ⟨x,hx⟩ := (Finset.mem_filter.mp i.property).2
    exact ⟨⟨restrictMap D (activeCoordinates D) x,⟨x,rfl⟩⟩,hx⟩

/-- Puncturing all inactive coordinates accounts for every branch in section 3. -/
theorem no_doubly_even_coset_97 (hWard : WardAssumption) (D : Code (Fin 97))
    (hk : Module.finrank F₂ D=7) (hD : DoublyEven D) (hd : MinWeight D 48)
    (c : Word (Fin 97)) (hcoset : ∀x∈D,46≤weight (c+x) ∧ weight (c+x)%4=2) : False := by
  let s := activeCoordinates D
  have hlo := effective_griesmer hk hd (by decide)
  have hg : griesmer 7 48=96 := by decide
  rw [hg] at hlo
  change 96≤s.card at hlo
  have hhi : s.card≤97 := (Finset.card_le_univ s).trans_eq (Fintype.card_fin _)
  have hcases : s.card=96 ∨ s.card=97 := by omega
  rcases hcases with hs | hs
  · let E := effectiveCode D
    letI : Fintype E := Fintype.ofFinite E
    have hp := effectiveCode_parameters D hk hD hd
    let c' : Word s := fun i => c i.val
    let ε := weight (fun i : ↥(sᶜ) => c i.val)
    have hε : ε≤1 := by
      have h := weight_le_length (fun i : ↥(sᶜ) => c i.val)
      simpa [Finset.card_compl,hs] using h
    apply d96_no_coset E (by simpa using hs) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 c' ε hε
    rintro y ⟨x,rfl⟩
    have he : weight (c+x.val)=weight (c'+restrictMap D s x)+ε := by
      have h := weight_partition s (c+x.val)
      have hz : (fun i : ↥(sᶜ) => (c+x.val) i.val)=(fun i : ↥(sᶜ) => c i.val) := by
        funext i
        have hx := inactive_zero D x i.val (Finset.mem_compl.mp i.property)
        simp [hx]
      rw [hz] at h
      exact h
    simpa only [he] using hcoset x.val x.property
  · have hfull : FullLength D := by
      have he : s=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hs])
      intro i
      have hi : i∈s := by rw [he]; exact Finset.mem_univ i
      exact (Finset.mem_filter.mp hi).2
    letI : Fintype D := Fintype.ofFinite D
    exact d97_no_coset hWard D (by simp) hk hD hd hfull c hcoset

#print axioms no_doubly_even_coset_97
end
end Binary97
