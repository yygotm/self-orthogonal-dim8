import D97Moments

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem d96_support_initial (D : Code ι) (hlen : Fintype.card ι=96)
    (hk : Module.finrank F₂ D=7) (hD : DoublyEven D) (hd : MinWeight D 48)
    (x : D) (hx : x≠0) : weight x.val=48 ∨ weight x.val=64 ∨ weight x.val=96 := by
  have hmax : weight x.val≤96 := (weight_le_length x.val).trans_eq hlen
  have hmin := hd x.val x.property (fun he => hx (Subtype.ext he))
  have he := hD x.val x.property
  have hb : weight x.val<96 → griesmer 6 (2*((48-weight x.val/2+1)/2))+weight x.val≤96 := by
    intro hh
    exact (so_residual_bound (doublyEven_selfOrthogonal hD) hk hd x hx hh).trans_eq hlen
  have htab : ∀ w : Fin 97,48≤w.val → w.val%4=0 →
      (w.val<96 → griesmer 6 (2*((48-w.val/2+1)/2))+w.val≤96) →
      w.val=48 ∨ w.val=64 ∨ w.val=96 := by decide
  exact htab ⟨weight x.val,by omega⟩ hmin he hb

theorem d96_counts (D : Code ι) [Fintype D] (hlen : Fintype.card ι=96)
    (hk : Module.finrank F₂ D=7) (hD : DoublyEven D) (hd : MinWeight D 48)
    (hfull : FullLength D) :
    (weightWords D 64).card=3 ∧ (weightWords D 96).card=0 := by
  have hproj := projective_of_shortening_bound hk hd (by decide) hfull
    (by rw [hlen]; decide : Fintype.card ι<griesmer 6 48+2)
  have hc : Fintype.card D=128 := code_card hk
  let b := (weightWords D 64).card
  let c := (weightWords D 96).card
  let F := fourier (coordinateForms D)
  have hf (x : D) : F x=96-2*(weight x.val : ℤ) := by
    change (∑ i,sign (x.val i)) = _
    simpa [weight,support,hlen] using sign_sum_weight x.val
  have he (x : D) : F x = -32*(if weight x.val=64 then 1 else 0)-
      96*(if weight x.val=96 then 1 else 0)+(if x=0 then 96 else 0) := by
    by_cases hx : x=0
    · subst x; simp [hf,weight_zero]
    · rcases d96_support_initial D hlen hk hD hd x hx with h | h | h <;> simp [hf,h,hx]
  have he2 (x : D) : F x^2 = 1024*(if weight x.val=64 then 1 else 0)+
      9216*(if weight x.val=96 then 1 else 0)+(if x=0 then 9216 else 0) := by
    by_cases hx : x=0
    · subst x; simp [hf,weight_zero]
    · rcases d96_support_initial D hlen hk hD hd x hx with h | h | h <;> simp [hf,h,hx]
  have hb : (∑ x : D,if weight x.val=64 then (1 : ℤ) else 0)=b := by simp [b,weightWords]
  have hcc : (∑ x : D,if weight x.val=96 then (1 : ℤ) else 0)=c := by simp [c,weightWords]
  have h1 := projective_fourier_sum D ((fullLength_iff_forms D).mp hfull)
  have h2 := projective_fourier_square_sum D hproj
  change (∑ x,F x)=0 at h1
  change (∑ x,F x^2)=(Fintype.card D : ℤ)*Fintype.card ι at h2
  simp_rw [he] at h1
  simp_rw [he2] at h2
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    hb,hcc,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hc,hlen] at h1 h2
  change b=3 ∧ c=0
  omega

theorem d96_support (D : Code ι) [Fintype D] (hlen : Fintype.card ι=96)
    (hk : Module.finrank F₂ D=7) (hD : DoublyEven D) (hd : MinWeight D 48)
    (hfull : FullLength D) (x : D) (hx : x≠0) : weight x.val=48 ∨ weight x.val=64 := by
  rcases d96_support_initial D hlen hk hD hd x hx with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have hz := (d96_counts D hlen hk hD hd hfull).2
    have hp : 0<(weightWords D 96).card := Finset.card_pos.mpr ⟨x,by simp [weightWords,h]⟩
    omega

/-- Inverse transform gives the complement-of-a-subspace geometry without a classification table. -/
theorem d96_inverse (D : Code ι) [Fintype D] (hlen : Fintype.card ι=96)
    (hk : Module.finrank F₂ D=7) (hD : DoublyEven D) (hd : MinWeight D 48)
    (hfull : FullLength D) (g : D →ₗ[F₂] F₂) :
    classWeight D 64 g = 2*(Finset.univ.filter fun i => coordinateForms D i=g).card := by
  have hc : Fintype.card D=128 := code_card hk
  have hb := (d96_counts D hlen hk hD hd hfull).1
  have hf (x : D) : fourier (coordinateForms D) x=96-2*(weight x.val : ℤ) := by
    change (∑ i,sign (x.val i)) = _
    simpa [weight,support,hlen] using sign_sum_weight x.val
  have he (x : D) : fourier (coordinateForms D) x*sign (g x) =
      -32*(if weight x.val=64 then sign (g x) else 0)+(if x=0 then 96 else 0) := by
    by_cases hx : x=0
    · subst x; simp [hf,weight_zero]
    · rcases d96_support D hlen hk hD hd hfull x hx with h | h <;> simp [hf,h,hx]
  have hi := fourier_dual_coefficient (coordinateForms D) g
  simp_rw [he] at hi
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hi
  have hs : (∑ x : D,if weight x.val=64 then sign (g x) else 0)=
      ((weightWords D 64).card : ℤ)-2*classWeight D 64 g := by
    rw [← Finset.sum_filter]
    exact sign_sum_finset (weightWords D 64) g
  rw [hs,hb,hc] at hi
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hi
  omega

#print axioms d96_support
#print axioms d96_inverse
end
end Binary97
