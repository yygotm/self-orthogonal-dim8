import Geometry
import WardInterface

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- No even [13,5,6] code, by the first three moments and integrality. -/
theorem no_even_13_5_6 (C : Code ι) (hlen : Fintype.card ι = 13)
    (hk : Module.finrank F₂ C = 5) (hd : MinWeight C 6)
    (heven : ∀ x ∈ C, weight x % 2 = 0) : False := by
  letI : Fintype C := Fintype.ofFinite C
  have hc : Fintype.card C = 32 := code_card hk
  have hfull : FullLength C := fullLength_of_griesmer hk hd (by decide)
    (by rw [hlen]; decide)
  have hinj := projective_of_shortening_bound hk hd (by decide) hfull
    (by rw [hlen]; decide)
  have hweights (x : C) (hx : x ≠ 0) :
      weight x.val = 6 ∨ weight x.val = 8 ∨ weight x.val = 12 := by
    have hmax : weight x.val ≤ 13 := (weight_le_length x.val).trans_eq hlen
    have hmin := hd x.val x.property (fun h => hx (Subtype.ext h))
    have he := heven x.val x.property
    have hbound : weight x.val < 12 →
        griesmer 4 (6 - weight x.val / 2) + weight x.val ≤ 13 := by
      intro hh
      exact (even_residual_bound heven hk hd x hx hh).trans_eq hlen
    have htab : ∀ w : Fin 14, 6 ≤ w.val → w.val % 2 = 0 →
        (w.val < 12 → griesmer 4 (6-w.val/2)+w.val ≤ 13) →
        w.val = 6 ∨ w.val = 8 ∨ w.val = 12 := by decide
    exact htab ⟨weight x.val,by omega⟩ hmin he hbound
  let F := fourier (coordinateForms C)
  have hf (x : C) : F x = 13-2*(weight x.val : ℤ) := by
    change (∑ i, sign (x.val i)) = _
    simpa [weight,support,hlen] using sign_sum_weight x.val
  have hdiv (x : C) : (3 : ℤ) ∣ F x^2+2*F x := by
    by_cases hx : x = 0
    · subst x; simp [hf,weight_zero]
    · rcases hweights x hx with h | h | h <;> simp [hf,h]
  have hs := Finset.dvd_sum (fun x (_ : x ∈ (Finset.univ : Finset C)) => hdiv x)
  have hfirst := projective_fourier_sum C ((fullLength_iff_forms C).mp hfull)
  have hsecond := projective_fourier_square_sum C hinj
  change (3 : ℤ) ∣ ∑ x : C, (F x^2+2*F x) at hs
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  change (∑ x : C, F x^2) = _ at hsecond
  change (∑ x : C, F x) = 0 at hfirst
  rw [hsecond,hfirst,hlen,hc] at hs
  norm_num at hs

/-- Ward and the 13-coordinate residual eliminate every linear [41,6,20] code. -/
theorem no_linear_41_6_20 (hWard : WardAssumption) (C : Code ι)
    (hlen : Fintype.card ι = 41) (hk : Module.finrank F₂ C = 6)
    (hd : MinWeight C 20) : False := by
  letI : Fintype C := Fintype.ofFinite C
  have hv := ward_finite hWard C (r := 2) (by decide) (by decide) hk
    (by rw [hlen]; decide) hd (by decide)
  have hD : DoublyEven C := by
    intro x hx
    exact Nat.mod_eq_zero_of_dvd (hv x hx)
  have hC := doublyEven_selfOrthogonal hD
  have hc : Fintype.card C = 64 := code_card hk
  have hfull : FullLength C := fullLength_of_griesmer hk hd (by decide)
    (by rw [hlen]; decide)
  have hinj := projective_of_shortening_bound hk hd (by decide) hfull
    (by rw [hlen]; decide)
  have h28 (x : C) (hx : weight x.val = 28) : False := by
    have hn : x ≠ 0 := by intro h; subst x; simp at hx
    have hdim := residual_finrank hd hk x hn (by omega)
    have hlenR : Fintype.card (Outside x.val) = 13 := by
      have h := outside_card_add_weight x.val
      rw [hlen,hx] at h
      omega
    have hm : MinWeight (LinearMap.range (residualMap C x)) 6 := by
      intro y hy hny
      have h := residual_minWeight hd x y hy hny
      change 40 ≤ weight x.val + 2*weight y at h
      omega
    exact no_even_13_5_6 _ hlenR hdim hm (residual_even hC x)
  have hweights (x : C) (hx : x ≠ 0) :
      weight x.val = 20 ∨ weight x.val = 24 ∨ weight x.val = 32 := by
    have hmax : weight x.val ≤ 41 := (weight_le_length x.val).trans_eq hlen
    have hmin := hd x.val x.property (fun h => hx (Subtype.ext h))
    have he := hD x.val x.property
    have hn28 : weight x.val ≠ 28 := h28 x
    have hn40 : weight x.val ≠ 40 := by
      intro heq
      have hh := full_so_weight_ne_sub_one hC hfull x
      rw [hlen,heq] at hh
      omega
    have hbound : weight x.val < 40 →
        griesmer 5 (2*((20-weight x.val/2+1)/2)) + weight x.val ≤ 41 := by
      intro hh
      exact (so_residual_bound hC hk hd x hx hh).trans_eq hlen
    have htab : ∀ w : Fin 42, 20 ≤ w.val → w.val % 4 = 0 → w.val ≠ 28 →
        w.val ≠ 40 → (w.val < 40 → griesmer 5 (2*((20-w.val/2+1)/2))+w.val ≤ 41) →
        w.val = 20 ∨ w.val = 24 ∨ w.val = 32 := by decide
    exact htab ⟨weight x.val,by omega⟩ hmin he hn28 hn40 hbound
  let F := fourier (coordinateForms C)
  have hf (x : C) : F x = 41-2*(weight x.val : ℤ) := by
    change (∑ i,sign (x.val i)) = _
    simpa [weight,support,hlen] using sign_sum_weight x.val
  have hdiv (x : C) : (3 : ℤ) ∣ F x^2-1 := by
    by_cases hx : x = 0
    · subst x; simp [hf,weight_zero]
    · rcases hweights x hx with h | h | h <;> simp [hf,h]
  have hs := Finset.dvd_sum (fun x (_ : x ∈ (Finset.univ : Finset C)) => hdiv x)
  have hsecond := projective_fourier_square_sum C hinj
  change (3 : ℤ) ∣ ∑ x : C, (F x^2-1) at hs
  rw [Finset.sum_sub_distrib] at hs
  change (∑ x : C, F x^2) = _ at hsecond
  rw [hsecond,hlen,hc] at hs
  norm_num [hc] at hs

#print axioms no_even_13_5_6
#print axioms no_linear_41_6_20
end
end Binary97
