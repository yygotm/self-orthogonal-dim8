import Geometry
import WardInterface

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The [25,6,12] auxiliary contradiction, using Ward and low moments. -/
theorem no_linear_25_6_12 (hWard : WardAssumption) (C : Code ι)
    (hlen : Fintype.card ι = 25) (hk : Module.finrank F₂ C = 6)
    (hd : MinWeight C 12) : False := by
  letI : Fintype C := Fintype.ofFinite C
  have hv := ward_finite hWard C (r := 2) (by decide) (by decide) hk
    (by rw [hlen]; decide) hd (by decide)
  have hD : DoublyEven C := fun x hx => Nat.mod_eq_zero_of_dvd (hv x hx)
  have hC := doublyEven_selfOrthogonal hD
  have hcard : Fintype.card C = 64 := code_card hk
  have hfull : FullLength C := fullLength_of_griesmer hk hd (by decide)
    (by rw [hlen]; decide)
  have hweights (x : C) (hx : x ≠ 0) : weight x.val = 12 ∨ weight x.val = 16 := by
    have hmax : weight x.val ≤ 25 := (weight_le_length x.val).trans_eq hlen
    have hmin := hd x.val x.property (fun h => hx (Subtype.ext h))
    have he := hD x.val x.property
    have hn24 : weight x.val ≠ 24 := by
      intro heq
      have hh := full_so_weight_ne_sub_one hC hfull x
      rw [hlen,heq] at hh
      omega
    have hbound : weight x.val < 24 →
        griesmer 5 (2*((12-weight x.val/2+1)/2)) + weight x.val ≤ 25 := by
      intro hh
      exact (so_residual_bound hC hk hd x hx hh).trans_eq hlen
    have htab : ∀ w : Fin 26, 12 ≤ w.val → w.val % 4 = 0 → w.val ≠ 24 →
        (w.val < 24 → griesmer 5 (2*((12-w.val/2+1)/2))+w.val ≤ 25) →
        w.val = 12 ∨ w.val = 16 := by decide
    exact htab ⟨weight x.val,by omega⟩ hmin he hn24 hbound
  let F := fourier (coordinateForms C)
  have hf (x : C) : F x = 25-2*(weight x.val : ℤ) := by
    change (∑ i,sign (x.val i)) = _
    simpa [weight,support,hlen] using sign_sum_weight x.val
  have hpoly (x : C) : F x ^ 2 = -6 * F x + 7 + (if x = 0 then 768 else 0) := by
    by_cases hx : x = 0
    · subst x; simp [hf,weight_zero]
    · rcases hweights x hx with h | h <;> simp [hf,h,hx]
  have hfirst := projective_fourier_sum C ((fullLength_iff_forms C).mp hfull)
  have hs : (∑ x : C, F x^2) = 1216 := by
    simp_rw [hpoly]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ,hcard,nsmul_eq_mul]
    change -6*(∑ x : C,fourier (coordinateForms C) x) + 64*7 +
      (∑ x : C,if x = 0 then (768 : ℤ) else 0) = 1216
    rw [hfirst]
    simp
  have hp := fourier_parseval (coordinateForms C)
  have hc := collisionCount_lower (coordinateForms C)
  have hc' : (25 : ℤ) ≤ collisionCount (coordinateForms C) := by
    rw [hlen] at hc
    exact_mod_cast hc
  change (∑ x : C,F x^2) = _ at hp
  rw [hcard,hs] at hp
  change (1216 : ℤ) = 64 * (collisionCount (coordinateForms C) : ℤ) at hp
  omega

/-- The [17,6,8] auxiliary contradiction: Ward leaves one nonzero weight. -/
theorem no_linear_17_6_8 (hWard : WardAssumption) (C : Code ι)
    (hlen : Fintype.card ι = 17) (hk : Module.finrank F₂ C = 6)
    (hd : MinWeight C 8) : False := by
  letI : Fintype C := Fintype.ofFinite C
  have hv := ward_finite hWard C (r := 3) (by decide) (by decide) hk
    (by rw [hlen]; decide) hd (by decide)
  have hD : DoublyEven C := by
    intro x hx
    exact Nat.mod_eq_zero_of_dvd (dvd_trans (by decide : (4 : ℕ) ∣ 8) (hv x hx))
  have hC := doublyEven_selfOrthogonal hD
  have hcard : Fintype.card C = 64 := code_card hk
  have hfull : FullLength C := fullLength_of_griesmer hk hd (by decide)
    (by rw [hlen]; decide)
  have hweights (x : C) (hx : x ≠ 0) : weight x.val = 8 := by
    have hmax : weight x.val ≤ 17 := (weight_le_length x.val).trans_eq hlen
    have hmin := hd x.val x.property (fun h => hx (Subtype.ext h))
    have he : weight x.val % 8 = 0 := Nat.mod_eq_zero_of_dvd (hv x.val x.property)
    have hn16 : weight x.val ≠ 16 := by
      intro heq
      have hh := full_so_weight_ne_sub_one hC hfull x
      rw [hlen,heq] at hh
      omega
    omega
  let F := fourier (coordinateForms C)
  have hf (x : C) : F x = 17-2*(weight x.val : ℤ) := by
    change (∑ i,sign (x.val i)) = _
    simpa [weight,support,hlen] using sign_sum_weight x.val
  have hpoly (x : C) : F x = 1 + (if x = 0 then 16 else 0) := by
    by_cases hx : x = 0
    · subst x; simp [hf,weight_zero]
    · simp [hf,hweights x hx,hx]
  have hfirst := projective_fourier_sum C ((fullLength_iff_forms C).mp hfull)
  change (∑ x : C,F x) = 0 at hfirst
  simp_rw [hpoly] at hfirst
  simp [Finset.sum_add_distrib,hcard] at hfirst

#print axioms no_linear_25_6_12
#print axioms no_linear_17_6_8
end
end Binary97
