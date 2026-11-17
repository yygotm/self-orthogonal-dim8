import Basics

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators

/-- A 98-value arithmetic screen, independent of the existence of any code. -/
theorem min48_numeric_screen :
    ∀ w : Fin 98, 48 ≤ w.val → w.val % 2 = 0 → w.val ≠ 96 →
      (w.val < 96 → griesmer 7 (2*((48-w.val/2+1)/2)) + w.val ≤ 97) →
      w.val = 48 ∨ w.val = 64 := by decide

/-- proof.md section 2: the only possible nonzero weights are 48 and 64. -/
theorem min48_support (C : Code (Fin 97))
    (hk : Module.finrank F₂ C = 8) (hC : SelfOrthogonal C)
    (hd : MinWeight C 48) (x : C) (hx : x ≠ 0) :
    weight x.val = 48 ∨ weight x.val = 64 := by
  have hfull : FullLength C := fullLength_of_griesmer hk hd (by decide) (by decide)
  have hn : x.val ≠ 0 := fun h => hx (Subtype.ext h)
  have hl : weight x.val ≤ 97 := by simpa using weight_le_length x.val
  apply min48_numeric_screen ⟨weight x.val,by omega⟩
  · exact hd x.val x.property hn
  · exact even_weight hC x.property
  · intro h96
    change weight x.val = 96 at h96
    have h := full_so_weight_ne_sub_one hC hfull x
    simp only [Fintype.card_fin] at h
    omega
  · intro hw
    simpa using so_residual_bound hC hk hd x hx hw

/-- The exact dimension/orthogonality/distance hypotheses imply a contradiction.
First and second Fourier moments are the first three MacWilliams equations. -/
theorem no_so_97_8_48 :
    ¬ ∃ C : Code (Fin 97), Module.finrank F₂ C = 8 ∧
      SelfOrthogonal C ∧ MinWeight C 48 := by
  rintro ⟨C,hk,hC,hd⟩
  letI : Fintype C := Fintype.ofFinite C
  have hcard : Fintype.card C = 256 := code_card hk
  have hfull : FullLength C := fullLength_of_griesmer hk hd (by decide) (by decide)
  have hfirst := projective_fourier_sum C ((fullLength_iff_forms C).mp hfull)
  let F := fourier (coordinateForms C)
  have hf (x : C) : F x = 97 - 2 * (weight x.val : ℤ) := by
    change (∑ i, sign (x.val i)) = _
    simpa [weight,support] using sign_sum_weight x.val
  have hpoly (x : C) : F x ^ 2 = -30 * F x + 31 + (if x = 0 then 12288 else 0) := by
    by_cases hx : x = 0
    · subst x
      simp [hf,weight_zero]
    · rcases min48_support C hk hC hd x hx with hw | hw <;> simp [hf,hw,hx]
  have hs : (∑ x : C, F x ^ 2) = 20224 := by
    simp_rw [hpoly]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ,hcard,nsmul_eq_mul]
    change -30 * (∑ x : C, fourier (coordinateForms C) x) + 256 * 31 +
      (∑ x : C, if x = 0 then (12288 : ℤ) else 0) = 20224
    rw [hfirst]
    simp
  have hp := fourier_parseval (coordinateForms C)
  have hc := collisionCount_lower (coordinateForms C)
  have hc' : (97 : ℤ) ≤ collisionCount (coordinateForms C) := by exact_mod_cast hc
  change (∑ x : C, F x ^ 2) = _ at hp
  rw [hcard,hs] at hp
  change (20224 : ℤ) = 256 * (collisionCount (coordinateForms C) : ℤ) at hp
  omega

#print axioms no_so_97_8_48
end
end Binary97
