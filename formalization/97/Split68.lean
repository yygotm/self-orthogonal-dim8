import D97Support

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators

/-- The two-cell calculation of section 5.2, eliminating first weights 64 and 68.
The only cases are 4x4 pairs and a residual weight between 0 and 29. -/
theorem split68_numeric (a b j : ℕ)
    (ha : a=48 ∨ a=52 ∨ a=64 ∨ a=68)
    (hb : b=48 ∨ b=52 ∨ b=64 ∨ b=68)
    (hj : j ≤ 29) (hpair : a+b=68+2*j)
    (hbound : j<28 → griesmer 5 (14-j/2)+j ≤ 29) : a=48 ∨ a=52 := by
  have hg1 : griesmer 5 1 = 5 := by decide
  have hg2 : griesmer 5 2 = 6 := by decide
  have hg3 : griesmer 5 3 = 8 := by decide
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;> try omega
  all_goals interval_cases j <;> norm_num [hg1,hg2,hg3] at *

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The split residual constraints and the first two moments exclude weight 68. -/
theorem d97_weight_ne_68 (hWard : WardAssumption) (D : Code ι)
    (hlen : Fintype.card ι = 97) (hk : Module.finrank F₂ D = 7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D)
    (c : D) : weight c.val ≠ 68 := by
  intro hc
  letI : Fintype D := Fintype.ofFinite D
  have hcard : Fintype.card D = 128 := code_card hk
  have hC := doublyEven_selfOrthogonal hD
  have hc0 : c ≠ 0 := by intro h; subst c; simp at hc
  let R := LinearMap.range (residualMap D c)
  have hkR : Module.finrank F₂ R = 6 := residual_finrank hd hk c hc0 (by omega)
  have hlR : Fintype.card (Outside c.val) = 29 := by
    have h := outside_card_add_weight c.val
    rw [hlen,hc] at h
    omega
  have hmR : MinWeight R 14 := by
    intro y hy hn
    have h := residual_minWeight hd c y hy hn
    change 96 ≤ weight c.val + 2*weight y at h
    omega
  have heR : ∀ y ∈ R, weight y % 2 = 0 := residual_even hC c
  have hweights (x : D) (hx : x ≠ 0) (hxc : x ≠ c) :
      weight x.val = 48 ∨ weight x.val = 52 := by
    have hxc0 : x+c ≠ 0 := by
      intro he
      apply hxc
      exact Subtype.ext ((add_eq_zero_iff _ _).mp (congrArg Subtype.val he))
    have ha := d97_support_before68 hWard D hlen hk hD hd hfull x hx
    have hb := d97_support_before68 hWard D hlen hk hD hd hfull (x+c) hxc0
    let y : R := ⟨residualMap D c x,⟨x,rfl⟩⟩
    have hy0 : y ≠ 0 := by
      intro he
      have hz : x ∈ LinearMap.ker (residualMap D c) := congrArg Subtype.val he
      rcases residual_ker_words hd c (by omega) x hz with h | h
      · exact hx h
      · exact hxc h
    have hj : weight y.val ≤ 29 := (weight_le_length y.val).trans_eq hlR
    have hp := residual_weight_identity c x
    change weight x.val + weight (x+c).val = weight c.val + 2*weight y.val at hp
    rw [hc] at hp
    have hbound : weight y.val < 28 → griesmer 5 (14-weight y.val/2)+weight y.val ≤ 29 := by
      intro hh
      exact (even_residual_bound heR hkR hmR y hy0 hh).trans_eq hlR
    exact split68_numeric _ _ _ ha hb hj hp hbound
  let F := fourier (coordinateForms D)
  have hf (x : D) : F x = 97-2*(weight x.val : ℤ) := by
    change (∑ i,sign (x.val i)) = _
    simpa [weight,support,hlen] using sign_sum_weight x.val
  have hpoly (x : D) : F x^2 = -6*F x+7+
      (if x=0 then 9984 else 0)+(if x=c then 1280 else 0) := by
    by_cases hx : x=0
    · subst x; simp [hf,weight_zero,hc0,Ne.symm hc0]
    · by_cases hxc : x=c
      · subst x; simp [hf,hc,hc0]
      · rcases hweights x hx hxc with h | h <;> simp [hf,h,hx,hxc]
  have hfirst := projective_fourier_sum D ((fullLength_iff_forms D).mp hfull)
  have hs : (∑ x : D,F x^2) = 12160 := by
    simp_rw [hpoly]
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
      Finset.card_univ,hcard,nsmul_eq_mul]
    change -6*(∑ x : D,fourier (coordinateForms D) x)+128*7+
      (∑ x : D,if x=0 then (9984 : ℤ) else 0)+
      (∑ x : D,if x=c then (1280 : ℤ) else 0) = 12160
    rw [hfirst]
    simp
  have hp := fourier_parseval (coordinateForms D)
  have hlo := collisionCount_lower (coordinateForms D)
  rw [hlen] at hlo
  have hlo' : (97 : ℤ) ≤ collisionCount (coordinateForms D) := by exact_mod_cast hlo
  change (∑ x : D,F x^2) = _ at hp
  rw [hs,hcard] at hp
  change (12160 : ℤ) = 128*(collisionCount (coordinateForms D) : ℤ) at hp
  omega

theorem d97_support (hWard : WardAssumption) (D : Code ι)
    (hlen : Fintype.card ι = 97) (hk : Module.finrank F₂ D = 7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D)
    (x : D) (hx : x ≠ 0) :
    weight x.val = 48 ∨ weight x.val = 52 ∨ weight x.val = 64 := by
  have h := d97_support_before68 hWard D hlen hk hD hd hfull x hx
  have h68 := d97_weight_ne_68 hWard D hlen hk hD hd hfull x
  omega

#print axioms d97_weight_ne_68
#print axioms d97_support
end
end Binary97
