import Split68

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weightWords (D : Code ι) [Fintype D] (w : ℕ) : Finset D :=
  Finset.univ.filter fun x => weight x.val = w

def classWeight (D : Code ι) [Fintype D] (w : ℕ) (g : D →ₗ[F₂] F₂) : ℕ :=
  ((weightWords D w).filter fun x => g x ≠ 0).card

theorem d97_fourier_expression (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι = 97) (hk : Module.finrank F₂ D = 7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D) (x : D) :
    fourier (coordinateForms D) x = 1 - 8*(if weight x.val=52 then 1 else 0) -
      32*(if weight x.val=64 then 1 else 0) + (if x=0 then 96 else 0) := by
  have hf : fourier (coordinateForms D) x = 97 - 2*(weight x.val : ℤ) := by
    change (∑ i,sign (x.val i)) = _
    simpa [weight,support,hlen] using sign_sum_weight x.val
  by_cases hx : x=0
  · subst x; simp [hf,weight_zero]
  · rcases d97_support hWard D hlen hk hD hd hfull x hx with h | h | h <;>
      simp [hf,h,hx]

/-- Section 5.3: a+4b=28 and 2<=b<=7, before the auxiliary-code argument. -/
theorem d97_class_counts (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι = 97) (hk : Module.finrank F₂ D = 7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D) :
    (weightWords D 52).card + 4*(weightWords D 64).card = 28 ∧
    2 ≤ (weightWords D 64).card ∧ (weightWords D 64).card ≤ 7 ∧
    (weightWords D 52).card ≤ 20 := by
  let a := (weightWords D 52).card
  let b := (weightWords D 64).card
  have hc : Fintype.card D = 128 := code_card hk
  have hi52 : (∑ x : D, if weight x.val=52 then (1 : ℤ) else 0) = a := by
    simp [a,weightWords]
  have hi64 : (∑ x : D, if weight x.val=64 then (1 : ℤ) else 0) = b := by
    simp [b,weightWords]
  let F := fourier (coordinateForms D)
  have hfirst := projective_fourier_sum D ((fullLength_iff_forms D).mp hfull)
  have hexpr := d97_fourier_expression hWard D hlen hk hD hd hfull
  have hs1 : (∑ x : D,F x) = 128-8*(a : ℤ)-32*(b : ℤ)+96 := by
    simp_rw [show ∀ x,F x = _ from hexpr]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul,hi52,hi64]
    simp
  have hcount : a+4*b=28 := by
    change (∑ x : D,F x)=0 at hfirst
    omega
  have hpoly (x : D) : F x^2 = -6*F x+7+
      768*(if weight x.val=64 then 1 else 0)+(if x=0 then 9984 else 0) := by
    have hf : F x = 97-2*(weight x.val : ℤ) := by
      change (∑ i,sign (x.val i)) = _
      simpa [weight,support,hlen] using sign_sum_weight x.val
    by_cases hx : x=0
    · subst x; simp [hf,weight_zero]
    · rcases d97_support hWard D hlen hk hD hd hfull x hx with h | h | h <;>
        simp [hf,h,hx]
  have hs2 : (∑ x : D,F x^2) = 10880+768*(b : ℤ) := by
    simp_rw [hpoly]
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
      Finset.card_univ,hc,nsmul_eq_mul,hi64]
    change -6*(∑ x : D,fourier (coordinateForms D) x)+128*7+768*(b : ℤ)+
      (∑ x : D,if x=0 then (9984 : ℤ) else 0)=10880+768*(b : ℤ)
    rw [hfirst]
    simp
    <;> ring
  have hp := fourier_parseval (coordinateForms D)
  have hlo := collisionCount_lower (coordinateForms D)
  rw [hlen] at hlo
  have hlo' : (97 : ℤ) ≤ collisionCount (coordinateForms D) := by exact_mod_cast hlo
  change (∑ x : D,F x^2) = _ at hp
  rw [hc,hs2] at hp
  change 10880+768*(b : ℤ)=128*(collisionCount (coordinateForms D) : ℤ) at hp
  change a+4*b=28 ∧ 2≤b ∧ b≤7 ∧ a≤20
  omega

/-- Inverse Fourier coefficient, expressed as a weight of V plus four copies of W. -/
theorem d97_inverse_aux (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι = 97) (hk : Module.finrank F₂ D = 7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D)
    (g : D →ₗ[F₂] F₂) (hg : g ≠ 0) :
    classWeight D 52 g + 4*classWeight D 64 g =
      8 + 8*(Finset.univ.filter fun i => coordinateForms D i = g).card := by
  have hc : Fintype.card D = 128 := code_card hk
  have hcount := (d97_class_counts hWard D hlen hk hD hd hfull).1
  have hinv := fourier_dual_coefficient (coordinateForms D) g
  have he (x : D) : fourier (coordinateForms D) x * sign (g x) =
      sign (g x) - 8*(if weight x.val=52 then sign (g x) else 0) -
      32*(if weight x.val=64 then sign (g x) else 0) + (if x=0 then 96 else 0) := by
    rw [d97_fourier_expression hWard D hlen hk hD hd hfull]
    by_cases hx : x=0
    · subst x; simp [weight_zero]
    · simp only [hx,if_false,add_zero]
      split_ifs <;> ring
  simp_rw [he] at hinv
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hinv
  have hchar := character_sum g
  rw [if_neg hg] at hchar
  rw [hchar,hc] at hinv
  have h52 : (∑ x : D,if weight x.val=52 then sign (g x) else 0) =
      ((weightWords D 52).card : ℤ)-2*classWeight D 52 g := by
    rw [← Finset.sum_filter]
    exact sign_sum_finset (weightWords D 52) g
  have h64 : (∑ x : D,if weight x.val=64 then sign (g x) else 0) =
      ((weightWords D 64).card : ℤ)-2*classWeight D 64 g := by
    rw [← Finset.sum_filter]
    exact sign_sum_finset (weightWords D 64) g
  rw [h52,h64] at hinv
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true] at hinv
  omega

#print axioms d97_class_counts
#print axioms d97_inverse_aux
end
end Binary97
