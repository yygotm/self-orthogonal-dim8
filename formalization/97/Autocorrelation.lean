import Fourier97

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators

/-- Translation by a nonzero vector pairs a shift-invariant set into pairs. -/
theorem shift_invariant_even {m : ℕ} (S : Finset (Word (Fin m)))
    (h : Word (Fin m)) (hh : h≠0)
    (hS : ∀ x,x+h ∈ S ↔ x ∈ S) : S.card%2=0 := by
  have hi : ∃ i,h i≠0 := by
    by_contra he
    push_neg at he
    exact hh (funext he)
  obtain ⟨i,hi⟩ := hi
  have hbit : ∀ a b : F₂,b≠0 → ((a+b=0) ↔ a≠0) := by decide
  have hc : (S.filter fun x => x i=0).card=(S.filter fun x => x i≠0).card := by
    apply Finset.card_bij (fun x _ => x+h)
    · intro x hx
      obtain ⟨hxS,hxi⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨(hS x).mpr hxS,?_⟩
      change x i+h i≠0
      simpa [hxi] using hi
    · intro x hx y hy he
      exact add_right_cancel he
    · intro y hy
      obtain ⟨hyS,hyi⟩ := Finset.mem_filter.mp hy
      refine ⟨y+h,Finset.mem_filter.mpr ⟨(hS y).mpr hyS,?_⟩,?_⟩
      · exact (hbit (y i) (h i) hi).mpr hyi
      · simp only [add_assoc,word_add_self,add_zero]
  have hs := Finset.card_filter_add_card_filter_not (s := S) (fun x => x i=0)
  rw [← hc] at hs
  omega

theorem autocorrelation_sign_formula {m : ℕ} (z : Word (Word (Fin m)))
    (h : Word (Fin m)) :
    autocorrelation (fun x => sign (z x)) h = (2^m : ℤ)-4*(weight z : ℤ)+
      4*((Finset.univ.filter fun x => z x≠0 ∧ z (x+h)≠0).card : ℤ) := by
  have hbit : ∀ a b : F₂,sign a*sign b = 1-2*(if a≠0 then (1 : ℤ) else 0)-
      2*(if b≠0 then 1 else 0)+4*(if a≠0 ∧ b≠0 then 1 else 0) := by decide
  have hs : (∑ x : Word (Fin m),if z (x+h)≠0 then (1 : ℤ) else 0)=
      ∑ x : Word (Fin m),if z x≠0 then 1 else 0 := by
    apply Fintype.sum_equiv (Equiv.addRight h)
    intro x; rfl
  unfold autocorrelation
  simp_rw [hbit]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hs]
  simp only [Finset.sum_boole,weight,support]
  simp [Word,F₂,ZMod.card]
  <;> ring

/-- The parity obstruction in section 7: odd negative support forces R(h)=4 mod 8. -/
theorem autocorrelation_odd_mod8 (z : Word (Word (Fin 5)))
    (hz : weight z%2=1) (h : Word (Fin 5)) (hh : h≠0) :
    autocorrelation (fun x => sign (z x)) h%8=4 := by
  let S := Finset.univ.filter fun x => z x≠0 ∧ z (x+h)≠0
  have hS (x : Word (Fin 5)) : x+h∈S ↔ x∈S := by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,add_assoc,
      word_add_self,add_zero]
    exact and_comm
  have he := shift_invariant_even S h hh hS
  have hf := autocorrelation_sign_formula z h
  change autocorrelation (fun x => sign (z x)) h = 32-4*(weight z : ℤ)+4*(S.card : ℤ) at hf
  omega

/-- A Boolean sign vector of length 32 cannot have every Walsh coefficient in ±2,±6. -/
theorem no_boolean_walsh_two_six (z : Word (Word (Fin 5)))
    (hv : ∀ v,walsh (fun x => sign (z x)) v = -6 ∨
      walsh (fun x => sign (z x)) v = -2 ∨
      walsh (fun x => sign (z x)) v = 2 ∨
      walsh (fun x => sign (z x)) v = 6) : False := by
  let s := fun x => sign (z x)
  have hc : Fintype.card (Word (Fin 5))=32 := by simp [Word,F₂,ZMod.card]
  have hsquare (x : Word (Fin 5)) : s x^2=1 := by simpa [s,pow_two] using sign_square (z x)
  have h2 : ∑ v,walsh s v^2=1024 := by
    rw [walsh_parseval]
    simp [hsquare,hc]
  have h4 := fourth_value_32 (walsh s) hc hv h2
  have h0 : walsh s 0 = 32-2*(weight z : ℤ) := by
    change (∑ x,s x*sign (binaryForm x 0)) = _
    simp only [map_zero,sign,ite_true,mul_one]
    simpa [s,hc,weight,support] using sign_sum_weight z
  have hz : weight z%2=1 := by
    rcases hv 0 with h | h | h | h <;> change walsh s 0 = _ at h <;> omega
  have hr0 : autocorrelation s 0=32 := by
    simp only [autocorrelation,add_zero]
    have he (x : Word (Fin 5)) : s x*s x=1 := sign_square (z x)
    simp [he,hc]
  have hlo (h : Word (Fin 5)) :
      (if h=0 then (1024 : ℤ) else 16) ≤ autocorrelation s h^2 := by
    by_cases hh : h=0
    · subst h; simp [hr0]
    · have hm := autocorrelation_odd_mod8 z hz h hh
      change autocorrelation s h%8=4 at hm
      rw [if_neg hh]
      have ha : autocorrelation s h≤ -4 ∨ 4≤autocorrelation s h := by omega
      rcases ha with ha | ha <;> nlinarith [sq_nonneg (autocorrelation s h+4),sq_nonneg (autocorrelation s h-4)]
  have hsum := Finset.sum_le_sum (fun h (_ : h∈(Finset.univ : Finset (Word (Fin 5)))) => hlo h)
  have he : (∑ h : Word (Fin 5),if h=0 then (1024 : ℤ) else 16)=1520 := by
    have hp (h : Word (Fin 5)) : (if h=0 then (1024 : ℤ) else 16)=16+(if h=0 then 1008 else 0) := by split_ifs <;> norm_num
    simp_rw [hp]
    simp [Finset.sum_add_distrib,hc]
  rw [he] at hsum
  have hf := walsh_fourth_moment s
  rw [h4] at hf
  change (36352 : ℤ)=32*∑ h,autocorrelation s h^2 at hf
  nlinarith only [hsum,hf]

#print axioms no_boolean_walsh_two_six
end
end Binary97
