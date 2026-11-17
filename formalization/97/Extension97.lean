import Block97

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators

theorem no_standard97_normalized (z : Word Index97) (hz : z none=0)
    (hbound : ∀ α τ β,standardSum z α τ β≤5 ∧ standardSum z α τ β%8=5) : False := by
  have hP (τ : Word (Fin 4)) (b : NonzeroTwo) :
      walsh (blockP z b) τ = -4 ∨ walsh (blockP z b) τ=0 ∨ walsh (blockP z b) τ=4 := by
    apply quotient_four (fun b => walsh (blockP z b) τ) _ b
    intro β
    have h := hbound 0 τ β
    rw [standard_sum_zero] at h
    simp only [hz,sign,ite_true] at h
    omega
  have hQ (τ : Word (Fin 4)) (b : NonzeroTwo) :
      walsh (blockQ z b) τ = -6 ∨ walsh (blockQ z b) τ = -2 ∨
      walsh (blockQ z b) τ=2 ∨ walsh (blockQ z b) τ=6 := by
    apply quotient_six (fun b => walsh (blockQ z b) τ) _ b
    intro β
    have h := hbound 1 τ β
    rw [standard_sum_one] at h
    simp only [hz,sign,ite_true] at h
    omega
  let b := nonzeroTwoAt 0
  have hp (τ : Word (Fin 4)) : walsh (blockP z b) τ^2≤16 := by
    rcases hP τ b with h | h | h <;> rw [h] <;> norm_num
  have hq (τ : Word (Fin 4)) : walsh (blockQ z b) τ^2≤36 := by
    rcases hQ τ b with h | h | h | h <;> rw [h] <;> norm_num
  have hc : Fintype.card (Word (Fin 4))=16 := by simp [Word,F₂,ZMod.card]
  have hpsum := Finset.sum_le_sum (fun τ (_ : τ∈(Finset.univ : Finset (Word (Fin 4)))) => hp τ)
  have hqsum := Finset.sum_le_sum (fun τ (_ : τ∈(Finset.univ : Finset (Word (Fin 4)))) => hq τ)
  simp only [Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul] at hpsum hqsum
  rw [walsh_parseval] at hpsum hqsum
  have hpair (t : Word (Fin 4)) (ht : t≠0) : blockP z b t^2+blockQ z b t^2=4 := by
    have h0 := sign_square (z (some (b,t,0)))
    have h1 := sign_square (z (some (b,t,1)))
    simp only [blockP,blockQ,if_neg ht]
    nlinarith only [h0,h1]
  have hlo (t : Word (Fin 4)) :
      (if t=0 then (0 : ℤ) else 4)≤blockP z b t^2+blockQ z b t^2 := by
    by_cases ht : t=0
    · simp only [ht,ite_true]; positivity
    · rw [if_neg ht,hpair t ht]
  have hsum := Finset.sum_le_sum (fun t (_ : t∈(Finset.univ : Finset (Word (Fin 4)))) => hlo t)
  have he : (∑ t : Word (Fin 4),if t=0 then (0 : ℤ) else 4)=60 := by decide
  rw [he,Finset.sum_add_distrib] at hsum
  norm_num only [show (2^4 : ℤ)=16 from rfl] at hpsum hqsum
  nlinarith only [hsum,hpsum,hqsum]

def normalize97 (z : Word Index97) : Word Index97 :=
  fun i => z i+standardForm (z none) 0 0 (standardColumn97 i)

theorem normalize97_zero (z : Word Index97) : normalize97 z none=0 := by
  simp only [normalize97,standardColumn97,standardForm,LinearMap.coe_mk,AddHom.coe_mk,
    one_mul,map_zero,add_zero]
  exact (by decide : ∀ a : F₂,a+a=0) (z none)

theorem normalize97_sum (z : Word Index97) (α : F₂) (τ : Word (Fin 4)) (β : Word (Fin 2)) :
    standardSum (normalize97 z) α τ β=standardSum z (α+z none) τ β := by
  apply Finset.sum_congr rfl
  intro i _
  have he : standardForm (α+z none) τ β (standardColumn97 i)=
      standardForm (z none) 0 0 (standardColumn97 i)+standardForm α τ β (standardColumn97 i) := by
    simp [standardForm,binaryForm]
    <;> ring
  simp only [normalize97,he,sign_add]
  ring

theorem no_standard97 (z : Word Index97)
    (hbound : ∀ α τ β,standardSum z α τ β≤5 ∧ standardSum z α τ β%8=5) : False := by
  apply no_standard97_normalized (normalize97 z) (normalize97_zero z)
  intro α τ β
  rw [normalize97_sum]
  exact hbound _ _ _

#print axioms no_standard97
end
end Binary97
