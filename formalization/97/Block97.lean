import Canonical97
import Autocorrelation

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators

def standardForm (α : F₂) (τ : Word (Fin 4)) (β : Word (Fin 2)) : StandardSpace →ₗ[F₂] F₂ where
  toFun p := p.1.1*α + binaryForm p.1.2 τ + binaryForm p.2 β
  map_add' p q := by simp [binaryForm,add_mul,Finset.sum_add_distrib,add_assoc,add_left_comm,add_comm]
  map_smul' a p := by simp [binaryForm,mul_assoc,Finset.mul_sum,mul_add]

def standardSum (z : Word Index97) (α : F₂) (τ : Word (Fin 4)) (β : Word (Fin 2)) : ℤ :=
  ∑ i,sign (z i)*sign (standardForm α τ β (standardColumn97 i))

def blockP (z : Word Index97) (b : NonzeroTwo) (t : Word (Fin 4)) : ℤ :=
  sign (z (some (b,t,0)))+sign (z (some (b,t,1)))

def blockQ (z : Word Index97) (b : NonzeroTwo) (t : Word (Fin 4)) : ℤ :=
  if t=0 then -blockP z b t else sign (z (some (b,t,0)))-sign (z (some (b,t,1)))

theorem sum_binary (f : F₂ → ℤ) : (∑ a,f a)=f 0+f 1 := by
  have hu : (Finset.univ : Finset F₂)={0,1} := by decide
  rw [hu]
  simp

theorem standard_block_zero (z : Word Index97) (b : NonzeroTwo) (t τ : Word (Fin 4)) (β : Word (Fin 2)) :
    (∑ a : F₂,sign (z (some (b,t,a)))*sign (standardForm 0 τ β (standardColumn97 (some (b,t,a)))))=
      blockP z b t*sign (binaryForm t τ)*sign (binaryForm b.val β) := by
  rw [sum_binary]
  simp only [standardColumn97,standardForm,LinearMap.coe_mk,AddHom.coe_mk,mul_zero,zero_add,sign_add,blockP]
  ring

theorem standard_block_one (z : Word Index97) (b : NonzeroTwo) (t τ : Word (Fin 4)) (β : Word (Fin 2)) :
    (∑ a : F₂,sign (z (some (b,t,a)))*sign (standardForm 1 τ β (standardColumn97 (some (b,t,a)))))=
      blockQ z b t*sign (binaryForm t τ)*sign (binaryForm b.val β) := by
  rw [sum_binary]
  have h0 : sign (0 : F₂)=1 := rfl
  have h1 : sign (1 : F₂)= -1 := by decide
  by_cases ht : t=0
  · simp only [standardColumn97,standardForm,LinearMap.coe_mk,AddHom.coe_mk,blockQ,blockP,
      if_pos ht,mul_one,sign_add,h1]
    ring
  · simp only [standardColumn97,standardForm,LinearMap.coe_mk,AddHom.coe_mk,blockQ,
      if_neg ht,mul_one,zero_add,sign_add,h0,h1]
    ring

theorem standard_sum_zero (z : Word Index97) (τ : Word (Fin 4)) (β : Word (Fin 2)) :
    standardSum z 0 τ β = sign (z none)+quotientSum (fun b => walsh (blockP z b) τ) β := by
  unfold standardSum
  rw [Fintype.sum_option]
  simp only [Fintype.sum_prod_type]
  simp_rw [standard_block_zero]
  simp only [← Finset.sum_mul]
  simp [standardColumn97,standardForm,binaryForm,sign,quotientSum,walsh,weightedFourier]

theorem standard_sum_one (z : Word Index97) (τ : Word (Fin 4)) (β : Word (Fin 2)) :
    standardSum z 1 τ β = -sign (z none)+quotientSum (fun b => walsh (blockQ z b) τ) β := by
  unfold standardSum
  rw [Fintype.sum_option]
  simp only [Fintype.sum_prod_type]
  simp_rw [standard_block_one]
  simp only [← Finset.sum_mul]
  simp [standardColumn97,standardForm,binaryForm,sign,quotientSum,walsh,weightedFourier]

#print axioms standard_sum_zero
#print axioms standard_sum_one
end
end Binary97
