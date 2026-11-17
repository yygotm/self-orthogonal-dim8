import Canonical96
import Autocorrelation

namespace Binary97
open scoped BigOperators

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem standard96_multiplicity : ∀ p : StandardSpace96,
    (Finset.univ.filter fun i => standardColumn96 i=p).card=if p.2=0 then 0 else 1 := by decide

noncomputable section
open Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem d96_columns (D : Code ι) [Fintype D] (hlen : Fintype.card ι=96)
    (hk : Module.finrank F₂ D=7) (hD : DoublyEven D) (hd : MinWeight D 48)
    (hfull : FullLength D) :
    ∃ e : (D →ₗ[F₂] F₂) ≃ₗ[F₂] StandardSpace96,∃ ρ : ι ≃ Index96,
      ∀ i,standardColumn96 (ρ i)=e (coordinateForms D i) := by
  letI : DecidableEq StandardSpace96 := Classical.decEq _
  obtain ⟨e,he⟩ := d96_column_coordinates D hlen hk hD hd hfull
  refine ⟨e,?_⟩
  apply coordinate_equiv_of_multiplicity (fun i => e (coordinateForms D i)) standardColumn96
  intro p
  let g := e.symm p
  have hp : e g=p := e.apply_symm_apply p
  trans (Finset.univ.filter fun i => coordinateForms D i=g).card
  · apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [← hp]
    exact e.injective.eq_iff
  · have h1 := he g
    rw [hp] at h1
    have h2 : (Finset.univ.filter fun i : Index96 => standardColumn96 i=p).card=if p.2=0 then 0 else 1 := by
      convert standard96_multiplicity p using 2 <;> ext i <;> simp
    exact h1.trans h2.symm

def standardForm96 (τ : Word (Fin 5)) (β : Word (Fin 2)) : StandardSpace96 →ₗ[F₂] F₂ where
  toFun p := binaryForm p.1 τ + binaryForm p.2 β
  map_add' p q := by simp [binaryForm,add_mul,Finset.sum_add_distrib,add_assoc,add_left_comm,add_comm]
  map_smul' a p := by simp [binaryForm,mul_assoc,Finset.mul_sum,mul_add]

def standardSum96 (z : Word Index96) (τ : Word (Fin 5)) (β : Word (Fin 2)) : ℤ :=
  ∑ i,sign (z i)*sign (standardForm96 τ β (standardColumn96 i))

theorem standard96_sum (z : Word Index96) (τ : Word (Fin 5)) (β : Word (Fin 2)) :
    standardSum96 z τ β=quotientSum (fun b => walsh (fun t => sign (z (b,t))) τ) β := by
  unfold standardSum96 quotientSum walsh weightedFourier
  rw [Fintype.sum_prod_type]
  simp only [standardColumn96,standardForm96,LinearMap.coe_mk,AddHom.coe_mk,sign_add]
  simp only [Finset.sum_mul,mul_assoc]

/-- Section 7, including both possible values at the single inactive coordinate. -/
theorem no_standard96 (z : Word Index96) (H : ℤ) (hH : H=4 ∨ H=6)
    (hbound : ∀ τ β,standardSum96 z τ β≤H ∧ standardSum96 z τ β%8=H) : False := by
  let b := nonzeroTwoAt 0
  rcases hH with rfl | rfl
  · have hv (τ : Word (Fin 5)) := quotient_four
      (fun b => walsh (fun t => sign (z (b,t))) τ) (by
        intro β
        simpa only [standard96_sum] using hbound τ β) b
    have hpoint (τ : Word (Fin 5)) : walsh (fun t => sign (z (b,t))) τ^2≤16 := by
      rcases hv τ with h | h | h <;> rw [h] <;> norm_num
    have hs := Finset.sum_le_sum (fun τ (_ : τ∈(Finset.univ : Finset (Word (Fin 5)))) => hpoint τ)
    have hc : Fintype.card (Word (Fin 5))=32 := by simp [Word,F₂,ZMod.card]
    have hsq (t : Word (Fin 5)) : sign (z (b,t))^2=1 := by simpa only [pow_two] using sign_square (z (b,t))
    rw [walsh_parseval] at hs
    simp [hsq,hc] at hs
  · apply no_boolean_walsh_two_six (fun t => z (b,t))
    intro τ
    exact quotient_six (fun b => walsh (fun t => sign (z (b,t))) τ)
      (by intro β; simpa only [standard96_sum] using hbound τ β) b

#print axioms d96_columns
#print axioms no_standard96
end
end Binary97
