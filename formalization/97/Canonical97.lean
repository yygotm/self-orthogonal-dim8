import StandardWeights
import BlockTypes

namespace Binary97
open scoped BigOperators

abbrev Index97 := Option (NonzeroTwo × (Word (Fin 4) × F₂))

def standardColumn97 : Index97 → StandardSpace
  | none => ((1,0),0)
  | some (b,t,a) => ((if t=0 then 1 else a,t),b.val)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Finite audit: 128 possible column vectors against the explicit 97 positions. -/
theorem standard97_inverse : ∀ p : StandardSpace,p≠0 →
    vWeight p.1+4*wWeight p.2=8+8*(Finset.univ.filter fun i => standardColumn97 i=p).card := by
  decide

set_option maxRecDepth 100000 in
theorem standard97_zero : (Finset.univ.filter fun i => standardColumn97 i=0).card=0 := by decide

theorem index97_card : Fintype.card Index97=97 := by decide

noncomputable section
open Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Classification of the full length-97 doubly-even subcode, as an actual coordinate bijection. -/
theorem d97_columns (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι=97) (hk : Module.finrank F₂ D=7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D) :
    ∃ e : (D →ₗ[F₂] F₂) ≃ₗ[F₂] StandardSpace,∃ ρ : ι ≃ Index97,
      ∀ i,standardColumn97 (ρ i)=e (coordinateForms D i) := by
  letI : DecidableEq StandardSpace := Classical.decEq _
  obtain ⟨e,he⟩ := d97_standard_weights hWard D hlen hk hD hd hfull
  refine ⟨e,?_⟩
  apply coordinate_equiv_of_multiplicity (fun i => e (coordinateForms D i)) standardColumn97
  intro p
  let g := e.symm p
  have hp : e g=p := e.apply_symm_apply p
  have hfilter : (Finset.univ.filter fun i => e (coordinateForms D i)=p)=
      (Finset.univ.filter fun i => coordinateForms D i=g) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [← hp]
    exact e.injective.eq_iff
  trans (Finset.univ.filter fun i => coordinateForms D i=g).card
  · apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [← hp]
    exact e.injective.eq_iff
  · by_cases hg : g=0
    · have hpz : p=0 := by rw [← hp,hg,map_zero]
      rw [hpz]
      have hzero : (Finset.univ.filter fun b : Index97 => standardColumn97 b=0).card=0 := by
        convert standard97_zero using 2 <;> ext i <;> simp
      rw [hzero]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have h := (Finset.mem_filter.mp hi).2
      exact ((fullLength_iff_forms D).mp hfull i) (h.trans hg)
    · have ha := d97_inverse_aux hWard D hlen hk hD hd hfull g hg
      have hV := (he g).1
      have hW := (he g).2
      rw [evaluation_weight] at hV hW
      change classWeight D 52 g=vWeight (e g).1 at hV
      change classWeight D 64 g=wWeight (e g).2 at hW
      have hpne : p≠0 := by intro hz; apply hg; apply e.injective; simpa [hp] using hz
      have hb : vWeight p.1+4*wWeight p.2=8+8*(Finset.univ.filter fun b : Index97 => standardColumn97 b=p).card := by
        convert standard97_inverse p hpne using 2 <;> congr 2 <;> ext i <;> simp
      rw [hp] at hV hW
      omega
  
#print axioms d97_columns
end
end Binary97
