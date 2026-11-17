import VParameters
import PointGeometry
import D96

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weight_pos_of_ne_zero (x : Word ι) (hx : x≠0) : 0<weight x := by
  by_contra hh
  apply hx
  funext i
  by_contra hi
  have hp : 0<(support x).card := Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
  change 0<weight x at hp
  omega

theorem eight16_full_word (E : Code ι) [Fintype E] (hlen : Fintype.card ι=16)
    (hk : Module.finrank F₂ E=5) (hfull : FullLength E)
    (h8 : ∀ x∈E,weight x%8=0) : ∃ x : E,weight x.val=16 := by
  let F := fourier (coordinateForms E)
  have hf (x : E) : F x=16-2*(weight x.val : ℤ) := by
    change (∑ i,sign (x.val i)) = _
    simpa [weight,support,hlen] using sign_sum_weight x.val
  have he (x : E) : F x = (if x=0 then 16 else 0)-
      16*(if weight x.val=16 then 1 else 0) := by
    by_cases hx : x=0
    · subst x; simp [hf,weight_zero]
    · have hp := weight_pos_of_ne_zero x.val (fun he => hx (Subtype.ext he))
      have hu := weight_le_length x.val
      have hd := h8 x.val x.property
      have hw : weight x.val=8 ∨ weight x.val=16 := by omega
      rcases hw with h | h <;> simp [hf,h,hx]
  have hs := projective_fourier_sum E ((fullLength_iff_forms E).mp hfull)
  change (∑ x,F x)=0 at hs
  simp_rw [he] at hs
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_boole] at hs
  have hc : (Finset.univ.filter fun x : E => weight x.val=16).card=1 := by omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter fun x : E => weight x.val=16).card by omega)
  exact ⟨x,(Finset.mem_filter.mp hx).2⟩

theorem even3_parameters (E : Code ι) [Fintype E] (hlen : Fintype.card ι=3)
    (hfull : FullLength E) (heven : ∀ x∈E,weight x%2=0) :
    Module.finrank F₂ E=2 := by
  let r := Module.finrank F₂ E
  have hc := code_card (show Module.finrank F₂ E=r from rfl)
  have hr : r≤3 := by
    have h := Submodule.finrank_le E
    simpa [r,Word,hlen] using h
  let F := fourier (coordinateForms E)
  have hf (x : E) : F x=3-2*(weight x.val : ℤ) := by
    change (∑ i,sign (x.val i)) = _
    simpa [weight,support,hlen] using sign_sum_weight x.val
  have he (x : E) : F x = -1+(if x=0 then 4 else 0) := by
    by_cases hx : x=0
    · subst x; simp [hf,weight_zero]
    · have hp := weight_pos_of_ne_zero x.val (fun he => hx (Subtype.ext he))
      have hu := weight_le_length x.val
      have hd := heven x.val x.property
      have hw : weight x.val=2 := by omega
      simp [hf,hw,hx]
  have hs := projective_fourier_sum E ((fullLength_iff_forms E).mp hfull)
  change (∑ x,F x)=0 at hs
  simp_rw [he] at hs
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
  have hn : Fintype.card E=4 := by omega
  rw [hn] at hc
  change r=2
  interval_cases r <;> norm_num at *

theorem d97_affine_witness (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι=97) (hk : Module.finrank F₂ D=7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D) :
    ∃ g : D →ₗ[F₂] F₂,∀ x∈weightWords D 52,g x=1 := by
  let E := evaluationCode (weightWords D 52)
  letI : Fintype E := Fintype.ofFinite E
  have hp := d97_V_parameters hWard D hlen hk hD hd hfull
  have hf := evaluation_full (weightWords D 52) (by simp [weightWords,weight_zero])
  obtain ⟨x,hx⟩ := eight16_full_word E (by simpa using hp.1) hp.2.1 hf
    (d97_V_eight_divisible hWard D hlen hk hD hd hfull)
  obtain ⟨g,hg⟩ := x.property
  exact ⟨g,full_weight_evaluation (weightWords D 52) g (by rw [hg,hx,hp.1])⟩

theorem d97_W_parameters (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι=97) (hk : Module.finrank F₂ D=7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D) :
    Module.finrank F₂ (evaluationCode (weightWords D 64))=2 := by
  let E := evaluationCode (weightWords D 64)
  letI : Fintype E := Fintype.ofFinite E
  have hp := d97_V_parameters hWard D hlen hk hD hd hfull
  have h8 := d97_V_eight_divisible hWard D hlen hk hD hd hfull
  have haux := (d97_auxiliary_weights hWard D hlen hk hD hd hfull).1
  apply even3_parameters E (by simpa using hp.2.2)
    (evaluation_full (weightWords D 64) (by simp [weightWords,weight_zero]))
  rintro x ⟨g,rfl⟩
  have h := haux g
  have hv := h8 (evaluationMap (weightWords D 52) g) ⟨g,rfl⟩
  omega

#print axioms d97_affine_witness
#print axioms d97_W_parameters
end
end Binary97
