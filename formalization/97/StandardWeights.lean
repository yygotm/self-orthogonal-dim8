import Joint
import Coordinates

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem binary_full_weight_unique (x y : Word ι)
    (hx : weight x=Fintype.card ι) (hy : weight y=Fintype.card ι) : x=y := by
  have hsx : support x=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa [weight] using hx.ge)
  have hsy : support y=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa [weight] using hy.ge)
  funext i
  have hxi : x i≠0 := (Finset.mem_filter.mp (show i∈support x by rw [hsx]; exact Finset.mem_univ i)).2
  have hyi : y i≠0 := (Finset.mem_filter.mp (show i∈support y by rw [hsy]; exact Finset.mem_univ i)).2
  have hbit : ∀ a b : F₂,a≠0 → b≠0 → a=b := by decide
  exact hbit _ _ hxi hyi

def vWeight (p : F₂ × Word (Fin 4)) : ℕ :=
  if p.2=0 then if p.1=0 then 0 else 16 else 8

def wWeight (p : Word (Fin 2)) : ℕ := if p=0 then 0 else 2

theorem eight16_coordinates (E : Code ι) [Fintype E]
    (hlen : Fintype.card ι=16) (hk : Module.finrank F₂ E=5)
    (hfull : FullLength E) (h8 : ∀x∈E,weight x%8=0) :
    ∃ e : E ≃ₗ[F₂] (F₂ × Word (Fin 4)),∀ x : E,weight x.val=vWeight (e x) := by
  obtain ⟨v,hv⟩ := eight16_full_word E hlen hk hfull h8
  have hv0 : v≠0 := by intro h; subst v; simp at hv
  obtain ⟨e,he⟩ := exists_coordinates_with_first 4 hk v hv0
  refine ⟨e,?_⟩
  intro x
  by_cases ht : (e x).2=0
  · by_cases ha : (e x).1=0
    · have hz : x=0 := e.injective (by rw [map_zero]; exact Prod.ext ha ht)
      subst x; simp [vWeight]
    · have ha1 : (e x).1=1 := (by decide : ∀ a : F₂,a≠0 → a=1) _ ha
      have hxv : x=v := e.injective (by rw [he]; exact Prod.ext ha1 ht)
      subst x; simp [vWeight,he,hv]
  · have hx0 : x≠0 := by intro h; subst x; simp at ht
    have hxv : x≠v := by intro h; subst x; simp [he] at ht
    have hp := weight_pos_of_ne_zero x.val (fun he => hx0 (Subtype.ext he))
    have hu := weight_le_length x.val
    have hw := h8 x.val x.property
    have hnot16 : weight x.val≠16 := by
      intro h
      exact hxv (Subtype.ext (binary_full_weight_unique x.val v.val (h.trans hlen.symm) (hv.trans hlen.symm)))
    have hew : weight x.val=8 := by omega
    simp [vWeight,ht,hew]

theorem even3_weight (E : Code ι) (hlen : Fintype.card ι=3)
    (heven : ∀x∈E,weight x%2=0) (x : E) :
    weight x.val=if x=0 then 0 else 2 := by
  by_cases hx : x=0
  · subst x; simp
  · have hp := weight_pos_of_ne_zero x.val (fun he => hx (Subtype.ext he))
    have hu := weight_le_length x.val
    have hw := heven x.val x.property
    have hew : weight x.val=2 := by omega
    simp [hew,hx]

abbrev StandardSpace := (F₂ × Word (Fin 4)) × Word (Fin 2)

theorem d97_standard_weights (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι=97) (hk : Module.finrank F₂ D=7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D) :
    ∃ e : (D →ₗ[F₂] F₂) ≃ₗ[F₂] StandardSpace,∀ g,
      weight (evaluationMap (weightWords D 52) g)=vWeight (e g).1 ∧
      weight (evaluationMap (weightWords D 64) g)=wWeight (e g).2 := by
  let E := evaluationCode (weightWords D 52)
  let F := evaluationCode (weightWords D 64)
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype F := Fintype.ofFinite F
  have hp := d97_V_parameters hWard D hlen hk hD hd hfull
  have h8 := d97_V_eight_divisible hWard D hlen hk hD hd hfull
  have haux := (d97_auxiliary_weights hWard D hlen hk hD hd hfull).1
  have heven : ∀x∈F,weight x%2=0 := by
    rintro x ⟨g,rfl⟩
    have h := haux g
    have hv := h8 (evaluationMap (weightWords D 52) g) ⟨g,rfl⟩
    omega
  obtain ⟨eE,hE⟩ := eight16_coordinates E (by simpa using hp.1) hp.2.1
    (evaluation_full (weightWords D 52) (by simp [weightWords,weight_zero])) h8
  let eF : F ≃ₗ[F₂] Word (Fin 2) := LinearEquiv.ofFinrankEq _ _
    (by simpa [Word] using d97_W_parameters hWard D hlen hk hD hd hfull)
  let j := d97_joint_equiv hWard D hlen hk hD hd hfull
  let e := j.trans (eE.prodCongr eF)
  refine ⟨e,fun g => ⟨?_,?_⟩⟩
  · exact hE (j g).1
  · have h := even3_weight F (by simpa using hp.2.2) heven (j g).2
    change weight (j g).2.val=wWeight (eF (j g).2)
    simpa [wWeight] using h

#print axioms d97_standard_weights
end
end Binary97
