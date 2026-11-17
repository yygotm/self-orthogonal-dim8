import AuxiliaryV

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem short_eight_numeric : ∀ a : Fin 21, ∀ r : Fin 8,
    0<a.val → a.val%4=0 → 0<r.val →
    (2^r.val : ℤ)*((a.val : ℤ)^2-47*a.val+512)=512 →
    a.val=16 ∧ r.val=5 := by decide

/-- Full projective eight-divisible codes of length at most twenty and rank at most seven. -/
theorem short_eight_parameters (E : Code ι) [Fintype E]
    (hn : 0<Fintype.card ι) (hn4 : Fintype.card ι%4=0) (hsmall : Fintype.card ι ≤ 20)
    (hr : Module.finrank F₂ E ≤ 7) (hfull : FullLength E)
    (hproj : Function.Injective (coordinateForms E))
    (h8 : ∀ x ∈ E,weight x%8=0) :
    Fintype.card ι=16 ∧ Module.finrank F₂ E=5 := by
  let n := Fintype.card ι
  let r := Module.finrank F₂ E
  have hrpos : 1≤r := by
    apply Submodule.one_le_finrank_iff.mpr
    intro he
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp hn
    obtain ⟨x,hx⟩ := hfull i
    have hz : x.val=0 := by simpa [he] using x.property
    exact hx (congrFun hz i)
  have hc : Fintype.card E=2^r := code_card rfl
  let F := fourier (coordinateForms E)
  have hfirst := projective_fourier_sum E ((fullLength_iff_forms E).mp hfull)
  have hsecond := projective_fourier_square_sum E hproj
  have hf (x : E) : F x=(n : ℤ)-2*(weight x.val : ℤ) := by
    change (∑ i,sign (x.val i)) = _
    simpa [n,weight,support] using sign_sum_weight x.val
  have hpoly (x : E) : F x^2-(2*n-48)*F x+((n : ℤ)-16)*(n-32)=
      if x=0 then 512 else 0 := by
    by_cases hx : x=0
    · subst x; simp [hf,weight_zero]; ring
    · have h0 : x.val≠0 := by simpa using hx
      have hw0 : 0<weight x.val := by
        by_contra hh
        apply h0
        funext i
        by_contra hi
        have hp : 0<(support x.val).card := Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
        change 0<weight x.val at hp
        omega
      have hwle := weight_le_length x.val
      have hw8 := h8 x.val x.property
      have hw : weight x.val=8 ∨ weight x.val=16 := by omega
      rcases hw with hw | hw <;> rw [hf,hw,if_neg hx] <;> push_cast <;> ring
  have hs := congrArg (fun f : E → ℤ => ∑ x,f x) (funext hpoly)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  change (∑ x,F x)=0 at hfirst
  change (∑ x,F x^2)=(Fintype.card E : ℤ)*n at hsecond
  rw [hfirst,hsecond,hc] at hs
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Nat.cast_pow,Nat.cast_ofNat] at hs
  have he : (2^r : ℤ)*((n : ℤ)^2-47*n+512)=512 := by nlinarith [hs]
  exact short_eight_numeric ⟨n,by omega⟩ ⟨r,by omega⟩ hn hn4 hrpos he

theorem d97_V_nonempty (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι=97) (hk : Module.finrank F₂ D=7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D) :
    0<(weightWords D 52).card := by
  by_contra hh
  have hs : weightWords D 52=∅ := Finset.card_eq_zero.mp (by omega)
  have hcount := (d97_class_counts hWard D hlen hk hD hd hfull).1
  have ht : (weightWords D 64).card=7 := by rw [hs,Finset.card_empty] at hcount; omega
  have ha := (d97_auxiliary_weights hWard D hlen hk hD hd hfull).2
  have hl (g : D →ₗ[F₂] F₂) (hg : g≠0) :
      2≤weight (evaluationMap (weightWords D 64) g) := by
    have h := ha g hg
    rw [evaluation_weight,hs] at h
    simp only [Finset.filter_empty,Finset.card_empty,zero_add] at h
    omega
  have hinj : Function.Injective (evaluationMap (weightWords D 64)) := by
    intro g h he
    by_contra hne
    have hgh : g-h≠0 := sub_ne_zero.mpr hne
    have hb := hl (g-h) hgh
    rw [map_sub,he,sub_self,weight_zero] at hb
    omega
  have hr : Module.finrank F₂ (evaluationCode (weightWords D 64))=7 := by
    rw [evaluationCode,LinearMap.finrank_range_of_inj hinj,Subspace.dual_finrank_eq,hk]
  have hmin : MinWeight (evaluationCode (weightWords D 64)) 2 := by
    rintro x ⟨g,rfl⟩ hx
    apply hl g
    intro he
    exact hx (by simp [he])
  have hb := griesmer_bound 7 2 (evaluationCode (weightWords D 64)) hr (by decide) hmin
  have hn : Fintype.card (weightWords D 64)=7 := by simpa using ht
  rw [hn] at hb
  have hg : griesmer 7 2=8 := by decide
  rw [hg] at hb
  omega

theorem d97_V_parameters (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι=97) (hk : Module.finrank F₂ D=7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D) :
    (weightWords D 52).card=16 ∧
    Module.finrank F₂ (evaluationCode (weightWords D 52))=5 ∧
    (weightWords D 64).card=3 := by
  let S := weightWords D 52
  let E := evaluationCode S
  letI : Fintype E := Fintype.ofFinite E
  have hcount := d97_class_counts hWard D hlen hk hD hd hfull
  have hr := (evaluationMap S).finrank_range_add_finrank_ker
  rw [Subspace.dual_finrank_eq,hk] at hr
  have hn : 0<Fintype.card S := by simpa [S] using d97_V_nonempty hWard D hlen hk hD hd hfull
  have hn4 : Fintype.card S%4=0 := by simpa [S] using (show (weightWords D 52).card%4=0 by omega)
  have hn20 : Fintype.card S≤20 := by simpa [S] using hcount.2.2.2
  have hfullE := evaluation_full S (by simp [S,weightWords,weight_zero])
  have hp := short_eight_parameters E hn hn4 hn20 (by change Module.finrank F₂ (LinearMap.range (evaluationMap S))≤7; omega)
    hfullE (evaluation_projective S) (d97_V_eight_divisible hWard D hlen hk hD hd hfull)
  have ha : (weightWords D 52).card=16 := by simpa [S] using hp.1
  exact ⟨ha,hp.2,by omega⟩

#print axioms short_eight_parameters
#print axioms d97_V_parameters
end
end Binary97
