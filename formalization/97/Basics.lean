import Foundation

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Source: So52/Residual.lean residual_even, generalized to a finite coordinate type. -/
theorem residual_even {C : Code ι} (hC : SelfOrthogonal C)
    (c : C) (y : Outside c.val → F₂) (hy : y ∈ LinearMap.range (residualMap C c)) :
    residualWeight y % 2 = 0 := by
  obtain ⟨x, rfl⟩ := hy
  rw [residualWeight_eq_sdiff]
  have hx := even_weight hC x.property
  have hi := even_inter hC x.property c.property
  have hw := Finset.card_sdiff_add_card_inter (support x.val) (support c.val)
  change (support x.val \ support c.val).card + (support x.val ∩ support c.val).card =
    weight x.val at hw
  omega

/-- The residual exclusion in proof.md section 1; no full-length hypothesis needed. -/
theorem residual_griesmer_even {C : Code ι} {k d r : ℕ}
    (hC : SelfOrthogonal C) (hk : Module.finrank F₂ C = k + 1)
    (hd : MinWeight C d) (c : C) (hc : c ≠ 0) (hw : weight c.val < 2*d)
    (hr : 1 ≤ r)
    (hround : ∀ u : ℕ, u % 2 = 0 → 2*d ≤ weight c.val + 2*u → r ≤ u) :
    griesmer k r + weight c.val ≤ Fintype.card ι := by
  have hkR := residual_finrank hd hk c hc hw
  have hm : MinWeight (LinearMap.range (residualMap C c)) r := by
    intro y hy hn
    exact hround (weight y) (residual_even hC c y hy) (residual_minWeight hd c y hy hn)
  have hg := griesmer_bound k r (LinearMap.range (residualMap C c)) hkR hr hm
  have hn := outside_card_add_weight c.val
  omega

/-- Full length means every coordinate is nonzero on some word. -/
def FullLength (C : Code ι) : Prop := ∀ i, ∃ x : C, x.val i ≠ 0

theorem fullLength_iff_forms (C : Code ι) :
    FullLength C ↔ ∀ i, coordinateForms C i ≠ 0 := by
  constructor
  · intro h i hz
    obtain ⟨x,hx⟩ := h i
    exact hx (LinearMap.congr_fun hz x)
  · intro h i
    by_contra! hn
    apply h i
    exact LinearMap.ext hn

/-- Restriction to an arbitrary finite set of coordinates. -/
def restrictMap (C : Code ι) (s : Finset ι) : C →ₗ[F₂] (s → F₂) where
  toFun x i := x.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem weight_restrict (s : Finset ι) (x : Word ι)
    (hz : ∀ i, i ∉ s → x i = 0) :
    weight (fun i : s => x i.val) = weight x := by
  have hs : (support (fun i : s => x i.val)).image Subtype.val = support x := by
    ext i
    constructor
    · rintro hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      simpa [support] using hj
    · intro hi
      have hn : x i ≠ 0 := (Finset.mem_filter.mp hi).2
      have his : i ∈ s := by
        by_contra h
        exact hn (hz i h)
      exact Finset.mem_image.mpr ⟨⟨i,his⟩, by simpa [support] using hi, rfl⟩
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm.trans
    (congrArg Finset.card hs)

theorem restrictMap_injective (C : Code ι) (s : Finset ι)
    (hz : ∀ x : C, ∀ i, i ∉ s → x.val i = 0) :
    Function.Injective (restrictMap C s) := by
  intro x y h
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ s
  · exact congrFun h ⟨i,hi⟩
  · rw [hz x i hi,hz y i hi]

theorem restrict_griesmer (C : Code ι) (s : Finset ι) {k d : ℕ}
    (hk : Module.finrank F₂ C = k) (hd : MinWeight C d) (hdpos : 1 ≤ d)
    (hz : ∀ x : C, ∀ i, i ∉ s → x.val i = 0) : griesmer k d ≤ s.card := by
  have hr : Module.finrank F₂ (LinearMap.range (restrictMap C s)) = k := by
    rw [LinearMap.finrank_range_of_inj (restrictMap_injective C s hz),hk]
  have hm : MinWeight (LinearMap.range (restrictMap C s)) d := by
    rintro y ⟨x,rfl⟩ hn
    have hx : x.val ≠ 0 := by
      intro h
      apply hn
      funext i
      exact congrFun h i.val
    have hw := weight_restrict s x.val (hz x)
    change weight (restrictMap C s x) = weight x.val at hw
    rw [hw]
    exact hd x.val x.property hx
  simpa using griesmer_bound k d (LinearMap.range (restrictMap C s)) hr hdpos hm

/-- Griesmer equality forces full length, without using Ward. -/
theorem fullLength_of_griesmer {C : Code ι} {k d : ℕ}
    (hk : Module.finrank F₂ C = k) (hd : MinWeight C d) (hdpos : 1 ≤ d)
    (hg : Fintype.card ι = griesmer k d) : FullLength C := by
  intro i
  by_contra! hn
  let s := (Finset.univ : Finset ι).erase i
  have hz : ∀ x : C, ∀ j, j ∉ s → x.val j = 0 := by
    intro x j hj
    have he : j = i := by simpa [s] using hj
    subst j
    exact hn x
  have hb := restrict_griesmer C s hk hd hdpos hz
  have hc : s.card + 1 = Fintype.card ι := by
    exact Finset.card_erase_add_one (Finset.mem_univ i)
  omega

/-- A full SO code cannot have a word with exactly one zero coordinate (Lemma 3). -/
theorem full_so_weight_ne_sub_one {C : Code ι} (hC : SelfOrthogonal C)
    (hfull : FullLength C) (c : C) : weight c.val + 1 ≠ Fintype.card ι := by
  intro he
  have ho := outside_card_add_weight c.val
  have hcard : Fintype.card (Outside c.val) = 1 := by omega
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card (Outside c.val))
  obtain ⟨x,hx⟩ := hfull i.val
  let y := residualMap C c x
  have hy : y ≠ 0 := by
    intro hz
    exact hx (congrFun hz i)
  have hw : residualWeight y ≤ 1 := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Outside c.val))
      (fun j => y j ≠ 0)
    simpa [residualWeight,hcard] using h
  have heven := residual_even hC c y ⟨x,rfl⟩
  have hzero : residualWeight y = 0 := by omega
  apply hy
  funext j
  change y j = 0
  have hf : (Finset.univ.filter fun j => y j ≠ 0) = ∅ :=
    Finset.card_eq_zero.mp hzero
  by_contra hj
  have hm : j ∈ (Finset.univ.filter fun j => y j ≠ 0) := by simp [hj]
  rw [hf] at hm
  exact Finset.notMem_empty j hm

/-- The concrete rounded residual Griesmer bound used in weight screening. -/
theorem so_residual_bound {C : Code ι} {k d : ℕ}
    (hC : SelfOrthogonal C) (hk : Module.finrank F₂ C = k + 1)
    (hd : MinWeight C d) (c : C) (hc : c ≠ 0) (hw : weight c.val < 2*d) :
    griesmer k (2 * ((d - weight c.val / 2 + 1) / 2)) + weight c.val ≤
      Fintype.card ι := by
  have he := even_weight hC c.property
  apply residual_griesmer_even hC hk hd c hc hw
  · omega
  · intro u hu hdist
    omega

theorem weight_le_length (x : Word ι) : weight x ≤ Fintype.card ι :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

theorem code_card {C : Code ι} [Fintype C] {k : ℕ}
    (hk : Module.finrank F₂ C = k) : Fintype.card C = 2^k := by
  rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F₂),hk]
  simp [Nat.card_eq_fintype_card,F₂,ZMod.card]

/-- The unrounded residual inequality for an even, possibly non-SO parent. -/
theorem even_residual_bound {C : Code ι} {k d : ℕ}
    (heven : ∀ x ∈ C, weight x % 2 = 0) (hk : Module.finrank F₂ C = k+1)
    (hd : MinWeight C d) (c : C) (hc : c ≠ 0) (hw : weight c.val < 2*d) :
    griesmer k (d - weight c.val / 2) + weight c.val ≤ Fintype.card ι := by
  have he := heven c.val c.property
  have hkR := residual_finrank hd hk c hc hw
  have hm : MinWeight (LinearMap.range (residualMap C c)) (d - weight c.val / 2) := by
    intro y hy hn
    have h := residual_minWeight hd c y hy hn
    change 2*d ≤ weight c.val + 2*weight y at h
    omega
  have hp : 1 ≤ d - weight c.val / 2 := by omega
  have hg := griesmer_bound k (d - weight c.val / 2)
    (LinearMap.range (residualMap C c)) hkR hp hm
  have hn := outside_card_add_weight c.val
  omega

end
end Binary97
