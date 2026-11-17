import Geometry

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pairwise support intersections divisible by four. -/
def IntersectionFour (C : Code ι) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, (support x ∩ support y).card % 4 = 0

/-- Projectivity and intersection divisibility rule out weight four. -/
theorem no_weight_four_of_intersections (C : Code ι)
    (hI : IntersectionFour C) (hinj : Function.Injective (coordinateForms C))
    (x : C) : weight x.val ≠ 4 := by
  intro hw
  have hsc : (support x.val).card = 4 := hw
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (support x.val).card)
  apply hij
  apply hinj
  ext y
  have hdiv := hI x.val x.property y.val y.property
  have hle := Finset.card_le_card (Finset.inter_subset_left :
    support x.val ∩ support y.val ⊆ support x.val)
  have hcases : (support x.val ∩ support y.val).card = 0 ∨
      (support x.val ∩ support y.val).card = 4 := by omega
  change y.val i = y.val j
  rcases hcases with he | he
  · have hempty := Finset.card_eq_zero.mp he
    have hzi : y.val i = 0 := by
      by_contra hn
      have hmem : i ∈ support x.val ∩ support y.val :=
        Finset.mem_inter.mpr ⟨hi,by simpa [support] using hn⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    have hzj : y.val j = 0 := by
      by_contra hn
      have hmem : j ∈ support x.val ∩ support y.val :=
        Finset.mem_inter.mpr ⟨hj,by simpa [support] using hn⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    rw [hzi,hzj]
  · have hall : support x.val ∩ support y.val = support x.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hni : y.val i ≠ 0 := by
      have hmem : i ∈ support x.val ∩ support y.val := by rw [hall]; exact hi
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hmem).2).2
    have hnj : y.val j ≠ 0 := by
      have hmem : j ∈ support x.val ∩ support y.val := by rw [hall]; exact hj
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hmem).2).2
    exact (by decide : ∀ a b : F₂, a ≠ 0 → b ≠ 0 → a=b) _ _ hni hnj

/-- Quarter-weight modulo two is linear when the intersections are four-divisible. -/
def quarterMap (C : Code ι) (hD : DoublyEven C) (hI : IntersectionFour C) : C →ₗ[F₂] F₂ where
  toFun x := (weight x.val / 4 : ℕ)
  map_add' x y := by
    change ((weight (x.val+y.val)/4 : ℕ) : F₂) =
      (weight x.val/4 : ℕ)+(weight y.val/4 : ℕ)
    rw [← Nat.cast_add]
    apply ZMod.val_injective
    simp only [ZMod.val_natCast]
    have h := weight_identity (support x.val) (support y.val)
    rw [← support_add] at h
    change weight (x.val+y.val)+2*(support x.val ∩ support y.val).card =
      weight x.val+weight y.val at h
    have hx := hD x.val x.property
    have hy := hD y.val y.property
    have hxy := hI x.val x.property y.val y.property
    omega
  map_smul' a x := by
    have ha : a=0 ∨ a=1 := (by decide : ∀ a : F₂,a=0 ∨ a=1) a
    rcases ha with rfl | rfl <;> simp

theorem quarterMap_zero_iff {C : Code ι} (hD : DoublyEven C) (hI : IntersectionFour C)
    (x : C) : quarterMap C hD hI x=0 ↔ weight x.val % 8=0 := by
  change ((weight x.val/4 : ℕ) : F₂)=0 ↔ _
  rw [ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero]
  have h := hD x.val x.property
  omega

/-- The coset-average step of proof.md section 5.3.
The character coefficient counts coordinates annihilated by the quarter-weight kernel. -/
theorem eight_divisible_of_short_projective (C : Code ι) [Fintype C]
    (hD : DoublyEven C) (hI : IntersectionFour C) (hfull : FullLength C)
    (hinj : Function.Injective (coordinateForms C)) (hlen : Fintype.card ι ≤ 20) :
    ∀ x ∈ C, weight x % 8=0 := by
  let q4 := quarterMap C hD hI
  have hqzero : q4=0 := by
    by_contra hq
    let F := fourier (coordinateForms C)
    let m := (Finset.univ.filter fun i => coordinateForms C i=q4).card
    have hm : m ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      apply hinj
      exact ((Finset.mem_filter.mp hi).2).trans ((Finset.mem_filter.mp hj).2.symm)
    have hchar := character_sum q4
    rw [if_neg hq] at hchar
    have hfirst := projective_fourier_sum C ((fullLength_iff_forms C).mp hfull)
    have htwist := fourier_dual_coefficient (coordinateForms C) q4
    have hpoint (x : C) : (1-sign (q4 x))*(F x+4) ≤ 0 := by
      by_cases hx : q4 x=0
      · simp [sign,hx]
      · have hneq : weight x.val % 8 ≠ 0 := by
          intro h
          exact hx ((quarterMap_zero_iff hD hI x).mpr h)
        have hfour := hD x.val x.property
        have hn4 := no_weight_four_of_intersections C hI hinj x
        have hmin : 12 ≤ weight x.val := by omega
        have hf : F x = (Fintype.card ι : ℤ)-2*(weight x.val : ℤ) := by
          change (∑ i,sign (x.val i)) = _
          exact sign_sum_weight x.val
        simp only [sign,hx,if_false] 
        have hn' : (Fintype.card ι : ℤ) ≤ 20 := by exact_mod_cast hlen
        have hw' : (12 : ℤ) ≤ weight x.val := by exact_mod_cast hmin
        omega
    have hsum := Finset.sum_nonpos (fun x (_ : x ∈ (Finset.univ : Finset C)) => hpoint x)
    have hexpand (x : C) : (1-sign (q4 x))*(F x+4) =
        F x-F x*sign (q4 x)+4-4*sign (q4 x) := by ring
    simp_rw [hexpand] at hsum
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
    change (∑ x : C,F x)=0 at hfirst
    change (∑ x : C,F x*sign (q4 x))=(Fintype.card C : ℤ)*m at htwist
    rw [hfirst,htwist,hchar] at hsum
    have hc : (0 : ℤ)<Fintype.card C := by exact_mod_cast Fintype.card_pos
    have hm' : (m : ℤ) ≤ 1 := by exact_mod_cast hm
    have hpos := mul_pos hc (by omega : (0 : ℤ)<4-m)
    nlinarith
  intro x hx
  apply (quarterMap_zero_iff hD hI ⟨x,hx⟩).mp
  change q4 ⟨x,hx⟩=0
  rw [hqzero]
  rfl

#print axioms no_weight_four_of_intersections
#print axioms eight_divisible_of_short_projective
end
end Binary97
