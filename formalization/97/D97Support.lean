import Auxiliary
import AuxSmall

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Initial support obtained from the SO residual bound and Lemma 3. -/
theorem d97_support_initial (D : Code ι) (hlen : Fintype.card ι = 97)
    (hk : Module.finrank F₂ D = 7) (hD : DoublyEven D) (hd : MinWeight D 48)
    (hfull : FullLength D) (x : D) (hx : x ≠ 0) :
    weight x.val = 48 ∨ weight x.val = 52 ∨ weight x.val = 56 ∨
      weight x.val = 64 ∨ weight x.val = 68 ∨ weight x.val = 72 ∨ weight x.val = 80 := by
  have hC := doublyEven_selfOrthogonal hD
  have hmax : weight x.val ≤ 97 := (weight_le_length x.val).trans_eq hlen
  have hmin := hd x.val x.property (fun h => hx (Subtype.ext h))
  have he := hD x.val x.property
  have hn96 : weight x.val ≠ 96 := by
    intro heq
    have hh := full_so_weight_ne_sub_one hC hfull x
    rw [hlen,heq] at hh
    omega
  have hbound : weight x.val < 96 →
      griesmer 6 (2*((48-weight x.val/2+1)/2))+weight x.val ≤ 97 := by
    intro hh
    exact (so_residual_bound hC hk hd x hx hh).trans_eq hlen
  have htab : ∀ w : Fin 98, 48 ≤ w.val → w.val % 4 = 0 → w.val ≠ 96 →
      (w.val < 96 → griesmer 6 (2*((48-w.val/2+1)/2))+w.val ≤ 97) →
      w.val = 48 ∨ w.val = 52 ∨ w.val = 56 ∨ w.val = 64 ∨
        w.val = 68 ∨ w.val = 72 ∨ w.val = 80 := by decide
  exact htab ⟨weight x.val,by omega⟩ hmin he hn96 hbound

/-- Weight 56 would give the excluded [41,6,20] residual. -/
theorem d97_weight_ne_56 (hWard : WardAssumption) (D : Code ι)
    (hlen : Fintype.card ι = 97) (hk : Module.finrank F₂ D = 7)
    (hd : MinWeight D 48) (c : D) : weight c.val ≠ 56 := by
  intro hc
  have hn : c ≠ 0 := by intro h; subst c; simp at hc
  have hkR := residual_finrank hd hk c hn (by omega)
  have hlR : Fintype.card (Outside c.val) = 41 := by
    have h := outside_card_add_weight c.val
    rw [hlen,hc] at h
    omega
  have hmR : MinWeight (LinearMap.range (residualMap D c)) 20 := by
    intro y hy hny
    have h := residual_minWeight hd c y hy hny
    change 96 ≤ weight c.val + 2*weight y at h
    omega
  exact no_linear_41_6_20 hWard _ hlR hkR hmR

/-- Weight 72 would give the excluded [25,6,12] residual. -/
theorem d97_weight_ne_72 (hWard : WardAssumption) (D : Code ι)
    (hlen : Fintype.card ι = 97) (hk : Module.finrank F₂ D = 7)
    (hd : MinWeight D 48) (c : D) : weight c.val ≠ 72 := by
  intro hc
  have hn : c ≠ 0 := by intro h; subst c; simp at hc
  have hkR := residual_finrank hd hk c hn (by omega)
  have hlR : Fintype.card (Outside c.val) = 25 := by
    have h := outside_card_add_weight c.val
    rw [hlen,hc] at h
    omega
  have hmR : MinWeight (LinearMap.range (residualMap D c)) 12 := by
    intro y hy hny
    have h := residual_minWeight hd c y hy hny
    change 96 ≤ weight c.val + 2*weight y at h
    omega
  exact no_linear_25_6_12 hWard _ hlR hkR hmR

/-- Weight 80 would give the excluded [17,6,8] residual. -/
theorem d97_weight_ne_80 (hWard : WardAssumption) (D : Code ι)
    (hlen : Fintype.card ι = 97) (hk : Module.finrank F₂ D = 7)
    (hd : MinWeight D 48) (c : D) : weight c.val ≠ 80 := by
  intro hc
  have hn : c ≠ 0 := by intro h; subst c; simp at hc
  have hkR := residual_finrank hd hk c hn (by omega)
  have hlR : Fintype.card (Outside c.val) = 17 := by
    have h := outside_card_add_weight c.val
    rw [hlen,hc] at h
    omega
  have hmR : MinWeight (LinearMap.range (residualMap D c)) 8 := by
    intro y hy hny
    have h := residual_minWeight hd c y hy hny
    change 96 ≤ weight c.val + 2*weight y at h
    omega
  exact no_linear_17_6_8 hWard _ hlR hkR hmR

theorem d97_support_before68 (hWard : WardAssumption) (D : Code ι)
    (hlen : Fintype.card ι = 97) (hk : Module.finrank F₂ D = 7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D)
    (x : D) (hx : x ≠ 0) :
    weight x.val = 48 ∨ weight x.val = 52 ∨ weight x.val = 64 ∨ weight x.val = 68 := by
  have h := d97_support_initial D hlen hk hD hd hfull x hx
  have h56 := d97_weight_ne_56 hWard D hlen hk hd x
  have h72 := d97_weight_ne_72 hWard D hlen hk hd x
  have h80 := d97_weight_ne_80 hWard D hlen hk hd x
  omega

#print axioms d97_support_before68
end
end Binary97
