import Min48
import Geometry

namespace Binary97
noncomputable section
open Classical

theorem exists_weight46 {C : Code (Fin 97)}
    (hk : Module.finrank F₂ C = 8) (hC : SelfOrthogonal C) (hd : MinWeight C 46) :
    ∃ x : C, weight x.val = 46 := by
  by_contra! hh
  apply no_so_97_8_48
  refine ⟨C,hk,hC,?_⟩
  intro x hx hn
  have h1 := hd x hx hn
  have h2 := even_weight hC hx
  have h3 := hh ⟨x,hx⟩
  change weight x ≠ 46 at h3
  omega

/-- Sections 2 and 3: the doubly-even kernel has exactly dimension seven. -/
theorem kernel_parameters {C : Code (Fin 97)}
    (hk : Module.finrank F₂ C = 8) (hC : SelfOrthogonal C) (hd : MinWeight C 46) :
    Module.finrank F₂ (doublyEvenKernel C hC) = 7 ∧
    MinWeight (doublyEvenKernel C hC) 48 := by
  obtain ⟨x,hx⟩ := exists_weight46 hk hC hd
  have hq : q C hC ≠ 0 := by
    intro hz
    have he : q C hC x = 0 := by rw [hz]; rfl
    have hdiv := (q_eq_zero_iff hC x).mp he
    rw [hx] at hdiv
    contradiction
  refine ⟨doublyEvenKernel_finrank hC hk hq,?_⟩
  intro y hy hn
  have hm := hd y (doublyEvenKernel_le hC hy) hn
  have hv := doublyEvenKernel_doublyEven hC y hy
  omega

/-- The three effective-length branches are exhaustive. -/
theorem effective_length_cases {C : Code (Fin 97)}
    (hk : Module.finrank F₂ C = 8) (hC : SelfOrthogonal C) (hd : MinWeight C 46) :
    let N := (activeCoordinates C).card
    let L := (activeCoordinates (doublyEvenKernel C hC)).card
    (N = 96 ∧ L = 96) ∨ (N = 97 ∧ L = 96) ∨ (N = 97 ∧ L = 97) := by
  obtain ⟨hkD,hmD⟩ := kernel_parameters hk hC hd
  have hlo := effective_griesmer hkD hmD (by decide)
  have hg : griesmer 7 48 = 96 := by decide
  rw [hg] at hlo
  have hle := Finset.card_le_card (active_mono (doublyEvenKernel_le hC))
  have hhi : (activeCoordinates C).card ≤ 97 := by
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  dsimp only
  omega

#print axioms kernel_parameters
#print axioms effective_length_cases
end
end Binary97
