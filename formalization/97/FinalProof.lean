import Puncture
import Reduction

namespace Binary97
noncomputable section
open Classical

/-- All branches of proof.md, with Ward retained as an explicit parameter. -/
theorem no_so_97 (hWard : WardAssumption) :
    ¬ ∃ C : Code (Fin 97),Module.finrank F₂ C=8 ∧ SelfOrthogonal C ∧ MinWeight C 46 := by
  rintro ⟨C,hk,hC,hd⟩
  obtain ⟨c,hc⟩ := exists_weight46 hk hC hd
  have hp := kernel_parameters hk hC hd
  let D := doublyEvenKernel C hC
  apply no_doubly_even_coset_97 hWard D hp.1 (doublyEvenKernel_doublyEven hC) hp.2 c.val
  intro x hx
  have hxC := doublyEvenKernel_le hC hx
  have hx4 := doublyEvenKernel_doublyEven hC x hx
  have hi := even_inter hC c.property hxC
  have hw := weight_identity (support c.val) (support x)
  rw [← support_add] at hw
  change weight (c.val+x)+2*(support c.val∩support x).card=weight c.val+weight x at hw
  rw [hc] at hw
  have hm : weight (c.val+x)%4=2 := by omega
  refine ⟨hd (c.val+x) (C.add_mem c.property hxC) ?_,hm⟩
  intro hz
  rw [hz,weight_zero] at hm
  contradiction

end
end Binary97
#print axioms Binary97.no_so_97
