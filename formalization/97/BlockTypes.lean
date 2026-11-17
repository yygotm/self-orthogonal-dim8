import Fourier97

namespace Binary97
open scoped BigOperators
abbrev NonzeroTwo := {b : Word (Fin 2) // b≠0}

def nonzeroTwoAt : Fin 3 → NonzeroTwo :=
  ![⟨![1,0],by decide⟩,⟨![0,1],by decide⟩,⟨![1,1],by decide⟩]

def nonzeroTwoEquiv : Fin 3 ≃ NonzeroTwo where
  toFun := nonzeroTwoAt
  invFun b := if b.val=![1,0] then 0 else if b.val=![0,1] then 1 else 2
  left_inv := by decide
  right_inv := by decide

def twoCharacter : Fin 4 → Word (Fin 2) :=
  ![![0,0],![0,1],![1,0],![1,1]]

def quotientSum (T : NonzeroTwo → ℤ) (β : Word (Fin 2)) : ℤ :=
  ∑ b,T b*sign (binaryForm b.val β)

theorem quotientSum_quartet (T : NonzeroTwo → ℤ) (i : Fin 4) :
    quotientSum T (twoCharacter i)=quartet (T (nonzeroTwoAt 0)) (T (nonzeroTwoAt 1)) (T (nonzeroTwoAt 2)) i := by
  have hs := Fintype.sum_equiv nonzeroTwoEquiv
    (fun j => T (nonzeroTwoAt j)*sign (binaryForm (nonzeroTwoAt j).val (twoCharacter i)))
    (fun b => T b*sign (binaryForm b.val (twoCharacter i))) (fun j => rfl)
  unfold quotientSum
  rw [← hs]
  have htable : ∀ i : Fin 4,∀ j : Fin 3,
      sign (binaryForm (nonzeroTwoAt j).val (twoCharacter i))=
        (![![1,1,1],![1,-1,-1],![-1,1,-1],![-1,-1,1]] : Fin 4 → Fin 3 → ℤ) i j := by decide
  simp_rw [htable]
  fin_cases i <;> norm_num [Fin.sum_univ_succ,quartet] <;> ring

theorem quotient_four (T : NonzeroTwo → ℤ)
    (h : ∀ β,quotientSum T β≤4 ∧ quotientSum T β%8=4) :
    ∀ b,T b = -4 ∨ T b=0 ∨ T b=4 := by
  have hq : QuartetCondition 4 (T (nonzeroTwoAt 0)) (T (nonzeroTwoAt 1)) (T (nonzeroTwoAt 2)) := by
    intro i
    simpa only [← quotientSum_quartet,show (4 : ℤ)%8=4 by decide] using h (twoCharacter i)
  have ht := quartet_four _ _ _ hq
  intro b
  obtain ⟨j,rfl⟩ := nonzeroTwoEquiv.surjective b
  fin_cases j
  · exact ht.1
  · exact ht.2.1
  · exact ht.2.2

theorem quotient_six (T : NonzeroTwo → ℤ)
    (h : ∀ β,quotientSum T β≤6 ∧ quotientSum T β%8=6) :
    ∀ b,T b = -6 ∨ T b = -2 ∨ T b=2 ∨ T b=6 := by
  have hq : QuartetCondition 6 (T (nonzeroTwoAt 0)) (T (nonzeroTwoAt 1)) (T (nonzeroTwoAt 2)) := by
    intro i
    simpa only [← quotientSum_quartet,show (6 : ℤ)%8=6 by decide] using h (twoCharacter i)
  have ht := quartet_six _ _ _ hq
  intro b
  obtain ⟨j,rfl⟩ := nonzeroTwoEquiv.surjective b
  fin_cases j
  · exact ht.1
  · exact ht.2.1
  · exact ht.2.2

#print axioms quotient_four
#print axioms quotient_six
end Binary97
