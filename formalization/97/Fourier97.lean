import Foundation

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators

/-- Four characters of the quotient F₂², in a fixed coordinate order. -/
def quartet (a b c : ℤ) : Fin 4 → ℤ :=
  ![a+b+c,a-b-c,-a+b-c,-a-b+c]

def QuartetCondition (H a b c : ℤ) : Prop :=
  ∀ i : Fin 4, quartet a b c i ≤ H ∧ quartet a b c i % 8=H%8

theorem quartet_four (a b c : ℤ) (h : QuartetCondition 4 a b c) :
    (a = -4 ∨ a=0 ∨ a=4) ∧ (b = -4 ∨ b=0 ∨ b=4) ∧
    (c = -4 ∨ c=0 ∨ c=4) := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp [quartet] at h0 h1 h2 h3
  omega

theorem quartet_six (a b c : ℤ) (h : QuartetCondition 6 a b c) :
    (a = -6 ∨ a = -2 ∨ a=2 ∨ a=6) ∧
    (b = -6 ∨ b = -2 ∨ b=2 ∨ b=6) ∧
    (c = -6 ∨ c = -2 ∨ c=2 ∨ c=6) := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp [quartet] at h0 h1 h2 h3
  omega

/-- Dot-product characters on the m-dimensional binary vector space. -/
def binaryForm {m : ℕ} (x : Fin m → F₂) : (Fin m → F₂) →ₗ[F₂] F₂ where
  toFun v := ∑ i,x i*v i
  map_add' _ _ := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum,mul_left_comm]

theorem binaryForm_injective (m : ℕ) : Function.Injective (@binaryForm m) := by
  intro x y h
  funext i
  have he := LinearMap.congr_fun h (Pi.single i 1)
  simpa [binaryForm,Pi.single_apply] using he

def walsh {m : ℕ} (s : (Fin m → F₂) → ℤ) (v : Fin m → F₂) : ℤ :=
  weightedFourier binaryForm s v

theorem walsh_parseval {m : ℕ} (s : (Fin m → F₂) → ℤ) :
    ∑ v, walsh s v ^ 2 = (2^m : ℤ)*∑ x,s x^2 := by
  have h := weighted_parseval_injective binaryForm (binaryForm_injective m) s
  simpa [walsh,F₂,ZMod.card] using h

theorem word_add_self {m : ℕ} (x : Fin m → F₂) : x+x=0 := by
  funext i
  exact (by decide : ∀ a : F₂,a+a=0) (x i)

theorem binaryForm_add {m : ℕ} (x y v : Fin m → F₂) :
    binaryForm (x+y) v = binaryForm x v+binaryForm y v := by
  simp [binaryForm,add_mul,Finset.sum_add_distrib]

theorem sign_square (a : F₂) : sign a * sign a=1 := by
  have h : ∀ a : F₂,sign a*sign a=1 := by decide
  exact h a

def autocorrelation {m : ℕ} (s : (Fin m → F₂) → ℤ) (h : Fin m → F₂) : ℤ :=
  ∑ x,s x*s (x+h)

/-- Squaring a Walsh transform is the Walsh transform of the autocorrelation. -/
theorem walsh_autocorrelation {m : ℕ} (s : (Fin m → F₂) → ℤ) (v : Fin m → F₂) :
    walsh s v ^ 2 = walsh (autocorrelation s) v := by
  unfold walsh weightedFourier autocorrelation
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun h x => s x*s (x+h)*sign (binaryForm h v))]
  apply Finset.sum_congr rfl
  intro x _
  apply Eq.symm
  apply Fintype.sum_equiv (Equiv.addLeft x)
  intro h
  change s x*s (x+h)*sign (binaryForm h v) =
    s (x+h)*sign (binaryForm (x+h) v)*(s x*sign (binaryForm x v))
  rw [binaryForm_add,sign_add]
  have hs := sign_square (binaryForm x v)
  calc
    _ = s x*s (x+h)*sign (binaryForm h v)*1 := by ring
    _ = s x*s (x+h)*sign (binaryForm h v)*
        (sign (binaryForm x v)*sign (binaryForm x v)) := by rw [hs]
    _ = _ := by ring

/-- The fourth-moment identity used in proof.md section 7. -/
theorem walsh_fourth_moment {m : ℕ} (s : (Fin m → F₂) → ℤ) :
    ∑ v,walsh s v^4 = (2^m : ℤ)*∑ h,autocorrelation s h^2 := by
  have hp := walsh_parseval (autocorrelation s)
  have he (v : Fin m → F₂) : walsh s v^4=walsh (autocorrelation s) v^2 := by
    rw [show (4 : ℕ)=2*2 from rfl,pow_mul,walsh_autocorrelation]
  simpa only [he] using hp

/-- The numerical fourth-moment upper value, from the exact four possible coefficients. -/
theorem fourth_value_32 {α : Type*} [Fintype α] (T : α → ℤ)
    (hc : Fintype.card α=32)
    (hval : ∀ x,T x = -6 ∨ T x = -2 ∨ T x=2 ∨ T x=6)
    (hsecond : ∑ x,T x^2=1024) : ∑ x,T x^4=36352 := by
  have he (x : α) : T x^4=40*T x^2-144 := by
    rcases hval x with h | h | h | h <;> rw [h] <;> norm_num
  simp_rw [he]
  simp [Finset.sum_sub_distrib,← Finset.mul_sum,hsecond,hc]

/-- The final energy discrepancy in section 8, for fifteen ordinary pairs. -/
theorem pair_energy_obstruction (P Q : Fin 16 → ℤ)
    (hP : ∑ t,P t^2 ≤ 16) (hQ : ∑ t,Q t^2 ≤ 36)
    (hpair : ∀ t : Fin 16,t ≠ 0 → P t^2+Q t^2=4) : False := by
  have hpoint (t : Fin 16) : (if t=0 then (0 : ℤ) else 4) ≤ P t^2+Q t^2 := by
    by_cases ht : t=0
    · simp only [ht,if_true]
      positivity
    · rw [if_neg ht,hpair t ht]
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin 16))) => hpoint t)
  have hleft : (∑ t : Fin 16,if t=0 then (0 : ℤ) else 4)=60 := by decide
  rw [hleft,Finset.sum_add_distrib] at hs
  omega

#print axioms quartet_four
#print axioms quartet_six
#print axioms walsh_fourth_moment
#print axioms pair_energy_obstruction
end
end Binary97
