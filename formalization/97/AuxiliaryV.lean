import D97Moments
import Evaluation
import Divisibility

namespace Binary97
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual auxiliary evaluation weights, including the zero functional. -/
theorem d97_auxiliary_weights (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι=97) (hk : Module.finrank F₂ D=7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D) :
    (∀ g : D →ₗ[F₂] F₂,
      (weight (evaluationMap (weightWords D 52) g)+
        4*weight (evaluationMap (weightWords D 64) g))%8=0) ∧
    (∀ g : D →ₗ[F₂] F₂,g≠0 →
      8 ≤ weight (evaluationMap (weightWords D 52) g)+
        4*weight (evaluationMap (weightWords D 64) g)) := by
  constructor
  · intro g
    by_cases hg : g=0
    · subst g; simp
    · have h := d97_inverse_aux hWard D hlen hk hD hd hfull g hg
      rw [evaluation_weight,evaluation_weight]
      change (classWeight D 52 g+4*classWeight D 64 g)%8=0
      omega
  · intro g hg
    have h := d97_inverse_aux hWard D hlen hk hD hd hfull g hg
    rw [evaluation_weight,evaluation_weight]
    change 8 ≤ classWeight D 52 g+4*classWeight D 64 g
    omega

/-- All of V is eight-divisible, proved by the short projective coset-average lemma. -/
theorem d97_V_eight_divisible (hWard : WardAssumption) (D : Code ι) [Fintype D]
    (hlen : Fintype.card ι=97) (hk : Module.finrank F₂ D=7)
    (hD : DoublyEven D) (hd : MinWeight D 48) (hfull : FullLength D) :
    ∀ x ∈ evaluationCode (weightWords D 52),weight x%8=0 := by
  let S := weightWords D 52
  let T := weightWords D 64
  let E := evaluationCode S
  letI : Fintype E := Fintype.ofFinite E
  have haux := (d97_auxiliary_weights hWard D hlen hk hD hd hfull).1
  have hfour : DoublyEven E := by
    rintro x ⟨g,rfl⟩
    have h := haux g
    change weight (evaluationMap S g)%4=0
    change (weight (evaluationMap S g)+4*weight (evaluationMap T g))%8=0 at h
    omega
  have hinter : IntersectionFour E := by
    rintro x ⟨g,rfl⟩ y ⟨h,rfl⟩
    have h1 := haux g
    have h2 := haux h
    have h3 := haux (g+h)
    have hs := weight_identity (support (evaluationMap S g)) (support (evaluationMap S h))
    have ht := weight_identity (support (evaluationMap T g)) (support (evaluationMap T h))
    rw [← support_add] at hs ht
    change weight (evaluationMap S g+evaluationMap S h)+
      2*(support (evaluationMap S g) ∩ support (evaluationMap S h)).card =
      weight (evaluationMap S g)+weight (evaluationMap S h) at hs
    change weight (evaluationMap T g+evaluationMap T h)+
      2*(support (evaluationMap T g) ∩ support (evaluationMap T h)).card =
      weight (evaluationMap T g)+weight (evaluationMap T h) at ht
    rw [← map_add] at hs ht
    change (support (evaluationMap S g) ∩ support (evaluationMap S h)).card%4=0
    change (weight (evaluationMap S g)+4*weight (evaluationMap T g))%8=0 at h1
    change (weight (evaluationMap S h)+4*weight (evaluationMap T h))%8=0 at h2
    change (weight (evaluationMap S (g+h))+4*weight (evaluationMap T (g+h)))%8=0 at h3
    omega
  have hz : (0 : D) ∉ S := by simp [S,weightWords,weight_zero]
  have hproj := evaluation_projective S
  have hfullE := evaluation_full S hz
  have hlenE : Fintype.card S ≤ 20 := by
    simpa [S] using (d97_class_counts hWard D hlen hk hD hd hfull).2.2.2
  exact eight_divisible_of_short_projective E hfour hinter hfullE hproj hlenE

#print axioms d97_V_eight_divisible
end
end Binary97
