import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
Self-contained binary-code definitions and proofs.
Source adaptations: the author's unpublished So52 Lean development.
  Reductions.lean: weight_identity, half_weight_add.
  Kernel.lean: support/weight/dot, q and kernel membership.
  Residual.lean: restriction map, residual kernel/rank/distance.
Only Mathlib is imported; the original So52 files are not dependencies.
-/
noncomputable section
open scoped BigOperators symmDiff
abbrev F₂ := ZMod 2
abbrev Word (ι : Type*) := ι → F₂
abbrev Code (ι : Type*) := Submodule F₂ (Word ι)

section Sets
variable {α : Type*} [DecidableEq α]
theorem weight_identity (s t : Finset α) :
    (s ∆ t).card + 2 * (s ∩ t).card = s.card + t.card := by
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  have h₁ := Finset.card_sdiff_add_card_inter s t
  have h₂ := Finset.card_sdiff_add_card_inter t s
  rw [Finset.inter_comm t s] at h₂
  omega

/-- Section 3: half the weight modulo 2 is additive on self-orthogonal words. -/
theorem half_weight_add (s t : Finset α)
    (hs : s.card % 2 = 0) (ht : t.card % 2 = 0)
    (hst : (s ∩ t).card % 2 = 0) :
    ((s ∆ t).card / 2) % 2 = (s.card / 2 + t.card / 2) % 2 := by
  have hw := weight_identity s t
  omega


end Sets
section Binary
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def support  (x : Word ι) : Finset (ι) :=
  Finset.univ.filter fun i => x i ≠ 0

def weight  (x : Word ι) : ℕ := (support x).card

def dot  (x y : Word ι) : F₂ := ∑ i, x i * y i

def SelfOrthogonal  (C : Code ι) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, dot x y = 0

def DoublyEven  (C : Code ι) : Prop :=
  ∀ x ∈ C, weight x % 4 = 0

def MinWeight  (C : Code ι) (d : ℕ) : Prop :=
  ∀ x ∈ C, x ≠ 0 → d ≤ weight x

open scoped symmDiff

theorem support_add  (x y : Word ι) :
    support (x + y) = support x ∆ support y := by
  ext i
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_symmDiff, Pi.add_apply]
  have h : ∀ a b : F₂, a + b ≠ 0 ↔ (a ≠ 0 ∧ ¬b ≠ 0) ∨ (b ≠ 0 ∧ ¬a ≠ 0) := by
    decide
  exact h (x i) (y i)

@[simp] theorem weight_zero : weight (0 : Word ι) = 0 := by
  simp [weight, support]

theorem dot_eq_card_inter  (x y : Word ι) :
    dot x y = ((support x ∩ support y).card : F₂) := by
  have h : ∀ a b : F₂, a * b = if a ≠ 0 ∧ b ≠ 0 then 1 else 0 := by decide
  simp only [dot, h]
  simp [support, Finset.filter_inter, Finset.filter_filter, Finset.sum_boole, and_comm]

theorem even_inter  {C : Code ι} (hC : SelfOrthogonal C)
    {x y : Word ι} (hx : x ∈ C) (hy : y ∈ C) :
    (support x ∩ support y).card % 2 = 0 := by
  have h := hC x hx y hy
  rw [dot_eq_card_inter] at h
  have hv := congrArg ZMod.val h
  simpa [ZMod.val_natCast] using hv

theorem even_weight  {C : Code ι} (hC : SelfOrthogonal C)
    {x : Word ι} (hx : x ∈ C) : weight x % 2 = 0 := by
  simpa [weight] using even_inter hC hx hx

theorem doublyEven_selfOrthogonal  {C : Code ι} (hD : DoublyEven C) :
    SelfOrthogonal C := by
  intro x hx y hy
  have hx4 := hD x hx
  have hy4 := hD y hy
  have hxy4 := hD (x + y) (C.add_mem hx hy)
  have hw := weight_identity (support x) (support y)
  rw [← support_add] at hw
  change weight (x + y) + 2 * (support x ∩ support y).card = weight x + weight y at hw
  rw [dot_eq_card_inter, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  omega

/-- Half-weight modulo two, as a linear functional on a self-orthogonal code. -/
def q  (C : Code ι) (hC : SelfOrthogonal C) : C →ₗ[F₂] F₂ where
  toFun x := (weight x.val / 2 : ℕ)
  map_add' x y := by
    change ((weight (x.val + y.val) / 2 : ℕ) : F₂) =
      (weight x.val / 2 : ℕ) + (weight y.val / 2 : ℕ)
    rw [← Nat.cast_add]
    apply ZMod.val_injective
    simp only [ZMod.val_natCast]
    simpa only [weight, support_add] using
      half_weight_add (support x.val) (support y.val)
        (even_weight hC x.property) (even_weight hC y.property)
        (even_inter hC x.property y.property)
  map_smul' a x := by
    have ha : a = 0 ∨ a = 1 := by
      have h : ∀ a : F₂, a = 0 ∨ a = 1 := by decide
      exact h a
    rcases ha with rfl | rfl <;> simp

theorem q_eq_zero_iff  {C : Code ι} (hC : SelfOrthogonal C) (x : C) :
    q C hC x = 0 ↔ weight x.val % 4 = 0 := by
  change ((weight x.val / 2 : ℕ) : F₂) = 0 ↔ _
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  have he := even_weight hC x.property
  omega

theorem q_eq_one_iff  {C : Code ι} (hC : SelfOrthogonal C) (x : C) :
    q C hC x = 1 ↔ weight x.val % 4 = 2 := by
  have he := even_weight hC x.property
  change ((weight x.val / 2 : ℕ) : F₂) = 1 ↔ _
  constructor
  · intro h
    have hv : (weight x.val / 2) % 2 = 1 := by
      simpa only [ZMod.val_natCast, ZMod.val_one] using congrArg ZMod.val h
    omega
  · intro h
    apply ZMod.val_injective
    simp only [ZMod.val_natCast, ZMod.val_one]
    omega

theorem q_zero_iff_doublyEven  {C : Code ι} (hC : SelfOrthogonal C) :
    q C hC = 0 ↔ DoublyEven C := by
  constructor
  · intro hz x hx
    apply (q_eq_zero_iff hC ⟨x, hx⟩).mp
    rw [hz]; rfl
  · intro hd
    apply LinearMap.ext
    intro x
    exact (q_eq_zero_iff hC x).mpr (hd x.val x.property)

/-- The kernel embedded back into the original ambient coordinate space. -/
def doublyEvenKernel  (C : Code ι) (hC : SelfOrthogonal C) : Code ι :=
  (LinearMap.ker (q C hC)).map C.subtype

theorem mem_doublyEvenKernel  {C : Code ι} (hC : SelfOrthogonal C)
    (x : Word ι) : x ∈ doublyEvenKernel C hC ↔ x ∈ C ∧ weight x % 4 = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, (q_eq_zero_iff hC y).mp hy⟩
  · rintro ⟨hx, hw⟩
    exact ⟨⟨x, hx⟩, (q_eq_zero_iff hC ⟨x, hx⟩).mpr hw, rfl⟩

theorem doublyEvenKernel_le  {C : Code ι} (hC : SelfOrthogonal C) :
    doublyEvenKernel C hC ≤ C := fun x hx => ((mem_doublyEvenKernel hC x).mp hx).1

theorem doublyEvenKernel_doublyEven  {C : Code ι} (hC : SelfOrthogonal C) :
    DoublyEven (doublyEvenKernel C hC) :=
  fun x hx => ((mem_doublyEvenKernel hC x).mp hx).2

theorem doublyEvenKernel_selfOrthogonal  {C : Code ι} (hC : SelfOrthogonal C) :
    SelfOrthogonal (doublyEvenKernel C hC) :=
  fun x hx y hy => hC x (doublyEvenKernel_le hC hx) y (doublyEvenKernel_le hC hy)


/-- Least multiple of four at least t. -/
def c4 (t : ℕ) : ℕ := 4 * ((t + 3) / 4)

/-- Generalization of So52/Kernel.lean: keep both possible kernel dimensions. -/
theorem doubly_even_subcode {k t : ℕ} (C : Code ι)
    (hC : SelfOrthogonal C) (hdim : Module.finrank F₂ C = k + 1)
    (hmin : MinWeight C t) :
    ∃ D : Code ι, D ≤ C ∧ k ≤ Module.finrank F₂ D ∧
      (∀ x ∈ D, weight x % 4 = 0) ∧ MinWeight D (c4 t) := by
  let D := doublyEvenKernel C hC
  have hr := (q C hC).finrank_range_add_finrank_ker
  have hle : Module.finrank F₂ (LinearMap.range (q C hC)) ≤ 1 := by
    simpa using (LinearMap.range (q C hC)).finrank_le
  have hd : k ≤ Module.finrank F₂ D := by
    change k ≤ Module.finrank F₂ ((LinearMap.ker (q C hC)).map C.subtype)
    rw [Submodule.finrank_map_subtype_eq]
    omega
  refine ⟨D, doublyEvenKernel_le hC, hd, doublyEvenKernel_doublyEven hC, ?_⟩
  intro x hx hn
  have hm := hmin x (doublyEvenKernel_le hC hx) hn
  have hw := doublyEvenKernel_doublyEven hC x hx
  unfold c4
  omega
abbrev Outside  (c : Word ι) := {i : ι // c i = 0}

theorem outside_card_add_weight (c : Word ι) :
    Fintype.card (Outside c) + weight c = Fintype.card ι := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : ι => c i = 0)
  rw [Fintype.card_subtype]
  simpa [weight, support] using h

def residualMap  (C : Code ι) (c : C) : C →ₗ[F₂] (Outside c.val → F₂) where
  toFun x i := x.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def residualWeight  {c : Word ι} (y : Outside c → F₂) : ℕ :=
  (Finset.univ.filter fun i => y i ≠ 0).card

theorem residualWeight_eq_sdiff  {C : Code ι} (c x : C) :
    residualWeight (residualMap C c x) = (support x.val \ support c.val).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    have hi' : x.val i.val ≠ 0 := (Finset.mem_filter.mp hi).2
    simpa [support] using And.intro hi' i.property
  · intro i hi j hj hij
    exact Subtype.ext hij
  · intro i hi
    have hi' : x.val i ≠ 0 ∧ c.val i = 0 := by simpa [support] using hi
    exact ⟨⟨i, hi'.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'.1⟩, rfl⟩

theorem add_eq_zero_iff  (x y : Word ι) : x + y = 0 ↔ x = y := by
  have h : ∀ a b : F₂, a + b = 0 ↔ a = b := by decide
  constructor
  · intro he
    funext i
    exact (h _ _).mp (congrFun he i)
  · rintro rfl
    funext i
    exact (h _ _).mpr rfl

theorem residual_weight_identity  {C : Code ι} (c x : C) :
    weight x.val + weight (x.val + c.val) =
      weight c.val + 2 * residualWeight (residualMap C c x) := by
  rw [residualWeight_eq_sdiff]
  have h₁ := weight_identity (support x.val) (support c.val)
  have h₂ := Finset.card_sdiff_add_card_inter (support x.val) (support c.val)
  simp only [weight, support_add]
  omega

theorem mem_residual_ker_iff  {C : Code ι} (c x : C) :
    x ∈ LinearMap.ker (residualMap C c) ↔ support x.val ⊆ support c.val := by
  constructor
  · intro hx i hi
    by_contra hc
    have hc0 : c.val i = 0 := by simpa [support] using hc
    have hx0 := congrFun hx (⟨i, hc0⟩ : Outside c.val)
    have hxne : x.val i ≠ 0 := by simpa [support] using hi
    exact hxne hx0
  · intro hs
    change residualMap C c x = 0
    funext i
    by_contra hx
    change x.val i.val ≠ 0 at hx
    have hi : i.val ∈ support c.val := hs (by simpa [support] using hx)
    simp [support, i.property] at hi

/-- Below twice the minimum weight, the only words supported on c are 0,c. -/
theorem residual_ker_words {d : ℕ} {C : Code ι} (hmin : MinWeight C d)
    (c : C) (hc : weight c.val < 2 * d) (x : C)
    (hx : x ∈ LinearMap.ker (residualMap C c)) : x = 0 ∨ x = c := by
  by_cases h0 : x = 0
  · exact Or.inl h0
  right
  by_contra hxc
  have hx0 : x.val ≠ 0 := fun h => h0 (Subtype.ext h)
  have hxc0 : x.val + c.val ≠ 0 := by
    intro h
    exact hxc (Subtype.ext ((add_eq_zero_iff _ _).mp h))
  have h₁ := hmin x.val x.property hx0
  have h₂ := hmin (x.val + c.val) (C.add_mem x.property c.property) hxc0
  have hs := (mem_residual_ker_iff c x).mp hx
  have hw := weight_identity (support x.val) (support c.val)
  rw [Finset.inter_eq_left.mpr hs, ← support_add] at hw
  change weight (x.val + c.val) + 2 * weight x.val = weight x.val + weight c.val at hw
  omega

theorem residual_ker_eq_span {d : ℕ} {C : Code ι} (hmin : MinWeight C d)
    (c : C) (hc : weight c.val < 2 * d) :
    LinearMap.ker (residualMap C c) = Submodule.span F₂ {c} := by
  apply le_antisymm
  · intro x hx
    rcases residual_ker_words hmin c hc x hx with h0 | he
    · rw [h0]; exact Submodule.zero_mem _
    · rw [he]; exact Submodule.subset_span (Set.mem_singleton c)
  · apply Submodule.span_le.mpr
    intro x hx
    have he : x = c := Set.mem_singleton_iff.mp hx
    subst x
    exact (mem_residual_ker_iff c c).mpr (Finset.Subset.refl _)

theorem residual_finrank {d k : ℕ} {C : Code ι} (hmin : MinWeight C d)
    (hdim : Module.finrank F₂ C = k + 1) (c : C)
    (hc0 : c ≠ 0) (hc : weight c.val < 2 * d) :
    Module.finrank F₂ (LinearMap.range (residualMap C c)) = k := by
  have hr := (residualMap C c).finrank_range_add_finrank_ker
  rw [residual_ker_eq_span hmin c hc, finrank_span_singleton hc0, hdim] at hr
  omega

/-- Every nonzero residual word satisfies the usual residual distance inequality. -/
theorem residual_minWeight {d : ℕ} {C : Code ι} (hmin : MinWeight C d)
    (c : C) (y : Outside c.val → F₂)
    (hy : y ∈ LinearMap.range (residualMap C c)) (hy0 : y ≠ 0) :
    2 * d ≤ weight c.val + 2 * residualWeight y := by
  obtain ⟨x, rfl⟩ := hy
  have hx0 : x.val ≠ 0 := by
    intro hx
    apply hy0
    funext i
    exact congrFun hx i.val
  have hxc0 : x.val + c.val ≠ 0 := by
    intro hx
    have he := (add_eq_zero_iff _ _).mp hx
    apply hy0
    funext i
    exact (congrFun he i.val).trans i.property
  have h₁ := hmin x.val x.property hx0
  have h₂ := hmin (x.val + c.val) (C.add_mem x.property c.property) hxc0
  have hw := residual_weight_identity c x
  omega



/-- The ordinary binary Griesmer sum, using Mathlib's natural ceiling division. -/
def griesmer (k d : ℕ) : ℕ := ∑ i ∈ Finset.range k, d ⌈/⌉ (2 ^ i)

theorem ceilDiv_nested (d a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    d ⌈/⌉ (a * b) = (d ⌈/⌉ a) ⌈/⌉ b := by
  apply eq_of_forall_ge_iff
  intro c
  rw [ceilDiv_le_iff_le_mul (mul_pos ha hb),
    ceilDiv_le_iff_le_mul hb, ceilDiv_le_iff_le_mul ha]
  simp only [Nat.mul_assoc]

theorem griesmer_mono_distance (k : ℕ) {d e : ℕ} (h : d ≤ e) :
    griesmer k d ≤ griesmer k e := by
  apply Finset.sum_le_sum
  intro i hi
  apply (ceilDiv_le_iff_le_mul (by positivity : 0 < 2 ^ i)).mpr
  exact h.trans ((ceilDiv_le_iff_le_mul (by positivity : 0 < 2 ^ i)).mp le_rfl)

theorem griesmer_mono_dimension {k l d : ℕ} (h : k ≤ l) :
    griesmer k d ≤ griesmer l d := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro i hi hnot
  exact Nat.zero_le _

theorem griesmer_succ (k d : ℕ) :
    griesmer (k + 1) d = d + griesmer k (d ⌈/⌉ 2) := by
  unfold griesmer
  rw [Finset.sum_range_succ']
  simp only [pow_zero, ceilDiv_one]
  rw [Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_succ, Nat.mul_comm (2 ^ i) 2, ceilDiv_nested d 2 (2 ^ i) (by decide)
    (by positivity)]

/-- General binary Griesmer bound. No orthogonality hypothesis.
The proof chooses an actual minimum-weight word and applies the residual induction. -/
theorem griesmer_bound (k d : ℕ) (C : Code ι)
    (hdim : Module.finrank F₂ C = k) (hd : 1 ≤ d) (hmin : MinWeight C d) :
    griesmer k d ≤ Fintype.card ι := by
  classical
  induction k generalizing ι d with
  | zero => simp [griesmer]
  | succ k ih =>
    have hp : 0 < Module.finrank F₂ C := by omega
    obtain ⟨c0, hc0⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := F₂) (M := C)).mp hp
    have hex : ∃ w : ℕ, ∃ c : C, c ≠ 0 ∧ weight c.val = w :=
      ⟨weight c0.val, c0, hc0, rfl⟩
    let δ := Nat.find hex
    obtain ⟨c, hc, hcw⟩ := Nat.find_spec hex
    have hcval : c.val ≠ 0 := by
      intro hz
      exact hc (Subtype.ext hz)
    have hδ : d ≤ δ := by
      have hh := hmin c.val c.property hcval
      change weight c.val = δ at hcw
      omega
    have hδpos : 0 < δ := by omega
    have hmδ : MinWeight C δ := by
      intro x hx hn
      apply Nat.find_min' hex
      exact ⟨⟨x,hx⟩, (fun hz => hn (congrArg Subtype.val hz)), rfl⟩
    have hcr : weight c.val < 2 * δ := by
      change weight c.val = δ at hcw
      omega
    let R := LinearMap.range (residualMap C c)
    have hrdim : Module.finrank F₂ R = k :=
      residual_finrank hmδ hdim c hc hcr
    have hrmin : MinWeight R (δ ⌈/⌉ 2) := by
      intro y hy hn
      have hh := residual_minWeight hmδ c y hy hn
      change weight c.val = δ at hcw
      change δ ⌈/⌉ 2 ≤ residualWeight y
      rw [ceilDiv_le_iff_le_mul (by decide : 0 < (2 : ℕ))]
      omega
    have hrdpos : 1 ≤ δ ⌈/⌉ 2 := by
      rw [Nat.ceilDiv_eq_add_pred_div]
      omega
    have hrbound := ih (δ ⌈/⌉ 2) R hrdim hrdpos hrmin
    have hn := outside_card_add_weight c.val
    have hm := griesmer_mono_distance (k + 1) hδ
    rw [griesmer_succ k δ] at hm
    change weight c.val = δ at hcw
    omega

/-- The six special cases use only the general kernel and Griesmer theorems. -/
theorem no_so_of_griesmer (n t : ℕ) (hpos : 1 ≤ c4 t)
    (hnum : n < griesmer 7 (c4 t)) :
    ¬ ∃ C : Submodule (ZMod 2) (Fin n → ZMod 2),
        Module.finrank (ZMod 2) C = 8 ∧
        (∀ x ∈ C, ∀ y ∈ C, ∑ i, x i * y i = 0) ∧
        (∀ x ∈ C, x ≠ 0 → t ≤ weight x) := by
  rintro ⟨C, hdim, hC, hmin⟩
  obtain ⟨D, hDC, hdD, hfour, hminD⟩ :=
    doubly_even_subcode (k := 7) C hC hdim hmin
  have hg := griesmer_bound (Module.finrank F₂ D) (c4 t) D rfl hpos hminD
  have hm := griesmer_mono_dimension (d := c4 t) hdD
  simp only [Fintype.card_fin] at hg
  omega


end Binary


theorem no_so_137_8_66 :
    ¬ ∃ C : Submodule (ZMod 2) (Fin 137 → ZMod 2),
        Module.finrank (ZMod 2) C = 8 ∧
        (∀ x ∈ C, ∀ y ∈ C, ∑ i, x i * y i = 0) ∧
        (∀ x ∈ C, x ≠ 0 → 66 ≤ weight x) := by
  exact no_so_of_griesmer 137 66 (by decide) (by decide)

theorem no_so_183_8_90 :
    ¬ ∃ C : Submodule (ZMod 2) (Fin 183 → ZMod 2),
        Module.finrank (ZMod 2) C = 8 ∧
        (∀ x ∈ C, ∀ y ∈ C, ∑ i, x i * y i = 0) ∧
        (∀ x ∈ C, x ≠ 0 → 90 ≤ weight x) := by
  exact no_so_of_griesmer 183 90 (by decide) (by decide)

theorem no_so_200_8_98 :
    ¬ ∃ C : Submodule (ZMod 2) (Fin 200 → ZMod 2),
        Module.finrank (ZMod 2) C = 8 ∧
        (∀ x ∈ C, ∀ y ∈ C, ∑ i, x i * y i = 0) ∧
        (∀ x ∈ C, x ≠ 0 → 98 ≤ weight x) := by
  exact no_so_of_griesmer 200 98 (by decide) (by decide)

theorem no_so_207_8_102 :
    ¬ ∃ C : Submodule (ZMod 2) (Fin 207 → ZMod 2),
        Module.finrank (ZMod 2) C = 8 ∧
        (∀ x ∈ C, ∀ y ∈ C, ∑ i, x i * y i = 0) ∧
        (∀ x ∈ C, x ≠ 0 → 102 ≤ weight x) := by
  exact no_so_of_griesmer 207 102 (by decide) (by decide)

theorem no_so_215_8_106 :
    ¬ ∃ C : Submodule (ZMod 2) (Fin 215 → ZMod 2),
        Module.finrank (ZMod 2) C = 8 ∧
        (∀ x ∈ C, ∀ y ∈ C, ∑ i, x i * y i = 0) ∧
        (∀ x ∈ C, x ≠ 0 → 106 ≤ weight x) := by
  exact no_so_of_griesmer 215 106 (by decide) (by decide)

theorem no_so_231_8_114 :
    ¬ ∃ C : Submodule (ZMod 2) (Fin 231 → ZMod 2),
        Module.finrank (ZMod 2) C = 8 ∧
        (∀ x ∈ C, ∀ y ∈ C, ∑ i, x i * y i = 0) ∧
        (∀ x ∈ C, x ≠ 0 → 114 ≤ weight x) := by
  exact no_so_of_griesmer 231 114 (by decide) (by decide)

/-- Numerical exclusions: all six entries from the brief are kernel-checked. -/
theorem numerical_exclusions :
    (c4 66 = 68 ∧ griesmer 7 68 = 138 ∧ 137 < griesmer 7 68) ∧
    (c4 90 = 92 ∧ griesmer 7 92 = 184 ∧ 183 < griesmer 7 92) ∧
    (c4 98 = 100 ∧ griesmer 7 100 = 201 ∧ 200 < griesmer 7 100) ∧
    (c4 102 = 104 ∧ griesmer 7 104 = 208 ∧ 207 < griesmer 7 104) ∧
    (c4 106 = 108 ∧ griesmer 7 108 = 216 ∧ 215 < griesmer 7 108) ∧
    (c4 114 = 116 ∧ griesmer 7 116 = 232 ∧ 231 < griesmer 7 116) := by
  decide

/-- The lower endpoints are not excluded by the same numerical test. -/
theorem negative_controls :
    (c4 64 = 64 ∧ griesmer 7 (c4 64) = 127 ∧ griesmer 7 (c4 64) ≤ 137) ∧
    (c4 88 = 88 ∧ griesmer 7 (c4 88) = 176 ∧ griesmer 7 (c4 88) ≤ 183) ∧
    (c4 96 = 96 ∧ griesmer 7 (c4 96) = 191 ∧ griesmer 7 (c4 96) ≤ 200) ∧
    (c4 100 = 100 ∧ griesmer 7 (c4 100) = 201 ∧ griesmer 7 (c4 100) ≤ 207) ∧
    (c4 104 = 104 ∧ griesmer 7 (c4 104) = 208 ∧ griesmer 7 (c4 104) ≤ 215) ∧
    (c4 112 = 112 ∧ griesmer 7 (c4 112) = 223 ∧ griesmer 7 (c4 112) ≤ 231) := by
  decide

/-- Binary [7,3,4] simplex map, listing the seven nonzero columns of F₂³. -/
def simplexMap : (Fin 3 → F₂) →ₗ[F₂] (Fin 7 → F₂) where
  toFun x := ![x 0, x 1, x 0 + x 1, x 2, x 0 + x 2,
    x 1 + x 2, x 0 + x 1 + x 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [Pi.add_apply] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, mul_add]

theorem simplexMap_injective : Function.Injective simplexMap := by
  intro x y h
  funext i
  fin_cases i
  · simpa [simplexMap] using congrFun h 0
  · simpa [simplexMap] using congrFun h 1
  · simpa [simplexMap] using congrFun h 3

theorem simplex_word_weight :
    ∀ x : Fin 3 → F₂, x ≠ 0 → weight (simplexMap x) = 4 := by
  decide

/-- A concrete SO equality case satisfying the actual Griesmer hypotheses. -/
theorem simplex_equality_control :
    Module.finrank F₂ (LinearMap.range simplexMap) = 3 ∧
    SelfOrthogonal (LinearMap.range simplexMap) ∧
    MinWeight (LinearMap.range simplexMap) 4 ∧ griesmer 3 4 = 7 := by
  have hr : Module.finrank F₂ (LinearMap.range simplexMap) = 3 := by
    rw [LinearMap.finrank_range_of_inj simplexMap_injective]
    simp
  have hm : MinWeight (LinearMap.range simplexMap) 4 := by
    rintro y ⟨x, rfl⟩ hn
    have hx : x ≠ 0 := by
      intro hz
      exact hn (by rw [hz, map_zero])
    exact (simplex_word_weight x hx).ge
  have hfour : DoublyEven (LinearMap.range simplexMap) := by
    rintro y ⟨x, rfl⟩
    by_cases hx : x = 0
    · simp [hx]
    · rw [simplex_word_weight x hx]
  exact ⟨hr, doublyEven_selfOrthogonal hfour, hm, by decide⟩

theorem simplex_griesmer_application :
    griesmer 3 4 ≤ Fintype.card (Fin 7) :=
  griesmer_bound 3 4 (LinearMap.range simplexMap) simplex_equality_control.1
    (by decide) simplex_equality_control.2.2.1

#print axioms doubly_even_subcode
#print axioms griesmer_bound
#print axioms no_so_137_8_66
#print axioms no_so_183_8_90
#print axioms no_so_200_8_98
#print axioms no_so_207_8_102
#print axioms no_so_215_8_106
#print axioms no_so_231_8_114
#print axioms numerical_exclusions
#print axioms negative_controls
#print axioms simplex_equality_control
#print axioms simplex_griesmer_application


