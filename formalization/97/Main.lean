import FinalProof

open scoped BigOperators

/-- The Hamming weight required in the public theorem statement. -/
def weight {n : ℕ} (x : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- Ward (1998), binary specialization of Kurz draft Theorem 1, printed p.3.
The draft's printed p.2 convention is minimum distance AT LEAST d.
Only positive dimension and positive distance are assumed; this is a parameter,
not a new logical primitive. -/
def WardBinary : Prop :=
  ∀ (n k d r : ℕ) (C : Submodule (ZMod 2) (Fin n → ZMod 2)),
    1 ≤ k → 1 ≤ d → Module.finrank (ZMod 2) C = k →
    n = ∑ i ∈ Finset.range k, d ⌈/⌉ (2 ^ i) →
    (∀ x ∈ C, x ≠ 0 → d ≤ weight x) →
    2 ^ r ∣ d → ∀ x ∈ C, 2 ^ r ∣ weight x

theorem ward_41 (hWard : WardBinary)
    (C : Submodule (ZMod 2) (Fin 41 → ZMod 2))
    (hk : Module.finrank (ZMod 2) C = 6)
    (hd : ∀ x ∈ C, x ≠ 0 → 20 ≤ weight x) :
    ∀ x ∈ C, 4 ∣ weight x := by
  exact hWard 41 6 20 2 C (by decide) (by decide) hk (by decide) hd (by decide)

theorem ward_25 (hWard : WardBinary)
    (C : Submodule (ZMod 2) (Fin 25 → ZMod 2))
    (hk : Module.finrank (ZMod 2) C = 6)
    (hd : ∀ x ∈ C, x ≠ 0 → 12 ≤ weight x) :
    ∀ x ∈ C, 4 ∣ weight x := by
  exact hWard 25 6 12 2 C (by decide) (by decide) hk (by decide) hd (by decide)

theorem ward_17 (hWard : WardBinary)
    (C : Submodule (ZMod 2) (Fin 17 → ZMod 2))
    (hk : Module.finrank (ZMod 2) C = 6)
    (hd : ∀ x ∈ C, x ≠ 0 → 8 ≤ weight x) :
    ∀ x ∈ C, 8 ∣ weight x := by
  exact hWard 17 6 8 3 C (by decide) (by decide) hk (by decide) hd (by decide)

/-- A real [7,3,4] code: SO, Ward equality hypotheses, and divisibility.
This does not assert consistency of all of WardBinary from a single instance. -/
theorem simplex_positive_control :
    ∃ C : Submodule (ZMod 2) (Fin 7 → ZMod 2),
      Module.finrank (ZMod 2) C = 3 ∧
      (∀ x ∈ C, ∀ y ∈ C, ∑ i, x i * y i = 0) ∧
      (∀ x ∈ C, x ≠ 0 → 4 ≤ weight x) ∧
      7 = (∑ i ∈ Finset.range 3, 4 ⌈/⌉ (2 ^ i)) ∧
      (2 ^ 2 : ℕ) ∣ 4 ∧ (∀ x ∈ C, 4 ∣ weight x) := by
  refine ⟨LinearMap.range Binary97.simplexMap,
    Binary97.simplex_equality_control.1,
    Binary97.simplex_equality_control.2.1,
    Binary97.simplex_equality_control.2.2.1, by decide, by decide, ?_⟩
  rintro x ⟨y, rfl⟩
  by_cases hy : y = 0
  · simp [hy, weight]
  · change 4 ∣ Binary97.weight (Binary97.simplexMap y)
    rw [Binary97.simplex_word_weight y hy]

/-- At length 98, Griesmer no longer forces a distance-48 code to be full length.
The strict slack is the obstruction to repeating proof.md section 2 verbatim. -/
theorem negative_length98_fullness_step :
    Binary97.griesmer 8 48 = 97 ∧ Binary97.griesmer 8 48 < 98 := by decide

#print axioms ward_41
#print axioms ward_25
#print axioms ward_17
#print axioms simplex_positive_control
#print axioms negative_length98_fullness_step

/-- No binary self-orthogonal length-97 dimension-8 code has minimum weight at least 46,
conditional only on the explicitly stated Ward theorem. -/
theorem no_so_97_8_46 (hWard : WardBinary) :
    ¬ ∃ C : Submodule (ZMod 2) (Fin 97 → ZMod 2),
        Module.finrank (ZMod 2) C = 8 ∧
        (∀ x ∈ C, ∀ y ∈ C, ∑ i, x i * y i = 0) ∧
        (∀ x ∈ C, x ≠ 0 → 46 ≤ weight x) := by
  exact Binary97.no_so_97 hWard

#print axioms no_so_97_8_46
#print no_so_97_8_46
#print WardBinary