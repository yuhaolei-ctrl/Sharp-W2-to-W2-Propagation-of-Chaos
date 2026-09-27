import SharpWasserstein.ExternalInteractionSymmetry

/-! Exact external-particle averaging of genuine tangent derivative pairings.
The finite-N coefficient is derived from the cardinality of the external
index set; it is not a premise of any hierarchy estimate. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.ExternalInteractionSymmetry
open WeightedTangent PropagatedSourcePermutation

/-- Literal action of a vector field on an actual scalar differential. -/
def pairing {n : ℕ} [MeasurableSpace (Point n)] (μ : Measure (Point n))
    (U : Point n → Point n) (F : Point n → ℝ) : ℝ :=
  ∫ x, fderiv ℝ F x (U x) ∂μ

/-- An invariant carrying law and an equivariant actual field give the correct
pullback-invariance of the scalar derivative action. -/
theorem pairing_invariant {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
    (μ : Measure (Point n)) (L : Point n ≃L[ℝ] Point n) (hμ : μ.map L = μ)
    (U : Point n → Point n) (hU : ∀ᵐ x ∂μ, U (L x) = L (U x)) (F : Point n → ℝ) :
    pairing μ U (F ∘ L) = pairing μ U F := by
  unfold pairing
  simp_rw [L.comp_right_fderiv]
  change (∫ x, fderiv ℝ F (L x) (L (U x)) ∂μ) = _
  have he : (∫ x, fderiv ℝ F (L x) (L (U x)) ∂μ) =
      ∫ x, fderiv ℝ F (L x) (U (L x)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hU] with x hx
    rw [hx]
  rw [he]
  have hi := integral_map_equiv (μ := μ) L.toHomeomorph.toMeasurableEquiv
    (fun x => fderiv ℝ F x (U x))
  change (∫ x, fderiv ℝ F x (U x) ∂μ.map L) =
    ∫ x, fderiv ℝ F (L x) (U (L x)) ∂μ at hi
  rw [hμ] at hi
  exact hi.symm

variable {d m N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- For a genuine exchangeable tangent field every external observation has
the same differential pairing as the next particle. -/
theorem external_pairing_eq (hm : m < N) (μ : Measure (Point (N*d)))
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (U : Point (N*d) → Point (N*d))
    (hU : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ,
      U (euclideanPermutation e x) = euclideanPermutation e (U x))
    (j : Fin N) (hj : m ≤ j.val) (F : Point (m*d+d) → ℝ) :
    pairing μ U (F ∘ observation hm.le j) = pairing μ U (F ∘ observation hm.le ⟨m,hm⟩) := by
  rw [← observation_test_swap hm j hj F]
  exact pairing_invariant μ _ (hμ _) U (hU _) _

/-- The exact set of external labels has N−m elements. -/
theorem external_card (hm : m < N) :
    (Finset.univ.filter (fun j : Fin N => m ≤ j.val)).card = N-m := by
  classical
  have he : Finset.univ.filter (fun j : Fin N => m ≤ j.val) =
      Finset.Ici (⟨m,hm⟩ : Fin N) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    rfl
  rw [he, Fin.card_Ici]

/-- Summing the literal external derivative pairings gives the exact multiplicity. -/
theorem external_pairing_sum (hm : m < N) (μ : Measure (Point (N*d)))
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (U : Point (N*d) → Point (N*d))
    (hU : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ,
      U (euclideanPermutation e x) = euclideanPermutation e (U x))
    (F : Point (m*d+d) → ℝ) :
    (∑ j : Fin N with m ≤ j.val, pairing μ U (F ∘ observation hm.le j)) =
      ((N:ℝ)-m)*pairing μ U (F ∘ observation hm.le ⟨m,hm⟩) := by
  classical
  calc
    _ = ∑ _j ∈ Finset.univ.filter (fun j : Fin N => m ≤ j.val),
        pairing μ U (F ∘ observation hm.le ⟨m,hm⟩) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact external_pairing_eq hm μ hμ U hU j (Finset.mem_filter.mp hj).2 F
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, external_card hm, Nat.cast_sub hm.le]

/-- The actual mean-field normalization gives (N−m)/N, retaining the exact
finite-N coefficient before any upper bound is applied. -/
theorem external_pairing_meanField (hm : m < N) (μ : Measure (Point (N*d)))
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (U : Point (N*d) → Point (N*d))
    (hU : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ,
      U (euclideanPermutation e x) = euclideanPermutation e (U x))
    (F : Point (m*d+d) → ℝ) :
    (N:ℝ)⁻¹*(∑ j : Fin N with m ≤ j.val, pairing μ U (F ∘ observation hm.le j)) =
      (((N:ℝ)-m)/N)*pairing μ U (F ∘ observation hm.le ⟨m,hm⟩) := by
  rw [external_pairing_sum hm μ hμ U hU, div_eq_mul_inv]
  ring

omit [BorelSpace (Point (N*d))] in
/-- At the terminal level the actual external index set is empty. -/
theorem external_pairing_terminal (μ : Measure (Point (N*d)))
    (U : Point (N*d) → Point (N*d)) (F : Point (N*d+d) → ℝ) :
    (∑ j : Fin N with N ≤ j.val, pairing μ U (F ∘ observation le_rfl j)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j hj
  have hh := (Finset.mem_filter.mp hj).2
  omega

/-- Scalar source symmetry suffices: equivariance of its actual minimum-energy
field is proved by uniqueness, then the real external sum is collapsed. -/
theorem canonical_external_pairing_meanField (hm : m < N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (hσE : FiniteEnergy μ σ)
    (hσ : ∀ e : Equiv.Perm (Fin N), ∀ φ : Test (N*d),
      σ (pullTest (euclideanPermutation e) φ) = σ φ)
    (F : Point (m*d+d) → ℝ) :
    (N:ℝ)⁻¹*(∑ j : Fin N with m ≤ j.val,
      pairing μ (representative μ σ : Lp (Point (N*d)) 2 μ) (F ∘ observation hm.le j)) =
      (((N:ℝ)-m)/N)*pairing μ (representative μ σ : Lp (Point (N*d)) 2 μ)
        (F ∘ observation hm.le ⟨m,hm⟩) := by
  apply external_pairing_meanField hm μ hμ
  intro e
  exact WeightedSourceSymmetry.representative_equivariant μ (euclideanPermutationIsometry e)
    (hμ e) σ hσE (hσ e)

end SharpWasserstein.ExternalInteractionSymmetry
