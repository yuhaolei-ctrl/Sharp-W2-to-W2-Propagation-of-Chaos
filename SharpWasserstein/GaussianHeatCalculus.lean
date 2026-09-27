import SharpWasserstein.GaussianStein
import SharpWasserstein.GaussianHeat

/-! Calculus of compact smooth tests along explicit Gaussian labels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace SharpWasserstein.GaussianSharpness

theorem insertNth_affine {n : ℕ} (i : Fin (n+1)) (ω : Fin n → ℝ) (z : ℝ) :
    i.insertNth z ω = i.insertNth 0 ω + z • Pi.single i 1 := by
  apply funext
  rw [Fin.forall_iff_succAbove i]
  constructor
  · simp
  · intro j
    simp [Fin.succAbove_ne]

theorem insertNth_hasDerivAt {n : ℕ} (i : Fin (n+1)) (ω : Fin n → ℝ) (z : ℝ) :
    HasDerivAt (fun y : ℝ => i.insertNth (α := fun _ : Fin (n+1) => ℝ) y ω)
      (Pi.single i (1 : ℝ)) z := by
  rw [show (fun y : ℝ => i.insertNth (α := fun _ : Fin (n+1) => ℝ) y ω) =
    (fun y => i.insertNth 0 ω + y • Pi.single i 1) from funext (insertNth_affine i ω)]
  convert! (hasDerivAt_const z (i.insertNth (0 : ℝ) ω)).add
    ((hasDerivAt_id z).smul_const (Pi.single i (1 : ℝ) : Fin (n+1) → ℝ)) using 1
  simp

/-- The labels use the square-root variance α and the fixed common-noise amplitude c. -/
def scaledGaussianLabel (k : ℕ) (c α : ℝ) (ω : Fin (k+1) → ℝ) : Configuration 1 k :=
  fun i _ => α * ω i.succ + c * ω 0

theorem scaledGaussianLabel_continuous (k : ℕ) (c α : ℝ) :
    Continuous (scaledGaussianLabel k c α) := by unfold scaledGaussianLabel; fun_prop

theorem scaledGaussianLabel_joint_continuous (k : ℕ) (c : ℝ) :
    Continuous (fun p : ℝ × (Fin (k+1) → ℝ) => scaledGaussianLabel k c p.1 p.2) := by
  unfold scaledGaussianLabel
  fun_prop

theorem scaledGaussianLabel_hasDerivAt (k : ℕ) (c α : ℝ) (ω : Fin (k+1) → ℝ) :
    HasDerivAt (fun β => scaledGaussianLabel k c β ω) (fun i (_ : Fin 1) => ω i.succ) α := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simpa only [scaledGaussianLabel, id_eq, one_mul] using
    ((hasDerivAt_id α).mul_const (ω i.succ)).add_const (c * ω 0)

theorem scaledGaussianLabel_insert_hasDerivAt (k : ℕ) (c α : ℝ) (i : Fin k)
    (ω : Fin k → ℝ) (z : ℝ) :
    HasDerivAt (fun y => scaledGaussianLabel k c α (i.succ.insertNth y ω))
      (α • coordinateVector i 0) z := by
  have hins := insertNth_hasDerivAt i.succ ω z
  apply hasDerivAt_pi.mpr
  intro j
  apply hasDerivAt_pi.mpr
  intro q
  have hj := (hasDerivAt_pi.mp hins) j.succ
  have h0 := (hasDerivAt_pi.mp hins) 0
  have h := (hj.const_mul α).add (h0.const_mul c)
  convert! h using 1
  simp [coordinateVector, Pi.single_apply, Fin.eq_zero q, eq_comm]

theorem compact_coordinateDerivative {k : ℕ} {φ : Configuration 1 k → ℝ}
    (hφ : SmoothCompactTest φ) (i : Fin k) (q : Fin 1) :
    SmoothCompactTest (coordinateDerivative φ i q) := by
  refine ⟨?_, hφ.2.fderiv_apply ℝ (coordinateVector i q)⟩
  exact (hφ.1.fderiv_right (by simp)).clm_apply contDiff_const

theorem compact_laplacian {k : ℕ} {φ : Configuration 1 k → ℝ}
    (hφ : SmoothCompactTest φ) : SmoothCompactTest (laplacian φ) := by
  constructor
  · apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro q _
    exact (compact_coordinateDerivative (compact_coordinateDerivative hφ i q) i q).1
  · have hc : HasCompactSupport (∑ i : Fin k, ∑ q : Fin 1,
        coordinateDerivative (coordinateDerivative φ i q) i q) := by
      apply HasCompactSupport.finset_sum
      intro i _
      apply HasCompactSupport.finset_sum
      intro q _
      exact (compact_coordinateDerivative (compact_coordinateDerivative hφ i q) i q).2
    convert hc using 1
    ext x
    simp [laplacian, Finset.sum_apply]

/-- Compactness gives an actual global test bound. -/
theorem compact_test_bound {k : ℕ} {φ : Configuration 1 k → ℝ}
    (hφ : SmoothCompactTest φ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hφ.2.isCompact_range hφ.1.continuous).isBounded.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun x => (hC _ (Set.mem_range_self x)).trans (le_max_left _ _)⟩

theorem gaussianVelocity_decomposition (k : ℕ) (ω : Fin (k+1) → ℝ) :
    (fun i (_ : Fin 1) => ω i.succ) = ∑ i : Fin k, ω i.succ • coordinateVector i 0 := by
  funext j q
  simp [Finset.sum_apply, coordinateVector, Fin.eq_zero q, Pi.smul_apply, smul_eq_mul,
    mul_ite]

theorem scaledGaussian_test_hasDerivAt {k : ℕ} {φ : Configuration 1 k → ℝ}
    (hφ : SmoothCompactTest φ) (c α : ℝ) (ω : Fin (k+1) → ℝ) :
    HasDerivAt (fun β => φ (scaledGaussianLabel k c β ω))
      (∑ i : Fin k, ω i.succ * coordinateDerivative φ i 0 (scaledGaussianLabel k c α ω)) α := by
  have h := (hφ.1.differentiable (by simp) (scaledGaussianLabel k c α ω)).hasFDerivAt.comp_hasDerivAt
    α (scaledGaussianLabel_hasDerivAt k c α ω)
  rw [gaussianVelocity_decomposition] at h
  simpa only [Function.comp_def, map_sum, map_smul, smul_eq_mul, coordinateDerivative] using h

theorem scaledGaussian_coordinate_test_hasDerivAt {k : ℕ} {φ : Configuration 1 k → ℝ}
    (hφ : SmoothCompactTest φ) (c α : ℝ) (i : Fin k) (ω : Fin k → ℝ) (z : ℝ) :
    HasDerivAt (fun y => φ (scaledGaussianLabel k c α (i.succ.insertNth y ω)))
      (α * coordinateDerivative φ i 0 (scaledGaussianLabel k c α (i.succ.insertNth z ω))) z := by
  have h := (hφ.1.differentiable (by simp)
      (scaledGaussianLabel k c α (i.succ.insertNth z ω))).hasFDerivAt.comp_hasDerivAt z
    (scaledGaussianLabel_insert_hasDerivAt k c α i ω z)
  simpa only [Function.comp_def, map_smul, smul_eq_mul, coordinateDerivative] using h

/-- Product Stein turns the derivative in a Gaussian label into a true spatial second derivative. -/
theorem scaledGaussian_coordinate_stein {k : ℕ} {φ : Configuration 1 k → ℝ}
    (hφ : SmoothCompactTest φ) (c α : ℝ) (i : Fin k) :
    (∫ ω, ω i.succ * coordinateDerivative φ i 0 (scaledGaussianLabel k c α ω)
      ∂standardLabels (k+1)) =
      α * ∫ ω, coordinateDerivative (coordinateDerivative φ i 0) i 0
        (scaledGaussianLabel k c α ω) ∂standardLabels (k+1) := by
  have h1 := compact_coordinateDerivative hφ i 0
  have h2 := compact_coordinateDerivative h1 i 0
  obtain ⟨C, _, hC⟩ := compact_test_bound h1
  obtain ⟨D, _, hD⟩ := compact_test_bound h2
  have hf : Continuous (fun ω => coordinateDerivative φ i 0 (scaledGaussianLabel k c α ω)) :=
    h1.1.continuous.comp (scaledGaussianLabel_continuous k c α)
  have hg : Continuous (fun ω => α * coordinateDerivative (coordinateDerivative φ i 0) i 0
      (scaledGaussianLabel k c α ω)) :=
    continuous_const.mul (h2.1.continuous.comp (scaledGaussianLabel_continuous k c α))
  have hi := standardLabels_stein i.succ hf.aestronglyMeasurable hg.aestronglyMeasurable
    (scaledGaussian_coordinate_test_hasDerivAt h1 c α i)
    (fun ω => hg.comp (continuous_iff_continuousAt.mpr
      (fun z => (insertNth_hasDerivAt i.succ ω z).continuousAt))) C (‖α‖*D)
    (fun ω => hC _) (fun ω => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hD _) (norm_nonneg α))
  rw [integral_const_mul] at hi
  exact hi

end SharpWasserstein.GaussianSharpness
