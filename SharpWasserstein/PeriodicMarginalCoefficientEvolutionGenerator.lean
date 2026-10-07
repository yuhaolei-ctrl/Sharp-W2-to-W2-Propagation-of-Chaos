module

public import SharpWasserstein.Compat
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionEnergy
public import SharpWasserstein.FiniteGeneratorPairing
public import SharpWasserstein.PhysicalFourierTrialBounds

@[expose] public section

/-! Finite coefficient contractions are literal marginal generator integrals.
All source and Gram terms are assembled from the actual finite potentials. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation PeriodicSourceConvolution
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution
open ExternalInteractionPeriodic ExternalInteractionSymmetry
open FiniteCoefficientMatrix FiniteCoefficientEnergy FiniteGradientTrial
open WeightedPeriodicFourierScale (PeriodicOf)
variable {d m N : ℕ} {ι : Type*} [Fintype ι]

/-- Finite coefficient synthesis commutes with the actual marginal cylinder. -/
theorem cylinder_potential (hm : m ≤ N) (a : ι → Point (m*d) → ℝ) (c : EuclideanSpace ℝ ι) :
    cylinder hm (potential a c) = potential (fun i => cylinder hm (a i)) c := by
  funext x
  simp [cylinder,potential]

/-- Exact finite linearity of the genuine split generator. -/
theorem splitGenerator_potential (hm : m ≤ N) (b : Position d → Position d → Position d)
    (a : ι → Point (m*d) → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i)) (c : EuclideanSpace ℝ ι) :
    splitGenerator hm b (potential a c) = potential (fun i => splitGenerator hm b (a i)) c := by
  rw [splitGenerator_eq hm b (BochnerIdentity.contDiff_two_of_smooth (potential_smooth a ha c)),
    cylinder_potential,FiniteGeneratorCalculus.euclideanGenerator_eq,
    FiniteGeneratorCalculus.generator_potential _ _ (fun i => cylinder_smooth hm (ha i))]
  congr 1
  funext i
  rw [splitGenerator_eq hm b (BochnerIdentity.contDiff_two_of_smooth (ha i)),
    FiniteGeneratorCalculus.euclideanGenerator_eq]

/-- The matrix Gram contraction expands the actual squared marginal gradient. -/
theorem splitGenerator_gradientSquare (hm : m ≤ N) (b : Position d → Position d → Position d)
    (a : ι → Point (m*d) → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i)) (c : EuclideanSpace ℝ ι)
    (x : Point (N*d)) :
    splitGenerator hm b (fun y => ‖gradient (potential a c) y‖^2) x =
      ∑ i,∑ j,(c i*c j)*splitGenerator hm b (gramTest (a i) (a j)) x := by
  let A : ι×ι → Point (m*d) → ℝ := fun ij => gramTest (a ij.1) (a ij.2)
  let C : EuclideanSpace ℝ (ι×ι) := WithLp.toLp 2 (fun ij => c ij.1*c ij.2)
  have hs : (fun y => ‖gradient (potential a c) y‖^2) = potential A C := by
    funext y
    rw [FiniteGeneratorCalculus.gradientSquare_potential a ha]
    simp [potential,A,C,gramTest,Fintype.sum_prod_type]
  rw [hs,splitGenerator_potential hm b A (fun ij => gramTest_smooth (ha ij.1) (ha ij.2)) C]
  simp [potential,A,C,Fintype.sum_prod_type]

variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]

/-- Every actual split test has all analytic bounds needed for the integral
contractions, obtained from the genuine full particle generator. -/
theorem splitGenerator_smooth_bounded (hm : m ≤ N)
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (hBf : AllDerivativesBounded f) :
    ContDiff ℝ ∞ (splitGenerator hm b f) ∧ AllDerivativesBounded (splitGenerator hm b f) := by
  rw [splitGenerator_eq hm b (BochnerIdentity.contDiff_two_of_smooth hf)]
  exact ⟨euclideanGenerator_smooth (particleDrift_smooth hb) (cylinder_smooth hm hf),
    euclideanGenerator_bounded (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb)
      (cylinder_smooth hm hf) (cylinder_allDerivativesBounded hm hf hBf)⟩

variable [DecidableEq ι]

theorem matrix_splitGenerator_quadratic (hm : m ≤ N) (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (a : ι → Point (m*d) → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i))
    (hBa : ∀ i,AllDerivativesBounded (a i)) (c : EuclideanSpace ℝ ι) :
    ⟪matrixOperator (fun i j => ∫ x,splitGenerator hm b (gramTest (a i) (a j)) x ∂μ) c,c⟫_ℝ =
      ∫ x,splitGenerator hm b (fun y => ‖gradient (potential a c) y‖^2) x ∂μ := by
  have hI (i j : ι) : Integrable (splitGenerator hm b (gramTest (a i) (a j))) μ := by
    obtain ⟨hs,hB⟩ := splitGenerator_smooth_bounded hm hb (gramTest_smooth (ha i) (ha j))
      (gramTest_allDerivativesBounded (ha i) (ha j) (hBa i) (hBa j))
    obtain ⟨C,_,hC⟩ := hB.bounded
    exact Integrable.of_bound hs.continuous.aestronglyMeasurable C (Eventually.of_forall hC)
  simp_rw [splitGenerator_gradientSquare hm b a ha c]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hI i j).const_mul (c i*c j)))]
  simp_rw [integral_finsetSum _ (fun j _ => (hI _ j).const_mul (c _*c j)),integral_const_mul]
  simp only [PiLp.inner_apply,RCLike.inner_apply,RCLike.conj_to_real,matrixOperator_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem source_splitGenerator_pairing (hm : m ≤ N) (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (a : ι → Point (m*d) → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i))
    (hBa : ∀ i,AllDerivativesBounded (a i)) (U : Lp (Point (N*d)) 2 μ) (c : EuclideanSpace ℝ ι) :
    ⟪coefficientVector (fun i => pairing μ U (splitGenerator hm b (a i))),c⟫_ℝ =
      pairing μ U (splitGenerator hm b (potential a c)) := by
  have hG i := (splitGenerator_smooth_bounded hm hb (ha i) (hBa i)).1
  have hBG i : ∃ C : ℝ,∀ x,‖gradient (splitGenerator hm b (a i)) x‖ ≤ C := by
    obtain ⟨C,_,hC⟩ := (gradient_allDerivativesBounded (hG i)
      (splitGenerator_smooth_bounded hm hb (ha i) (hBa i)).2).bounded
    exact ⟨C,hC⟩
  simp only [pairing,← inner_gradient_left]
  rw [splitGenerator_potential hm b a ha,
    ← gradientMap_source_pairing μ _ hG hBG U c,← ContinuousLinearMap.adjoint_inner_left]
  congr 1
  ext i
  rw [coefficientVector_apply,adjoint_source_coefficient]

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
