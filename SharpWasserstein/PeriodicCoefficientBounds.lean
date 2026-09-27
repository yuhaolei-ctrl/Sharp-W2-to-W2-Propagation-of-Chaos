import SharpWasserstein.PeriodicSmoothBounds
import SharpWasserstein.PeriodicDriftResidual

/-! Actual global coefficient bounds from periodicity and smoothness. Compactness
of the quotient torus supplies bounds for vector coordinates, first coordinate
partials, and the scalar Laplacian. They remove the auxiliary boundedness inputs
from the genuine Galerkin drift-residual limit. -/

noncomputable section
namespace SharpWasserstein.PeriodicCoefficientBounds
open MeasureTheory Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient WeightedTangent
open scoped ContDiff Topology BoundedContinuousFunction

variable {n : ℕ}

/-- Coordinate periodicity is genuine periodicity of the whole vector field. -/
theorem vector_periodic {b : Coordinates n → Coordinates n}
    (hpb : ∀ j, Periodic (fun x => b x j)) :
    ∀ i, Function.Periodic b (Pi.single i 1) := by
  intro i x
  ext j
  exact hpb j i x

/-- All scalar coordinates of a continuous periodic vector field have one nonnegative global bound. -/
theorem exists_coordinate_bound {b : Coordinates n → Coordinates n}
    (hb : Continuous b) (hpb : ∀ j, Periodic (fun x => b x j)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x j, ‖b x j‖ ≤ A := by
  obtain ⟨A, hA, hbound⟩ := PeriodicSmoothBounds.norm_bound (vector_periodic hpb) hb
  exact ⟨A, hA, fun x j => (norm_le_pi_norm (b x) j).trans (hbound x)⟩

/-- The actual matrix of coordinate derivatives; no independently supplied coefficients. -/
def coordinateDerivativeField (b : Coordinates n → Coordinates n)
    (x : Coordinates n) (i j : Fin n) : ℝ := coordinatePartial (fun y => b y j) i x

theorem continuous_coordinateDerivativeField {b : Coordinates n → Coordinates n}
    (hb : ContDiff ℝ 1 b) : Continuous (coordinateDerivativeField b) :=
  continuous_pi (fun i => continuous_pi (fun j =>
    continuous_coordinatePartial ((contDiff_pi.mp hb) j) i))

theorem periodic_coordinateDerivativeField {b : Coordinates n → Coordinates n}
    (hpb : ∀ j, Periodic (fun x => b x j)) :
    ∀ k, Function.Periodic (coordinateDerivativeField b) (Pi.single k 1) := by
  intro k x
  ext i j
  exact periodic_coordinatePartial (hpb j) i k x

/-- Every actual first coordinate partial has a common global bound, proved from C¹ periodicity. -/
theorem exists_first_partial_bound {b : Coordinates n → Coordinates n}
    (hb : ContDiff ℝ 1 b) (hpb : ∀ j, Periodic (fun x => b x j)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x i j, ‖coordinatePartial (fun y => b y j) i x‖ ≤ D := by
  obtain ⟨D, hD, hbound⟩ := PeriodicSmoothBounds.norm_bound
    (periodic_coordinateDerivativeField hpb) (continuous_coordinateDerivativeField hb)
  refine ⟨D, hD, fun x i j => ?_⟩
  exact ((norm_le_pi_norm (coordinateDerivativeField b x i) j).trans
    (norm_le_pi_norm (coordinateDerivativeField b x) i)).trans (hbound x)

/-- The two scalar bounds used by the actual drift-gradient estimate follow from smooth periodic data. -/
theorem exists_drift_bounds {b : Coordinates n → Coordinates n}
    (hb : ContDiff ℝ ∞ b) (hpb : ∀ j, Periodic (fun x => b x j)) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ (∀ x j, ‖b x j‖ ≤ A) ∧
      (∀ x i j, ‖coordinatePartial (fun y => b y j) i x‖ ≤ D) := by
  obtain ⟨A, hA, hbA⟩ := exists_coordinate_bound hb.continuous hpb
  obtain ⟨D, hD, hbD⟩ := exists_first_partial_bound
    (hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hpb
  exact ⟨A, D, hA, hD, hbA, hbD⟩

/-- The actual coordinate Laplacian remains periodic. -/
theorem periodic_laplacian {f : Coordinates n → ℝ} (hpf : Periodic f) :
    Periodic (PeriodicIntegrationByParts.laplacian f) := by
  intro k x
  apply Finset.sum_congr rfl
  intro i _
  exact periodic_coordinatePartial (periodic_coordinatePartial hpf i) i k x

/-- C² regularity suffices for continuity of the actual Laplacian. -/
theorem continuous_laplacian {f : Coordinates n → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (PeriodicIntegrationByParts.laplacian f) :=
  continuous_finsetSum Finset.univ (fun i _ =>
    continuous_coordinatePartial (contDiff_coordinatePartial hf i) i)

/-- The Laplacian of a C² periodic scalar field has a nonnegative global absolute bound. -/
theorem exists_laplacian_norm_bound {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ 2 f) (hpf : Periodic f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖PeriodicIntegrationByParts.laplacian f x‖ ≤ B :=
  PeriodicSmoothBounds.norm_bound (periodic_laplacian hpf) (continuous_laplacian hf)

/-- In particular, the nonnegative upper bound needed by the elliptic estimate is derived, not assumed. -/
theorem exists_laplacian_upper_bound {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ 2 f) (hpf : Periodic f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, PeriodicIntegrationByParts.laplacian f x ≤ B := by
  obtain ⟨B, hB, hbound⟩ := exists_laplacian_norm_bound hf hpf
  exact ⟨B, hB, fun x => (le_abs_self _).trans (hbound x)⟩

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- The actual Galerkin drift residual vanishes using only the natural smooth
periodic data and elliptic source pairing; all three auxiliary global bounds
are obtained from the preceding compactness theorems. -/
theorem residual_tendsto_zero_of_smooth (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {σ : Coordinates n → ℝ} {a : ℝ}
    (ha : 0 < a) (hp : ∀ y, a ≤ ρ y)
    (hρ : ContDiff ℝ 2 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ (trialGradient s ψ) = ∫ x, σ x * ψ.val x ∂cube n)
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b)
    (hpb : ∀ j, Periodic (fun x => b x j)) :
    Tendsto (PeriodicDriftResidual.residual ρ ℓ b hb) atTop (𝓝 0) := by
  obtain ⟨B, hB, hΔρ⟩ := exists_laplacian_upper_bound hρ hpρ
  obtain ⟨A, D, hA, hD, hbA, hbD⟩ := exists_drift_bounds hb hpb
  exact PeriodicDriftResidual.residual_tendsto_zero ρ ℓ ha hB hp hρ hpρ
    (Filter.Eventually.of_forall hΔρ) hσ hpσ hsource hb hA hD hbA hbD

end SharpWasserstein.PeriodicCoefficientBounds
