import SharpWasserstein.ExternalInteractionEnergyLimit

/-! Explicit density-weighted versions of the external energy estimate on the
actual Euclidean fundamental cube. Smooth finite potentials have all required
integrability properties as conclusions of compactness. -/
noncomputable section
namespace SharpWasserstein.ExternalInteractionEnergyLimit
open MeasureTheory Filter WeightedTangent WeightedMarginal WeightedDensity
open PeriodicIntegrationByParts PeriodicBochner PeriodicFourierTests PeriodicGalerkin
open PeriodicMarginalLift PeriodicMarginalEnergy PeriodicConvolution
open BochnerIdentity ExternalInteraction
open scoped Topology InnerProductSpace ContDiff BoundedContinuousFunction
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- The actual density-weighted Euclidean cube measure. -/
def weightedCube (ρ : Point n →ᵇ ℝ) : Measure (Point n) :=
  (cubePoint (n := n)).withDensity (fun y => ENNReal.ofReal (ρ y))

omit [BorelSpace (Point n)] in
theorem weightedCube_le (ρ : Point n →ᵇ ℝ) :
    weightedCube ρ ≤ ENNReal.ofReal ‖ρ‖ • (cubePoint (n := n)) := by
  rw [← withDensity_const]
  exact withDensity_mono (Eventually.of_forall (fun y => ENNReal.ofReal_le_ofReal
    ((le_abs_self (ρ y)).trans (ρ.norm_coe_le_norm y))))

omit [BorelSpace (Point n)] in
/-- An actual cube `L²` field remains square-integrable for a bounded density. -/
theorem memLp_weightedCube (ρ : Point n →ᵇ ℝ) {F : Type*} [NormedAddCommGroup F]
    {u : Point n → F} (hu : MemLp u 2 (cubePoint (n := n))) : MemLp u 2 (weightedCube ρ) :=
  MemLp.mono_measure (weightedCube_le ρ) (hu.smul_measure ENNReal.ofReal_ne_top)

omit [BorelSpace (Point n)] in
theorem integrable_weightedCube (ρ : Point n →ᵇ ℝ) {u : Point n → ℝ}
    (hu : Integrable u (cubePoint (n := n))) : Integrable u (weightedCube ρ) :=
  (hu.smul_measure ENNReal.ofReal_ne_top).mono_measure (weightedCube_le ρ)

/-- Every integral here is the literal positive-density weighted integral. -/
theorem integral_weightedCube (ρ : Point n →ᵇ ℝ) (hρ : ∀ y,0 ≤ ρ y) (u : Point n → ℝ) :
    (∫ y,u y ∂weightedCube ρ) = ∫ y,ρ y*u y ∂cubePoint := by
  unfold weightedCube
  rw [integral_withDensity_eq_integral_toReal_smul ρ.continuous.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (hρ _),smul_eq_mul]

/-- Continuity suffices for genuine integrability over the compact cube. -/
theorem continuous_integrable_cubePoint {u : Point n → ℝ} (hu : Continuous u) : Integrable u (cubePoint (n := n)) := by
  apply (coordinateSymm_measurePreserving.integrable_comp hu.aestronglyMeasurable).mp
  exact continuous_integrable_cube (hu.comp (coordinateEquiv n).symm.continuous)

/-- Continuous fields are genuinely square-integrable on the cube. -/
theorem continuous_memLp_cubePoint {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : Point n → F} (hu : Continuous u) : MemLp u 2 (cubePoint (n := n)) :=
  (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr
    (continuous_integrable_cubePoint (hu.norm.pow 2))

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
/-- Continuity of the actual full Hessian-square field, derived from smoothness. -/
theorem continuous_frobenius_hessian {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun y => HierarchyAlgebra.frobeniusSq (hessian f y)) := by
  unfold HierarchyAlgebra.frobeniusSq hessian
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((smooth_directionDeriv (smooth_directionDeriv hf _) _).continuous.pow 2)

variable {d m : ℕ}
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]

/-- The sharp external estimate applied to an actual positive cube density,
with integrability of every smooth-potential term proved from compactness. -/
theorem weighted_external_le (ρ : Point (m*d+d) →ᵇ ℝ) (hρ : ∀ y,0 ≤ ρ y)
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (U : Lp (Point (m*d+d)) 2 (cubePoint (n := m*d+d))) {ε : ℝ} (hε : 0 < ε) :
    2*(∫ z,ρ z*⟪U z,gradient (interaction b f) z⟫_ℝ ∂cubePoint)-
      (∫ z,ρ z*⟪liftedForce b z,
        gradient (fun q => ‖gradient f (prefixProjection (m*d) d q)‖^2) z⟫_ℝ ∂cubePoint) ≤
      (2*(d:ℝ)*L₁+ε)*(∫ z,ρ z*‖gradient f (prefixProjection (m*d) d z)‖^2 ∂cubePoint)+
      ε*(∫ z,ρ z*HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂cubePoint)+
      (gradientConstant d M L₁ L₂*(m:ℝ)/ε)*
        (∫ z,ρ z*‖U z-prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))‖^2 ∂cubePoint) := by
  have hG := memLp_weightedCube ρ (continuous_memLp_cubePoint
    ((smooth_gradient hf).continuous.comp (prefixProjection (m*d) d).continuous))
  have hH := integrable_weightedCube ρ (continuous_integrable_cubePoint
    ((continuous_frobenius_hessian hf).comp (prefixProjection (m*d) d).continuous))
  have hh := integral_external_le (weightedCube ρ) hb hbound hm hM hL₁ hL₂ hf hG hH
    (memLp_weightedCube ρ (Lp.memLp U)) hε
  simpa only [integral_weightedCube ρ hρ] using hh

end SharpWasserstein.ExternalInteractionEnergyLimit
