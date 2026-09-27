import SharpWasserstein.GaussianHeatCalculus

/-! The actual weak heat equation for the explicit Gaussian sharpness laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Interval
namespace SharpWasserstein.GaussianSharpness

def scaledGaussianExpectation {k : ℕ} (φ : Configuration 1 k → ℝ) (c α : ℝ) : ℝ :=
  ∫ ω, φ (scaledGaussianLabel k c α ω) ∂standardLabels (k+1)

theorem scaledGaussianExpectation_hasDerivAt {k : ℕ} {φ : Configuration 1 k → ℝ}
    (hφ : SmoothCompactTest φ) (c α : ℝ) :
    HasDerivAt (scaledGaussianExpectation φ c)
      (α * scaledGaussianExpectation (laplacian φ) c α) α := by
  letI := standardLabels_probability (k+1)
  choose C hCn hC using fun i : Fin k => compact_test_bound (compact_coordinateDerivative hφ i 0)
  obtain ⟨B, _, hB⟩ := compact_test_bound hφ
  let F := fun β ω => φ (scaledGaussianLabel k c β ω)
  let G := fun β ω => ∑ i : Fin k, ω i.succ * coordinateDerivative φ i 0 (scaledGaussianLabel k c β ω)
  let bound := fun ω : Fin (k+1) → ℝ => ∑ i : Fin k, ‖ω i.succ‖ * C i
  have hFc (β : ℝ) : Continuous (F β) := hφ.1.continuous.comp (scaledGaussianLabel_continuous k c β)
  have hGc (β : ℝ) : Continuous (G β) := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_apply i.succ).mul
      ((compact_coordinateDerivative hφ i 0).1.continuous.comp (scaledGaussianLabel_continuous k c β))
  have hbound : Integrable bound (standardLabels (k+1)) := by
    apply integrable_finsetSum
    intro i _
    exact ((coordinate_memLp (k+1) i.succ).integrable (by norm_num)).norm.mul_const (C i)
  have hGbound (ω : Fin (k+1) → ℝ) (β : ℝ) : ‖G β ω‖ ≤ bound ω := by
    calc
      ‖G β ω‖ ≤ ∑ i : Fin k, ‖ω i.succ * coordinateDerivative φ i 0 (scaledGaussianLabel k c β ω)‖ :=
        norm_sum_le _ _
      _ ≤ bound ω := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hC i _) (norm_nonneg _)
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := standardLabels (k+1)) (F := F) (F' := G) (x₀ := α) (s := Set.univ)
    (bound := bound) (Filter.univ_mem)
    (Eventually.of_forall fun β => (hFc β).aestronglyMeasurable)
    (Integrable.of_bound (hFc α).aestronglyMeasurable B (Eventually.of_forall fun ω => hB _))
    (hGc α).aestronglyMeasurable
    (Eventually.of_forall fun ω β _ => hGbound ω β) hbound
    (Eventually.of_forall fun ω β _ => scaledGaussian_test_hasDerivAt hφ c β ω)
  have hi (i : Fin k) : Integrable
      (fun ω => ω i.succ * coordinateDerivative φ i 0 (scaledGaussianLabel k c α ω))
      (standardLabels (k+1)) :=
    ((coordinate_memLp (k+1) i.succ).integrable (by norm_num)).mul_bdd
      (((compact_coordinateDerivative hφ i 0).1.continuous.comp
        (scaledGaussianLabel_continuous k c α)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => hC i _)
  have hii (i : Fin k) : Integrable
      (fun ω => coordinateDerivative (coordinateDerivative φ i 0) i 0 (scaledGaussianLabel k c α ω))
      (standardLabels (k+1)) := by
    obtain ⟨D, _, hD⟩ := compact_test_bound (compact_coordinateDerivative (compact_coordinateDerivative hφ i 0) i 0)
    exact Integrable.of_bound
      (((compact_coordinateDerivative (compact_coordinateDerivative hφ i 0) i 0).1.continuous.comp
        (scaledGaussianLabel_continuous k c α)).aestronglyMeasurable)
      D (Eventually.of_forall fun ω => hD _)
  have he : (∫ ω, G α ω ∂standardLabels (k+1)) =
      α * scaledGaussianExpectation (laplacian φ) c α := by
    rw [show G α = (fun ω => ∑ i : Fin k, ω i.succ *
        coordinateDerivative φ i 0 (scaledGaussianLabel k c α ω)) from rfl,
      integral_finsetSum _ (fun i _ => hi i)]
    simp_rw [scaledGaussian_coordinate_stein hφ c α]
    rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => hii i)]
    simp only [scaledGaussianExpectation, laplacian, Fin.sum_univ_one]
  rw [he] at hdiff
  exact hdiff.2

theorem scaledGaussianExpectation_continuous {k : ℕ} {φ : Configuration 1 k → ℝ}
    (hφ : SmoothCompactTest φ) (c : ℝ) : Continuous (scaledGaussianExpectation φ c) :=
  continuous_iff_continuousAt.mpr fun α => (scaledGaussianExpectation_hasDerivAt hφ c α).continuousAt

theorem integral_commonNoiseLaw {k : ℕ} {φ : Configuration 1 k → ℝ}
    (hφ : Continuous φ) (a s : ℝ) :
    (∫ x, φ x ∂commonNoiseLaw k a s) =
      scaledGaussianExpectation φ (Real.sqrt s) (Real.sqrt a) := by
  rw [commonNoiseLaw_explicit]
  change (∫ x, φ x ∂(standardLabels (k+1)).map
    (scaledGaussianLabel k (Real.sqrt s) (Real.sqrt a))) = _
  rw [integral_map (scaledGaussianLabel_continuous k _ _).measurable.aemeasurable
    hφ.aestronglyMeasurable]
  rfl

theorem commonNoiseLaw_expectation_continuous {k : ℕ} {φ : Configuration 1 k → ℝ}
    (hφ : SmoothCompactTest φ) (s : ℝ) :
    Continuous (fun t => ∫ x, φ x ∂commonNoiseLaw k (1+2*t) s) := by
  have he : (fun t => ∫ x, φ x ∂commonNoiseLaw k (1+2*t) s) =
      (fun t => scaledGaussianExpectation φ (Real.sqrt s) (Real.sqrt (1+2*t))) :=
    funext fun t => integral_commonNoiseLaw hφ.1.continuous _ _
  rw [he]
  exact (scaledGaussianExpectation_continuous hφ _).comp (by fun_prop)

/-- Derivative of a genuine Gaussian expectation equals the expected Laplacian. -/
theorem commonNoiseLaw_expectation_hasDerivAt {k : ℕ} {φ : Configuration 1 k → ℝ}
    (hφ : SmoothCompactTest φ) (s t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun r => ∫ x, φ x ∂commonNoiseLaw k (1+2*r) s)
      (∫ x, laplacian φ x ∂commonNoiseLaw k (1+2*t) s) t := by
  have ha : 0 < 1+2*t := by positivity
  have hsqrt : Real.sqrt (1+2*t) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hr : HasDerivAt (fun r : ℝ => Real.sqrt (1+2*r)) (1 / Real.sqrt (1+2*t)) t := by
    have hi : HasDerivAt (fun r : ℝ => 1+2*r) 2 t := by
      convert! ((hasDerivAt_id t).const_mul 2).const_add 1 using 1
      simp
    convert! (Real.hasDerivAt_sqrt ha.ne').comp t hi using 1
    field_simp
  have h := (scaledGaussianExpectation_hasDerivAt hφ (Real.sqrt s) (Real.sqrt (1+2*t))).comp t hr
  have he : (fun r => ∫ x, φ x ∂commonNoiseLaw k (1+2*r) s) =
      (fun r => scaledGaussianExpectation φ (Real.sqrt s) (Real.sqrt (1+2*r))) :=
    funext fun r => integral_commonNoiseLaw hφ.1.continuous _ _
  rw [he, integral_commonNoiseLaw (compact_laplacian hφ).1.continuous]
  convert! h using 1
  field_simp [hsqrt]

theorem generator_zero {k : ℕ} (φ : Configuration 1 k → ℝ) :
    generator (fun _ => 0) φ = laplacian φ := by
  funext x
  simp [generator]

/-- All fields of the project's genuine weak heat-evolution predicate are proved. -/
theorem commonNoiseLaw_weakEvolution (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    WeakEvolution (fun _ _ => 0) (fun t => commonNoiseLaw k (1+2*t) s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    exact (commonNoiseLaw_isGaussian k (1+2*t) s).toIsProbabilityMeasure
  · intro t _
    exact commonNoiseLaw_secondMoment k (1+2*t) s
  · intro T hT
    refine ⟨ENNReal.ofReal ((k : ℝ)*(1+2*T+s)), ENNReal.ofReal_lt_top, ?_⟩
    intro t ht
    rw [commonNoiseLaw_secondMoment_value k (by linarith [ht.1]) hs]
    apply ENNReal.ofReal_le_ofReal
    gcongr
    exact ht.2
  · intro φ hφ
    exact (commonNoiseLaw_expectation_continuous hφ s).continuousOn
  · intro φ hφ t _
    rw [generator_zero]
    letI := (commonNoiseLaw_isGaussian k (1+2*t) s).toIsProbabilityMeasure
    obtain ⟨C, _, hC⟩ := compact_test_bound (compact_laplacian hφ)
    exact Integrable.of_bound (compact_laplacian hφ).1.continuous.aestronglyMeasurable
      C (Eventually.of_forall hC)
  · intro φ hφ t _
    simp_rw [generator_zero]
    exact (commonNoiseLaw_expectation_continuous (compact_laplacian hφ) s).intervalIntegrable 0 t
  · intro φ hφ t ht
    simp_rw [generator_zero]
    symm
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro r hr
      rw [Set.uIcc_of_le ht] at hr
      exact commonNoiseLaw_expectation_hasDerivAt hφ s r hr.1
    · exact (commonNoiseLaw_expectation_continuous (compact_laplacian hφ) s).intervalIntegrable 0 t

/-- The correlated Gaussian family is an actual exchangeable zero-interaction particle evolution. -/
theorem particleGaussianLaw_isParticleEvolution (N : ℕ) :
    IsParticleEvolution (fun (_ _ : Position 1) => 0)
      (fun t => particleGaussianLaw N (1+2*t)) := by
  constructor
  · convert! commonNoiseLaw_weakEvolution N (1/(N : ℝ)) (by positivity) using 1
    ext t x i j
    simp [particleDrift]
  · simpa only [mul_zero, add_zero, particleGaussianLaw]
      using commonNoiseLaw_exchangeable N (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ 1/(N : ℝ))

theorem oneParticleGaussian_probability (a : ℝ) : IsProbabilityMeasure (oneParticleGaussian a) := by
  unfold oneParticleGaussian
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The one-particle reference is exactly the zero-common-noise member of the heat family. -/
theorem singleton_oneParticleGaussian_eq_commonNoiseLaw (a : ℝ) :
    singletonLaw (oneParticleGaussian a) = commonNoiseLaw 1 a 0 := by
  have hm : (standardLabels 2).map (fun ω => ω (1 : Fin 2)) = gaussianReal 0 1 :=
    (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) 1).map_eq
  calc
    singletonLaw (oneParticleGaussian a) = (gaussianReal 0 1).map
        (fun z : ℝ => fun (_ : Fin 1) (_ : Fin 1) => Real.sqrt a * z) := by
      unfold singletonLaw oneParticleGaussian
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = ((standardLabels 2).map (fun ω => ω (1 : Fin 2))).map
        (fun z : ℝ => fun (_ : Fin 1) (_ : Fin 1) => Real.sqrt a * z) := by rw [hm]
    _ = commonNoiseLaw 1 a 0 := by
      rw [Measure.map_map (by fun_prop) (by fun_prop), commonNoiseLaw_explicit]
      congr 1
      funext ω i j
      simp [Fin.eq_zero i]

/-- The reference Gaussian family is an actual zero-interaction nonlinear limit evolution. -/
theorem oneParticleGaussian_isLimitEvolution :
    IsLimitEvolution (fun (_ _ : Position 1) => 0)
      (fun t => oneParticleGaussian (1+2*t)) := by
  constructor
  · intro t _
    exact oneParticleGaussian_probability (1+2*t)
  · have hp : (fun t => singletonLaw (oneParticleGaussian (1+2*t))) =
        (fun t => commonNoiseLaw 1 (1+2*t) 0) :=
      funext fun t => singleton_oneParticleGaussian_eq_commonNoiseLaw _
    rw [hp]
    convert! commonNoiseLaw_weakEvolution 1 0 le_rfl using 1
    ext t x i j
    simp [nonlinearDrift]

/-- The identically zero interaction satisfies the precise smooth bounded kernel assumptions. -/
theorem zeroKernel_boundedSmooth : BoundedSmoothKernel (fun (_ _ : Position 1) => 0) := by
  constructor
  · exact contDiff_const
  · intro n
    refine ⟨0, le_rfl, ?_⟩
    intro z
    simp [Function.uncurry_def, iteratedFDeriv_fun_zero]

theorem zeroKernel_bounds : KernelBounds (fun (_ _ : Position 1) => 0) 0 0 0 := by
  constructor <;> intro x y <;> simp

/-- The concrete Gaussian example fulfills every initial-data and evolution hypothesis
of the main propagation target, with zero interaction and C₀=1/4. -/
theorem gaussian_sharpness_hypotheses :
    BoundedSmoothKernel (fun (_ _ : Position 1) => 0) ∧
    KernelBounds (fun (_ _ : Position 1) => 0) 0 0 0 ∧
    IsLimitEvolution (fun (_ _ : Position 1) => 0) (fun t => oneParticleGaussian (1+2*t)) ∧
    (∀ (N : ℕ), 1 ≤ N → IsParticleEvolution (fun (_ _ : Position 1) => 0)
      (fun t => particleGaussianLaw N (1+2*t))) ∧
    InitialHierarchy (1/4) (oneParticleGaussian 1) (fun N => particleGaussianLaw N 1) :=
  ⟨zeroKernel_boundedSmooth, zeroKernel_bounds, oneParticleGaussian_isLimitEvolution,
    fun N _ => particleGaussianLaw_isParticleEvolution N, gaussian_initialHierarchy⟩

/-- A strictly positive fixed-time constant gives the matching sharp rate for actual solutions. -/
theorem gaussian_sharpness_fixed_time (t : ℝ) (ht : 0 ≤ t) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N k : ℕ) (_hk : 0 < k) (hkN : k ≤ N),
      ENNReal.ofReal (c * localRate k N) ≤
        wassersteinSq (marginal hkN (particleGaussianLaw N (1+2*t)))
          (tensorLaw (oneParticleGaussian (1+2*t)) k) := by
  refine ⟨1 / (Real.sqrt ((1+2*t)+1) + Real.sqrt (1+2*t))^2, by positivity, ?_⟩
  intro N k hk hkN
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using
    particleGaussianLaw_fixed_time_lower hk hkN t ht

end SharpWasserstein.GaussianSharpness
