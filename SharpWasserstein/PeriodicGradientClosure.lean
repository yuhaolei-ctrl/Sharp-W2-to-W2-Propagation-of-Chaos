import SharpWasserstein.PeriodicGalerkin

/-! The actual closed periodic tangent space and strong Fourier Galerkin
convergence. It is deliberately a subspace of the cube's compact-test gradient
closure: nonperiodic cube gradients are not silently identified with torus
ones. The optimizer is constructed by coercive inversion on this closed space. -/

noncomputable section
namespace SharpWasserstein.PeriodicGradientClosure
open MeasureTheory Set Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open WeightedTangent WeightedDensity WeightedEnergyDerivative PeriodicGalerkin
open scoped ENNReal InnerProductSpace BigOperators Topology BoundedContinuousFunction ContDiff

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- Enlarging the finite frequency set enlarges the actual gradient trial space. -/
theorem trialSpace_mono : Monotone (trialSpace (n := n)) := by
  intro s t hst v hv
  obtain ⟨f, rfl⟩ := hv
  have hf : f.val ∈ frequencySpace t :=
    Submodule.span_mono (Set.image_mono hst) f.property
  refine ⟨⟨f.val, hf⟩, ?_⟩
  rfl

/-- Closure of all actual finite Fourier gradients in the fundamental cube. -/
def periodicSpace : Submodule ℝ (gradientClosure (cubePoint (n := n))) :=
  (⨆ s, trialSpace s).topologicalClosure

instance periodicSpace_complete : CompleteSpace (periodicSpace (n := n)) := by
  unfold periodicSpace
  infer_instance

theorem trialSpace_le_periodicSpace (s : Finset ((Fin n → ℤ) × Bool)) :
    trialSpace s ≤ periodicSpace :=
  (le_iSup (trialSpace (n := n)) s).trans (iSup (trialSpace (n := n))).le_topologicalClosure

/-- The periodic weighted optimizer is constructed on the periodic closed space. -/
def optimizer (ρ : Point n →ᵇ ℝ) (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ) :
    periodicSpace (n := n) :=
  GalerkinApproximation.solution periodicSpace (weightedOperator (cubePoint (n := n)) ρ)
    (TangentEnergy.rieszRepresentative ℓ)

/-- Its weak equation holds against every vector in the periodic gradient closure. -/
theorem optimizer_equation (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂(cubePoint (n := n)), a ≤ ρ y)
    (w : periodicSpace (n := n)) :
    ⟪weightedOperator (cubePoint (n := n)) ρ (optimizer ρ ℓ : gradientClosure (cubePoint (n := n))),
      (w : gradientClosure (cubePoint (n := n)))⟫_ℝ = ℓ w := by
  simpa only [optimizer, TangentEnergy.inner_rieszRepresentative] using
    GalerkinApproximation.solution_equation periodicSpace (weightedOperator (cubePoint (n := n)) ρ)
      (TangentEnergy.rieszRepresentative ℓ) ha
      (WeightedGalerkin.weightedOperator_lower_bound (cubePoint (n := n)) ρ hp) w

/-- Céa's estimate uses the actual closed-space weak equation, not a stronger
whole-cube equation that a periodic optimizer need not satisfy. -/
theorem vector_error_le (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂(cubePoint (n := n)), a ≤ ρ y)
    (s : Finset ((Fin n → ℤ) × Bool)) (w : trialSpace s) :
    ‖(optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) - vector ρ ℓ s‖ ≤
      (‖weightedOperator (cubePoint (n := n)) ρ‖ / a) *
        ‖(optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) - (w : gradientClosure (cubePoint (n := n)))‖ := by
  let A := weightedOperator (cubePoint (n := n)) ρ
  let u : gradientClosure (cubePoint (n := n)) := optimizer ρ ℓ
  let v : gradientClosure (cubePoint (n := n)) := vector ρ ℓ s
  have hv : v ∈ trialSpace s :=
    (GalerkinApproximation.solution (trialSpace s) A (TangentEnergy.rieszRepresentative ℓ)).property
  have ho : ⟪A (u - v), (w : gradientClosure (cubePoint (n := n))) - v⟫_ℝ = 0 := by
    have hu := optimizer_equation ρ ℓ ha hp
      ⟨(w : gradientClosure (cubePoint (n := n))) - v,
        trialSpace_le_periodicSpace s ((trialSpace s).sub_mem w.property hv)⟩
    have hvEq := GalerkinApproximation.solution_equation (trialSpace s) A
      (TangentEnergy.rieszRepresentative ℓ) ha
      (WeightedGalerkin.weightedOperator_lower_bound (cubePoint (n := n)) ρ hp)
      ⟨(w : gradientClosure (cubePoint (n := n))) - v, (trialSpace s).sub_mem w.property hv⟩
    rw [TangentEnergy.inner_rieszRepresentative] at hvEq
    rw [map_sub, inner_sub_left]
    exact sub_eq_zero.mpr (hu.trans hvEq.symm)
  have he : ⟪A (u - v), u - v⟫_ℝ = ⟪A (u - v), u - (w : gradientClosure (cubePoint (n := n)))⟫_ℝ := by
    simp only [inner_sub_right] at ho ⊢
    linarith
  have hb : a * ‖u - v‖ ^ 2 ≤ ‖A‖ * ‖u - v‖ * ‖u - (w : gradientClosure (cubePoint (n := n)))‖ := by
    calc
      _ ≤ ⟪A (u - v), u - v⟫_ℝ := WeightedGalerkin.weightedOperator_lower_bound (cubePoint (n := n)) ρ hp _
      _ = _ := he
      _ ≤ ‖A (u - v)‖ * ‖u - (w : gradientClosure (cubePoint (n := n)))‖ := real_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
  change ‖u - v‖ ≤ (‖A‖ / a) * ‖u - (w : gradientClosure (cubePoint (n := n)))‖
  by_cases hz : ‖u - v‖ = 0
  · rw [hz]
    positivity
  · have hepos : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    nlinarith

/-- The actual Fourier optimizers converge strongly to the actual periodic optimizer. -/
theorem vector_tendsto (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂(cubePoint (n := n)), a ≤ ρ y) :
    Tendsto (vector ρ ℓ) atTop (𝓝 (optimizer ρ ℓ : gradientClosure (cubePoint (n := n)))) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let C := ‖weightedOperator (cubePoint (n := n)) ρ‖ / a
  have hC : 0 ≤ C := div_nonneg (ContinuousLinearMap.opNorm_nonneg _) ha.le
  have hu : (optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) ∈
      (⨆ s, trialSpace s).topologicalClosure := by
    exact (optimizer ρ ℓ).property
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hu
  obtain ⟨w, hw, hdist⟩ := hu (ε / (C + 1)) (by positivity)
  obtain ⟨s, hs⟩ := (Submodule.mem_iSup_of_directed _ trialSpace_mono.directed_le).mp hw
  refine ⟨s, fun t ht => ?_⟩
  have he := vector_error_le ρ ℓ ha hp t ⟨w, trialSpace_mono ht hs⟩
  rw [dist_eq_norm] at hdist
  rw [dist_eq_norm, norm_sub_rev]
  calc
    _ ≤ C * ‖(optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) - w‖ := he
    _ ≤ (C + 1) * ‖(optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) - w‖ := by
      gcongr
      linarith
    _ < ε := by
      have := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp hdist
      nlinarith

/-- The solved finite periodic energies converge to the closed-space energy. -/
theorem energy_tendsto (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂(cubePoint (n := n)), a ≤ ρ y) :
    Tendsto (fun s => ℓ (vector ρ ℓ s)) atTop (𝓝 (ℓ (optimizer ρ ℓ))) :=
  ℓ.continuous.continuousAt.tendsto.comp (vector_tendsto ρ ℓ ha hp)

/-- Differentiating the genuine periodic optimizer uses operator inversion;
no differentiability of a selected potential is assumed. -/
theorem hasDerivAt_energy
    {ρ : ℝ → (Point n →ᵇ ℝ)} {ρ' : Point n →ᵇ ℝ}
    {ℓ : ℝ → (gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)}
    {ℓ' : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ}
    {t a : ℝ} (hρ : HasDerivAt ρ ρ' t) (hℓ : HasDerivAt ℓ ℓ' t)
    (ha : 0 < a) (hp : ∀ᵐ y ∂(cubePoint (n := n)), a ≤ ρ t y) :
    HasDerivAt (fun r => ℓ r (optimizer (ρ r) (ℓ r)))
      (2 * ℓ' (optimizer (ρ t) (ℓ t)) -
        ∫ y, ρ' y * ‖((optimizer (ρ t) (ℓ t) : gradientClosure (cubePoint (n := n))) :
          Lp (Point n) 2 (cubePoint (n := n))) y‖ ^ 2 ∂(cubePoint (n := n))) t := by
  have hA : HasDerivAt (fun r => weightedOperator (cubePoint (n := n)) (ρ r))
      (weightedOperator (cubePoint (n := n)) ρ') t :=
    HasFDerivAt.comp_hasDerivAt (F := Point n →ᵇ ℝ)
      (E := gradientClosure (cubePoint (n := n)) →L[ℝ] gradientClosure (cubePoint (n := n))) t
      (weightedOperator (cubePoint (n := n))).hasFDerivAt hρ
  have hf := HasFDerivAt.comp_hasDerivAt (F := gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (E := gradientClosure (cubePoint (n := n))) t (rieszMap (cubePoint (n := n))).hasFDerivAt hℓ
  have h := GalerkinApproximation.hasDerivAt_energy periodicSpace hA hf ha
    (WeightedGalerkin.weightedOperator_lower_bound (cubePoint (n := n)) (ρ t) hp)
    (weightedOperator_symmetric (cubePoint (n := n)) (ρ t))
  simpa only [Function.comp_apply, rieszMap_apply, TangentEnergy.inner_rieszRepresentative,
    weightedOperator_inner, real_inner_self_eq_norm_sq, optimizer] using h

/-- The finite Fourier optimized energy has the corresponding actual density derivative. -/
theorem hasDerivAt_finiteEnergy
    {ρ : ℝ → (Point n →ᵇ ℝ)} {ρ' : Point n →ᵇ ℝ}
    {ℓ : ℝ → (gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)}
    {ℓ' : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ}
    {t a : ℝ} (hρ : HasDerivAt ρ ρ' t) (hℓ : HasDerivAt ℓ ℓ' t)
    (ha : 0 < a) (hp : ∀ᵐ y ∂(cubePoint (n := n)), a ≤ ρ t y)
    (s : Finset ((Fin n → ℤ) × Bool)) :
    HasDerivAt (fun r => ℓ r (vector (ρ r) (ℓ r) s))
      (2 * ℓ' (vector (ρ t) (ℓ t) s) -
        ∫ y, ρ' y * ‖(vector (ρ t) (ℓ t) s : Lp (Point n) 2 (cubePoint (n := n))) y‖ ^ 2 ∂(cubePoint (n := n))) t := by
  have hA : HasDerivAt (fun r => weightedOperator (cubePoint (n := n)) (ρ r))
      (weightedOperator (cubePoint (n := n)) ρ') t :=
    HasFDerivAt.comp_hasDerivAt (F := Point n →ᵇ ℝ)
      (E := gradientClosure (cubePoint (n := n)) →L[ℝ] gradientClosure (cubePoint (n := n))) t
      (weightedOperator (cubePoint (n := n))).hasFDerivAt hρ
  have hf := HasFDerivAt.comp_hasDerivAt (F := gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (E := gradientClosure (cubePoint (n := n))) t (rieszMap (cubePoint (n := n))).hasFDerivAt hℓ
  have h := GalerkinApproximation.hasDerivAt_energy (trialSpace s) hA hf ha
    (WeightedGalerkin.weightedOperator_lower_bound (cubePoint (n := n)) (ρ t) hp)
    (weightedOperator_symmetric (cubePoint (n := n)) (ρ t))
  simpa only [Function.comp_apply, rieszMap_apply, TangentEnergy.inner_rieszRepresentative,
    weightedOperator_inner, real_inner_self_eq_norm_sq, vector] using h

/-- Strong convergence passes the genuine density/source derivative values to the limit. -/
theorem derivativePairing_tendsto (ρ ρ' : Point n →ᵇ ℝ)
    (ℓ ℓ' : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂(cubePoint (n := n)), a ≤ ρ y) :
    Tendsto (fun s => 2 * ℓ' (vector ρ ℓ s) -
        ∫ y, ρ' y * ‖(vector ρ ℓ s : Lp (Point n) 2 (cubePoint (n := n))) y‖ ^ 2 ∂(cubePoint (n := n)))
      atTop (𝓝 (2 * ℓ' (optimizer ρ ℓ) -
        ∫ y, ρ' y * ‖((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) :
          Lp (Point n) 2 (cubePoint (n := n))) y‖ ^ 2 ∂(cubePoint (n := n)))) := by
  have hc : Continuous (fun v : gradientClosure (cubePoint (n := n)) =>
      2 * ℓ' v - ⟪weightedOperator (cubePoint (n := n)) ρ' v, v⟫_ℝ) := by fun_prop
  have h := hc.continuousAt.tendsto.comp (vector_tendsto ρ ℓ ha hp)
  simpa only [Function.comp_def, weightedOperator_inner, real_inner_self_eq_norm_sq] using h

end SharpWasserstein.PeriodicGradientClosure
