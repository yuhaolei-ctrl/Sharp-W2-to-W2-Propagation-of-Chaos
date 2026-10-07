module

public import SharpWasserstein.Compat
public import SharpWasserstein.PropagatedFlux
public import SharpWasserstein.FlowSemigroupDerivativePairing

@[expose] public section

/-! Actual fixed-time propagation of a finite-energy source by the constructed
flow semigroup. The flux is J_t(x,w)u(x), under the genuine product input law. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace
namespace SharpWasserstein.PropagatedFlux.Flow
open WeightedTangent FlowInitialDerivative NoiseAverage FlowSemigroupDerivative
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]
  {b : Point d → Point d} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
  {T : ℝ} [MeasurableSpace C(Icc 0 T,Point d)] [BorelSpace C(Icc 0 T,Point d)]
  (hT : 0 ≤ T) (ξ : Measure C(Icc 0 T,Point d)) [IsProbabilityMeasure ξ]
  {t : ℝ} (ht : t ∈ Icc 0 T)
  (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Point d)) [IsFiniteMeasure μ]

/-- The actual random endpoint. -/
def endpoint (q : Point d × C(Icc 0 T,Point d)) : Point d :=
  BoundedFlow.flow hv hb hl hT q.1 q.2 t

/-- The initial field transported by the actual initial-value derivative. -/
def velocity (u : Point d → Point d) (q : Point d × C(Icc 0 T,Point d)) : Point d :=
  fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y q.2 t) q.1 (u q.1)

include ht in
theorem endpoint_measurable : Measurable (endpoint hv hb hl hT (t := t)) :=
  (BoundedFlow.flow_continuous hv hb hl hT ht).measurable

include ht hbs hB in
omit [IsFiniteMeasure μ] in
/-- L² membership of the actual random flux is proved from the initial field. -/
theorem velocity_memLp {u : Point d → Point d} (hu : MemLp u 2 μ) :
    MemLp (velocity hv hb hl hT (t := t) u) 2 (μ.prod ξ) :=
  boundedFlow_fderiv_apply_memLp hv hb hl hbs hB hT ht (μ.prod ξ)
    (hu.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ξ)))

/-- The actual propagated distribution on compact smooth output tests. -/
def source (u : Point d → Point d) (hu : MemLp u 2 μ) : Test d →ₗ[ℝ] ℝ :=
  PropagatedFlux.source (μ.prod ξ) (endpoint hv hb hl hT (t := t))
    (endpoint_measurable hv hb hl hT ht)
    ((velocity_memLp hv hb hl hT ξ ht hbs hB μ hu).toLp (velocity hv hb hl hT (t := t) u))

/-- Exact pairing of the propagated source with the pushed actual vector. -/
theorem source_apply (u : Point d → Point d) (hu : MemLp u 2 μ) (φ : Test d) :
    source hv hb hl hT ξ ht hbs hB μ u hu φ =
      ∫ q : Point d × C(Icc 0 T,Point d), fderiv ℝ (φ : Point d → ℝ) (endpoint hv hb hl hT (t := t) q)
        (velocity hv hb hl hT (t := t) u q) ∂μ.prod ξ := by
  rw [source,PropagatedFlux.source_apply]
  apply integral_congr_ae
  filter_upwards [(velocity_memLp hv hb hl hT ξ ht hbs hB μ hu).coeFn_toLp] with q hq
  rw [hq,inner_gradient_left]

/-- The random flux source is exactly the derivative action of the actual
semigroup on the initial field. -/
theorem source_eq_semigroup_pairing (u : Point d → Point d) (hu : MemLp u 2 μ) (φ : Test d) :
    source hv hb hl hT ξ ht hbs hB μ u hu φ =
      ∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) (φ : Point d → ℝ)) x (u x) ∂μ := by
  obtain ⟨C,hC⟩ := φ.property.2.exists_bound_of_continuous φ.property.1.continuous
  obtain ⟨L,hL⟩ := (φ.property.2.fderiv ℝ).exists_bound_of_continuous
    (φ.property.1.continuous_fderiv (by simp))
  have hL0 : 0 ≤ L := (norm_nonneg (fderiv ℝ (φ : Point d → ℝ) 0)).trans (hL 0)
  rw [source_apply]
  exact (integral_fderiv_expectation_eq hv hb hl hT ξ ht hbs hB μ
    (φ.property.1.of_le (by simp)) hC (L := NNReal.mk L hL0) hL hu).symm

/-- Actual propagation produces a finite-energy output source. -/
theorem source_finiteEnergy (u : Point d → Point d) (hu : MemLp u 2 μ) :
    FiniteEnergy ((μ.prod ξ).map (endpoint hv hb hl hT (t := t)))
      (source hv hb hl hT ξ ht hbs hB μ u hu) :=
  PropagatedFlux.source_finiteEnergy _ _ _ _

/-- The propagated source energy is bounded by exp(2Kt) times the genuine
initial Euclidean energy, with no dimension-dependent conversion. -/
theorem source_energy_le (u : Point d → Point d) (hu : MemLp u 2 μ) :
    energy ((μ.prod ξ).map (endpoint hv hb hl hT (t := t)))
      (source hv hb hl hT ξ ht hbs hB μ u hu) ≤
      Real.exp ((K:ℝ)*t)^2 * ∫ x, ‖u x‖^2 ∂μ := by
  let V := (velocity_memLp hv hb hl hT ξ ht hbs hB μ hu).toLp (velocity hv hb hl hT (t := t) u)
  have hp := PropagatedFlux.source_energy_le (μ.prod ξ) (endpoint hv hb hl hT (t := t))
    (endpoint_measurable hv hb hl hT ht) V
  have he : (∫ q, ‖V q‖^2 ∂μ.prod ξ) =
      ∫ q, ‖velocity hv hb hl hT (t := t) u q‖^2 ∂μ.prod ξ := by
    apply integral_congr_ae
    filter_upwards [(velocity_memLp hv hb hl hT ξ ht hbs hB μ hu).coeFn_toLp] with q hq
    rw [hq]
  rw [he] at hp
  apply hp.trans
  have hj := boundedFlow_fderiv_apply_energy_le hv hb hl hbs hB hT ht (μ.prod ξ)
    (hu.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ξ)))
  have hf : (∫ q : Point d × C(Icc 0 T,Point d), ‖u q.1‖^2 ∂μ.prod ξ) =
      ∫ x, ‖u x‖^2 ∂μ := by
    simpa only [probReal_univ,one_smul] using
      (integral_fun_fst (μ := μ) (ν := ξ) (fun x => ‖u x‖^2))
  change (∫ q, ‖velocity hv hb hl hT (t := t) u q‖^2 ∂μ.prod ξ) ≤
    Real.exp ((K:ℝ)*t)^2 * (∫ q : Point d × C(Icc 0 T,Point d), ‖u q.1‖^2 ∂μ.prod ξ) at hj
  rwa [hf] at hj

/-- Propagation of the canonical representing tangent of an actual finite-energy
initial distribution. -/
def distribution (σ : Test d →ₗ[ℝ] ℝ) : Test d →ₗ[ℝ] ℝ :=
  source hv hb hl hT ξ ht hbs hB μ
    (representative μ σ : Lp (Point d) 2 μ) (Lp.memLp _)

/-- This action uses the derivative of the proved semigroup expectation and
the genuine Riesz representative of the original distribution. -/
theorem distribution_apply (σ : Test d →ₗ[ℝ] ℝ) (φ : Test d) :
    distribution hv hb hl hT ξ ht hbs hB μ σ φ =
      ∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) (φ : Point d → ℝ)) x
        ((representative μ σ : Lp (Point d) 2 μ) x) ∂μ :=
  source_eq_semigroup_pairing hv hb hl hT ξ ht hbs hB μ _ _ φ

/-- An actual finite-energy initial distribution propagates to a finite-energy
source with the dimension-free exponential energy bound. -/
theorem distribution_finiteEnergy_and_energy_le (σ : Test d →ₗ[ℝ] ℝ)
    (hσ : FiniteEnergy μ σ) :
    FiniteEnergy ((μ.prod ξ).map (endpoint hv hb hl hT (t := t)))
      (distribution hv hb hl hT ξ ht hbs hB μ σ) ∧
    energy ((μ.prod ξ).map (endpoint hv hb hl hT (t := t)))
      (distribution hv hb hl hT ξ ht hbs hB μ σ) ≤ Real.exp ((K:ℝ)*t)^2 * energy μ σ := by
  refine ⟨source_finiteEnergy hv hb hl hT ξ ht hbs hB μ _ _,?_⟩
  rw [energy_eq_integral μ σ hσ]
  exact source_energy_le hv hb hl hT ξ ht hbs hB μ _ _

/-- For paths starting at zero, the constructed propagated distribution has
exactly the original finite-energy source as initial value. -/
theorem distribution_zero (hzero : ∀ᵐ w ∂ξ, w ⟨0,le_rfl,hT⟩ = 0)
    (σ : Test d →ₗ[ℝ] ℝ) (hσ : FiniteEnergy μ σ) :
    distribution hv hb hl hT ξ (t := 0) (left_mem_Icc.2 hT) hbs hB μ σ = σ := by
  ext φ
  rw [distribution_apply,expectation_zero hv hb hl hT ξ hzero]
  rw [representative_divergence μ σ hσ φ]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => inner_gradient_left.symm)

end SharpWasserstein.PropagatedFlux.Flow
