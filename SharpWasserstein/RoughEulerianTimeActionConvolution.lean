module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianTimeActionLaw
public import SharpWasserstein.RoughEulerianSmoothingAction

@[expose] public section

/-! Exact joint Euclidean action contraction for a normalized nonnegative
space-time convolution kernel. The concrete product time/space kernel will
supply the normalization; no action estimate is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace
namespace SharpWasserstein.RoughEulerianTime
open WeightedTangent RoughEulerianSmoothing
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

variable (K : (ℝ × Point d) → ℝ) (hKc : Continuous K) (hKn : ∀ z,0 ≤ K z)
  (hKi : Integrable K (Measure.prod (volume : Measure ℝ) (volume : Measure (Point d)))) (hKone : (∫ z,K z ∂(Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))))=1)

include hKc hKn hKi hKone in
/-- Genuine joint Bochner integrability from translation invariance and
kernel normalization, for scalar or vector input fields. -/
theorem kernel_smul_joint_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : Measure (ℝ × Point d)) [SFinite ρ] {f : (ℝ × Point d) → E} (hf : Integrable f ρ) :
    Integrable (fun p : (ℝ × Point d) × (ℝ × Point d) => K (p.1-p.2) • f p.2) (Measure.prod (Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))) ρ) := by
  have hm : AEStronglyMeasurable (fun p : (ℝ × Point d) × (ℝ × Point d) => K (p.1-p.2) • f p.2) (Measure.prod (Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))) ρ) :=
    ((hKc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).smul
      hf.aestronglyMeasurable.comp_snd
  apply (integrable_prod_iff' hm).mpr
  constructor
  · exact Eventually.of_forall fun y => (hKi.comp_sub_right y).smul_const (f y)
  · have he (y : (ℝ × Point d)) : (∫ x,‖K (x-y) • f y‖ ∂(Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))))=‖f y‖ := by
      simp_rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hKn _)]
      rw [integral_mul_const,integral_sub_right_eq_self,hKone,one_mul]
    simpa only [he] using hf.norm

include hKc hKn hKi hKone in
/-- The actual scalar convolution preserves the integral exactly. -/
theorem integral_kernel_mul (ρ : Measure (ℝ × Point d)) [SFinite ρ] {f : (ℝ × Point d) → ℝ} (hf : Integrable f ρ) :
    (∫ p,∫ z,K (p-z)*f z ∂ρ ∂(Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))))=∫ z,f z ∂ρ := by
  have hi := kernel_smul_joint_integrable K hKc hKn hKi hKone ρ hf
  simp only [smul_eq_mul] at hi
  rw [integral_integral_swap hi]
  simp_rw [integral_mul_const,integral_sub_right_eq_self,hKone,one_mul]

include hKc in
/-- Every translate multiplies an integrable scalar field integrably. -/
theorem kernel_mul_integrable (hKb : ∃ C : ℝ,∀ z,‖K z‖ ≤ C)
    (ρ : Measure (ℝ × Point d)) {f : (ℝ × Point d) → ℝ} (hf : Integrable f ρ) (p : (ℝ × Point d)) :
    Integrable (fun z => K (p-z)*f z) ρ := by
  obtain ⟨C,hC⟩ := hKb
  exact hf.bdd_mul (hKc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun z => hC (p-z))

include hKc hKn in
/-- Pointwise Jensen bound for the actual vector convolution with a positive
stationary floor. The source measure need not be a probability. -/
theorem kernel_floor_action_le (hKb : ∃ C : ℝ,∀ z,‖K z‖ ≤ C)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] {U : (ℝ × Point d) → Point d}
    (hU : Integrable U ρ) (hU₂ : Integrable (fun z => ‖U z‖^2) ρ)
    {a : ℝ} (ha : 0 ≤ a) {g : (ℝ × Point d) → ℝ} (hg : ∀ p,0 < g p) (p : (ℝ × Point d)) :
    floorDensity a (fun q => ∫ z,K (q-z) ∂ρ) g p *
      ‖floorVelocity a (fun q => ∫ z,K (q-z) ∂ρ) g
        (fun q => ∫ z,K (q-z) • U z ∂ρ) p‖^2 ≤
      a*∫ z,K (p-z)*‖U z‖^2 ∂ρ := by
  have hd (q : (ℝ × Point d)) : 0 ≤ ∫ z,K (q-z) ∂ρ := integral_nonneg fun _ => hKn _
  rw [floorVelocity_action ha hd hg]
  have hw : Integrable (fun z => K (p-z)) ρ := by
    simpa only [mul_one] using kernel_mul_integrable K hKc hKb ρ (integrable_const (1:ℝ)) p
  have hh := weighted_norm_integral_sq_le_add (v := U) (hw.const_mul a)
    (by simpa only [mul_assoc] using (kernel_mul_integrable K hKc hKb ρ hU.norm p).const_mul a)
    (by simpa only [mul_assoc] using (kernel_mul_integrable K hKc hKb ρ hU₂ p).const_mul a)
    (Eventually.of_forall fun z => mul_nonneg ha (hKn (p-z))) (hg p)
  simpa only [mul_assoc,mul_smul,integral_smul,integral_const_mul,floorDensity] using hh

include hKc hKn hKi hKone in
/-- The whole space-time action is genuinely integrable and contracts with
constant one, after the exact scaling of the moving density. -/
theorem kernel_floor_action_integrable_and_le (hKb : ∃ C : ℝ,∀ z,‖K z‖ ≤ C)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] {U : (ℝ × Point d) → Point d}
    (hU : Integrable U ρ) (hU₂ : Integrable (fun z => ‖U z‖^2) ρ)
    {a : ℝ} (ha : 0 ≤ a) {g : (ℝ × Point d) → ℝ} (hg : ∀ p,0 < g p) (hgm : AEStronglyMeasurable g (Measure.prod (volume : Measure ℝ) (volume : Measure (Point d)))) :
    let A := fun p => floorDensity a (fun q => ∫ z,K (q-z) ∂ρ) g p *
      ‖floorVelocity a (fun q => ∫ z,K (q-z) ∂ρ) g
        (fun q => ∫ z,K (q-z) • U z ∂ρ) p‖^2
    Integrable A (Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))) ∧ (∫ p,A p ∂(Measure.prod (volume : Measure ℝ) (volume : Measure (Point d)))) ≤ a*∫ z,‖U z‖^2 ∂ρ := by
  let D := fun q => ∫ z,K (q-z) ∂ρ
  let F := fun q => ∫ z,K (q-z) • U z ∂ρ
  let A := fun p => floorDensity a D g p*‖floorVelocity a D g F p‖^2
  have hd (p : (ℝ × Point d)) : 0 ≤ D p := integral_nonneg fun _ => hKn _
  have hdm : AEStronglyMeasurable D (Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))) := by
    have hi := (kernel_smul_joint_integrable K hKc hKn hKi hKone ρ (integrable_const (1:ℝ))).integral_prod_left
    simpa only [smul_eq_mul,mul_one] using hi.aestronglyMeasurable
  have hfm : AEStronglyMeasurable F (Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))) :=
    (kernel_smul_joint_integrable K hKc hKn hKi hKone ρ hU).integral_prod_left.aestronglyMeasurable
  have hdg : AEStronglyMeasurable (floorDensity a D g) (Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))) := (hdm.const_mul a).add hgm
  have hvm : AEStronglyMeasurable (floorVelocity a D g F) (Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))) := hdg.inv₀.smul (hfm.const_smul a)
  have hmajor : Integrable (fun p => a*∫ z,K (p-z)*‖U z‖^2 ∂ρ) (Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))) := by
    simpa only [smul_eq_mul] using
      ((kernel_smul_joint_integrable K hKc hKn hKi hKone ρ hU₂).integral_prod_left).const_mul a
  have hiA : Integrable A (Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))) := by
    apply Integrable.mono' hmajor (hdg.mul (hvm.norm.pow 2))
    exact Eventually.of_forall fun p => by
      change ‖floorDensity a D g p*‖floorVelocity a D g F p‖^2‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (floorDensity_pos ha hd hg p).le (sq_nonneg _))]
      exact kernel_floor_action_le K hKc hKn hKb ρ hU hU₂ ha hg p
  refine ⟨hiA,?_⟩
  calc
    _ ≤ ∫ p,a*∫ z,K (p-z)*‖U z‖^2 ∂ρ ∂(Measure.prod (volume : Measure ℝ) (volume : Measure (Point d))) :=
      integral_mono hiA hmajor (kernel_floor_action_le K hKc hKn hKb ρ hU hU₂ ha hg)
    _ = _ := by rw [integral_const_mul,integral_kernel_mul K hKc hKn hKi hKone ρ hU₂]

end SharpWasserstein.RoughEulerianTime
