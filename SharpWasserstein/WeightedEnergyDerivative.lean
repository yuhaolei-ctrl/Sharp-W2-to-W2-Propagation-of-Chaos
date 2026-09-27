import SharpWasserstein.WeightedTangent
import SharpWasserstein.WeightedDensity
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Differentiation of variational tangents through the actual inverse of a
coercive weighted operator. Optimizer differentiability is proved from
operator/source differentiability rather than included as a hypothesis. -/

noncomputable section
namespace SharpWasserstein.WeightedEnergyDerivative

open scoped InnerProductSpace Topology

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Solve the variational operator equation by its genuine bounded-operator inverse. -/
def inverseSolution (A : ℝ → H →L[ℝ] H) (f : ℝ → H) (t : ℝ) : H :=
  Ring.inverse (A t) (f t)

/-- The optimizer is differentiable because inversion and evaluation are differentiable. -/
theorem hasDerivAt_inverseSolution {A : ℝ → H →L[ℝ] H} {A' : H →L[ℝ] H}
    {f : ℝ → H} {f' : H} {t : ℝ} (hA : HasDerivAt A A' t) (hf : HasDerivAt f f' t)
    (a : (H →L[ℝ] H)ˣ) (ha : A t = a) :
    HasDerivAt (inverseSolution A f)
      ((↑a⁻¹ : H →L[ℝ] H) (f' - A' (inverseSolution A f t))) t := by
  have hi : HasFDerivAt (@Ring.inverse (H →L[ℝ] H) _)
      (-ContinuousLinearMap.mulLeftRight ℝ (H →L[ℝ] H) (↑a⁻¹) (↑a⁻¹)) (A t) := by
    rw [ha]
    exact hasFDerivAt_ringInverse a
  have hd := (hi.comp_hasDerivAt t hA).clm_apply hf
  convert hd using 1
  · rfl
  · simp [inverseSolution, ha, sub_eq_add_neg, add_comm,
      ContinuousLinearMap.mulLeftRight_apply]

omit [CompleteSpace H] in
/-- The resulting derivative satisfies the differentiated variational equation. -/
theorem inverseSolution_derivative_equation {A : ℝ → H →L[ℝ] H} {A' : H →L[ℝ] H}
    {f : ℝ → H} {f' : H} {t : ℝ} (a : (H →L[ℝ] H)ˣ) (ha : A t = a) :
    A t ((↑a⁻¹ : H →L[ℝ] H) (f' - A' (inverseSolution A f t))) =
      f' - A' (inverseSolution A f t) := by
  rw [ha, ← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]

omit [CompleteSpace H] in
/-- Invertibility gives the original variational equation exactly. -/
theorem inverseSolution_equation {A : ℝ → H →L[ℝ] H} {f : ℝ → H} {t : ℝ}
    (a : (H →L[ℝ] H)ˣ) (ha : A t = a) : A t (inverseSolution A f t) = f t := by
  simp [inverseSolution, ha, ← mul_apply_eq_comp]

/-- Differentiating the optimized energy cancels the derivative of the optimizer. -/
theorem hasDerivAt_optimizedEnergy {A : ℝ → H →L[ℝ] H} {A' : H →L[ℝ] H}
    {f : ℝ → H} {f' : H} {t : ℝ} (hA : HasDerivAt A A' t) (hf : HasDerivAt f f' t)
    (a : (H →L[ℝ] H)ˣ) (ha : A t = a)
    (hsymm : ∀ v w : H, ⟪A t v, w⟫_ℝ = ⟪v, A t w⟫_ℝ) :
    HasDerivAt (fun s => ⟪f s, inverseSolution A f s⟫_ℝ)
      (2 * ⟪f', inverseSolution A f t⟫_ℝ -
        ⟪A' (inverseSolution A f t), inverseSolution A f t⟫_ℝ) t := by
  have hu := hasDerivAt_inverseSolution hA hf a ha
  have he := hf.inner ℝ hu
  convert! he using 1
  let u := inverseSolution A f t
  let u' := (↑a⁻¹ : H →L[ℝ] H) (f' - A' u)
  have hAu : A t u = f t := inverseSolution_equation a ha
  have hAu' : A t u' = f' - A' u := inverseSolution_derivative_equation a ha
  have hp : ⟪f t, u'⟫_ℝ = ⟪f', u⟫_ℝ - ⟪A' u, u⟫_ℝ := by
    rw [← hAu, hsymm, hAu', inner_sub_right, real_inner_comm u f', real_inner_comm u (A' u)]
  change 2 * ⟪f', u⟫_ℝ - ⟪A' u, u⟫_ℝ = ⟪f t, u'⟫_ℝ + ⟪f', u⟫_ℝ
  rw [hp]
  ring

/-- The actual quadratic operator objective used before taking the compact-test supremum. -/
def operatorObjective (A : H →L[ℝ] H) (f v : H) : ℝ :=
  2 * ⟪f, v⟫_ℝ - ⟪A v, v⟫_ℝ

omit [CompleteSpace H] in
/-- Completion of the weighted square uses the operator equation and symmetry. -/
theorem operatorObjective_complete_square (A : H →L[ℝ] H) (f u : H)
    (hAu : A u = f) (hsymm : ∀ v w : H, ⟪A v, w⟫_ℝ = ⟪v, A w⟫_ℝ) (v : H) :
    operatorObjective A f v = ⟪f, u⟫_ℝ - ⟪A (v - u), v - u⟫_ℝ := by
  unfold operatorObjective
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    hAu, hsymm v u, hAu, real_inner_comm f v]
  ring

omit [CompleteSpace H] in
/-- Density of actual test gradients preserves the exact weighted variational value. -/
theorem dense_variational_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : V →ₗ[ℝ] H) (hdense : DenseRange e) (A : H →L[ℝ] H) (f u : H)
    (hAu : A u = f) (hsymm : ∀ v w : H, ⟪A v, w⟫_ℝ = ⟪v, A w⟫_ℝ)
    (hpos : ∀ v, 0 ≤ ⟪A v, v⟫_ℝ) :
    sSup (Set.range (fun φ => operatorObjective A f (e φ))) = ⟪f, u⟫_ℝ := by
  apply IsLUB.csSup_eq _ (Set.range_nonempty _)
  constructor
  · rintro y ⟨φ, rfl⟩
    change operatorObjective A f (e φ) ≤ _
    rw [operatorObjective_complete_square A f u hAu hsymm]
    exact sub_le_self _ (hpos _)
  · intro C hC
    have hb (v : H) : operatorObjective A f v ≤ C := by
      refine hdense.induction_on v (isClosed_le (by
        unfold operatorObjective
        fun_prop) continuous_const) ?_
      intro φ
      exact hC ⟨φ, rfl⟩
    have h := hb u
    simp only [operatorObjective, hAu] at h
    linarith

end Hilbert
open MeasureTheory WeightedTangent WeightedDensity
open scoped BoundedContinuousFunction

variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]
variable (μ : Measure (Point d)) [IsFiniteMeasure μ]

/-- The actual density-dependent tangent vector in the fixed reference gradient closure. -/
def densitySolution (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ) : gradientClosure μ :=
  Ring.inverse (weightedOperator μ ρ) (TangentEnergy.rieszRepresentative ℓ)

/-- The original compact-test objective with an actual density-weighted energy integral. -/
def densityTestObjective (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ) (φ : Test d) : ℝ :=
  2 * ℓ (gradientIntoClosure μ φ) - ∫ x, ρ x * ‖gradient (φ : Point d → ℝ) x‖ ^ 2 ∂μ

/-- The genuine variational energy over compact smooth tests for the changing density. -/
def densityEnergy (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ) : ℝ :=
  sSup (Set.range (densityTestObjective μ ρ ℓ))

/-- The weighted operator objective is exactly the actual compact-test integral objective. -/
theorem densityTestObjective_eq_operator (ρ : Point d →ᵇ ℝ)
    (ℓ : gradientClosure μ →L[ℝ] ℝ) (φ : Test d) :
    densityTestObjective μ ρ ℓ φ = operatorObjective (weightedOperator μ ρ)
      (TangentEnergy.rieszRepresentative ℓ) (gradientIntoClosure μ φ) := by
  unfold densityTestObjective operatorObjective
  rw [TangentEnergy.inner_rieszRepresentative, weightedOperator_inner]
  congr 1
  apply integral_congr_ae
  filter_upwards [testGradient_ae μ φ] with x hx
  change ρ x * ‖gradient (φ : Point d → ℝ) x‖ ^ 2 =
    ρ x * ⟪testGradient μ φ x, testGradient μ φ x⟫_ℝ
  rw [hx, real_inner_self_eq_norm_sq]

/-- Positive bounded density gives the variational equation for the constructed optimizer. -/
theorem densitySolution_equation (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hρ : ∀ᵐ x ∂μ, a ≤ ρ x) :
    weightedOperator μ ρ (densitySolution μ ρ ℓ) = TangentEnergy.rieszRepresentative ℓ := by
  obtain ⟨u, hu⟩ := weightedOperator_isUnit μ ρ ha hρ
  simp [densitySolution, ← hu, ← mul_apply_eq_comp]

/-- The constructed optimizer represents the source by the actual density-weighted divergence pairing. -/
theorem densitySolution_divergence (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hρ : ∀ᵐ x ∂μ, a ≤ ρ x) (φ : Test d) :
    ℓ (gradientIntoClosure μ φ) = ∫ x, ρ x * ⟪gradient (φ : Point d → ℝ) x,
      (densitySolution μ ρ ℓ : Lp (Point d) 2 μ) x⟫_ℝ ∂μ := by
  rw [← TangentEnergy.inner_rieszRepresentative, ← densitySolution_equation μ ρ ℓ ha hρ,
    weightedOperator_inner]
  apply integral_congr_ae
  filter_upwards [testGradient_ae μ φ] with x hx
  change ρ x * ⟪(densitySolution μ ρ ℓ : Lp (Point d) 2 μ) x, testGradient μ φ x⟫_ℝ = _
  rw [hx, real_inner_comm]

/-- The exact compact-test supremum equals the optimized source pairing. -/
theorem densityEnergy_eq_solution (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hρ : ∀ᵐ x ∂μ, a ≤ ρ x) :
    densityEnergy μ ρ ℓ = ℓ (densitySolution μ ρ ℓ) := by
  unfold densityEnergy
  rw [funext (densityTestObjective_eq_operator μ ρ ℓ)]
  rw [dense_variational_eq (gradientIntoClosure μ) (dense_gradientIntoClosure μ)
    (weightedOperator μ ρ) (TangentEnergy.rieszRepresentative ℓ) (densitySolution μ ρ ℓ)
    (densitySolution_equation μ ρ ℓ ha hρ) (weightedOperator_symmetric μ ρ)
    (weightedOperator_nonneg μ ρ ha hρ), TangentEnergy.inner_rieszRepresentative]

/-- The optimized energy is the actual density-weighted integral of the squared tangent norm. -/
theorem densityEnergy_eq_integral (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hρ : ∀ᵐ x ∂μ, a ≤ ρ x) :
    densityEnergy μ ρ ℓ = ∫ x, ρ x * ‖(densitySolution μ ρ ℓ : Lp (Point d) 2 μ) x‖ ^ 2 ∂μ := by
  rw [densityEnergy_eq_solution μ ρ ℓ ha hρ, ← TangentEnergy.inner_rieszRepresentative,
    ← densitySolution_equation μ ρ ℓ ha hρ, weightedOperator_inner]
  simp_rw [real_inner_self_eq_norm_sq]

/-- The distribution on actual compact smooth tests induced by the source functional. -/
def densityDistribution (ℓ : gradientClosure μ →L[ℝ] ℝ) : Test d →ₗ[ℝ] ℝ :=
  ℓ.toLinearMap.comp (gradientIntoClosure μ)

omit [IsFiniteMeasure μ] in
/-- The weighted integral is integration against the genuine changed measure. -/
theorem integral_density_eq_withDensity (ρ : Point d →ᵇ ℝ)
    (hρ : ∀ᵐ x ∂μ, 0 ≤ ρ x) (g : Point d → ℝ) :
    (∫ x, ρ x * g x ∂μ) = ∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (ρ x)) := by
  rw [integral_withDensity_eq_integral_toReal_smul
    (ρ.continuous.measurable.ennreal_ofReal) (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hρ] with x hx
  simp [ENNReal.toReal_ofReal hx]

/-- The optimized compact-test supremum is precisely the existing weighted negative-Sobolev energy
for the actual measure with density, not a new abstract proxy for that energy. -/
theorem densityEnergy_eq_weightedTangent (ρ : Point d →ᵇ ℝ)
    (ℓ : gradientClosure μ →L[ℝ] ℝ) (hρ : ∀ᵐ x ∂μ, 0 ≤ ρ x) :
    densityEnergy μ ρ ℓ = WeightedTangent.energy
      (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) (densityDistribution μ ℓ) := by
  unfold densityEnergy WeightedTangent.energy
  congr 2
  funext φ
  unfold densityTestObjective WeightedTangent.testObjective
  rw [integral_density_eq_withDensity μ ρ hρ]
  rfl

/-- The source-to-Riesz map is an actual continuous linear isometry, so source differentiation transfers. -/
def rieszMap : (gradientClosure μ →L[ℝ] ℝ) →L[ℝ] gradientClosure μ :=
  (InnerProductSpace.toDual ℝ (gradientClosure μ)).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rieszMap_apply (ℓ : gradientClosure μ →L[ℝ] ℝ) :
    rieszMap μ ℓ = TangentEnergy.rieszRepresentative ℓ := rfl

omit [BorelSpace (Point d)] [IsFiniteMeasure μ] in
/-- The positive lower bound persists on a full time neighborhood. -/
theorem eventually_density_positive {ρ : ℝ → (Point d →ᵇ ℝ)} {t a : ℝ}
    (hρ : ContinuousAt ρ t) (ha : 0 < a) (hp : ∀ᵐ x ∂μ, a ≤ ρ t x) :
    ∀ᶠ s in 𝓝 t, ∀ᵐ x ∂μ, a / 2 ≤ ρ s x := by
  have hn : Filter.Tendsto (fun s => ‖ρ s - ρ t‖) (𝓝 t) (𝓝 0) := by
    simpa using (hρ.tendsto.sub (tendsto_const_nhds (x := ρ t))).norm
  filter_upwards [hn.eventually (gt_mem_nhds (half_pos ha))] with s hs
  filter_upwards [hp] with x hx
  have hb := (ρ s - ρ t).norm_coe_le_norm x
  simp only [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs] at hb
  have hl := (abs_le.mp (hb.trans hs.le)).1
  linarith

/-- The actual optimizer varies continuously with the density and source, with no optimizer regularity assumption. -/
theorem continuousAt_densitySolution
    {ρ : ℝ → (Point d →ᵇ ℝ)} {ℓ : ℝ → (gradientClosure μ →L[ℝ] ℝ)} {t a : ℝ}
    (hρ : ContinuousAt ρ t) (hℓ : ContinuousAt ℓ t)
    (ha : 0 < a) (hp : ∀ᵐ x ∂μ, a ≤ ρ t x) :
    ContinuousAt (fun s => densitySolution μ (ρ s) (ℓ s)) t := by
  have hA : ContinuousAt (fun s => weightedOperator μ (ρ s)) t :=
    (weightedOperator μ).continuous.continuousAt.comp hρ
  have hf : ContinuousAt (fun s => TangentEnergy.rieszRepresentative (ℓ s)) t :=
    (rieszMap μ).continuous.continuousAt.comp hℓ
  have hi : ContinuousAt (Ring.inverse : (gradientClosure μ →L[ℝ] gradientClosure μ) →
      (gradientClosure μ →L[ℝ] gradientClosure μ)) (weightedOperator μ (ρ t)) :=
    (differentiableAt_inverse (𝕜 := ℝ)
      (R := gradientClosure μ →L[ℝ] gradientClosure μ)
      (weightedOperator_isUnit μ (ρ t) ha hp)).continuousAt
  exact (hi.comp (f := fun s => weightedOperator μ (ρ s)) (x := t) hA).clm_apply hf

/-- Differentiating the actual optimizer gives the inverse applied to the differentiated
source minus the density variation acting on the current optimizer. -/
theorem hasDerivAt_densitySolution
    {ρ : ℝ → (Point d →ᵇ ℝ)} {ρ' : Point d →ᵇ ℝ}
    {ℓ : ℝ → (gradientClosure μ →L[ℝ] ℝ)} {ℓ' : gradientClosure μ →L[ℝ] ℝ} {t a : ℝ}
    (hρ : HasDerivAt ρ ρ' t) (hℓ : HasDerivAt ℓ ℓ' t)
    (ha : 0 < a) (hp : ∀ᵐ x ∂μ, a ≤ ρ t x) :
    HasDerivAt (fun s => densitySolution μ (ρ s) (ℓ s))
      (Ring.inverse (weightedOperator μ (ρ t))
        (TangentEnergy.rieszRepresentative ℓ' -
          weightedOperator μ ρ' (densitySolution μ (ρ t) (ℓ t)))) t := by
  obtain ⟨u, hu⟩ := weightedOperator_isUnit μ (ρ t) ha hp
  have hA : HasDerivAt (fun s => weightedOperator μ (ρ s)) (weightedOperator μ ρ') t := by
    exact HasFDerivAt.comp_hasDerivAt (F := Point d →ᵇ ℝ)
      (E := gradientClosure μ →L[ℝ] gradientClosure μ) t (weightedOperator μ).hasFDerivAt hρ
  have hf : HasDerivAt (fun s => TangentEnergy.rieszRepresentative (ℓ s))
      (TangentEnergy.rieszRepresentative ℓ') t := by
    exact HasFDerivAt.comp_hasDerivAt (F := gradientClosure μ →L[ℝ] ℝ)
      (E := gradientClosure μ) t (rieszMap μ).hasFDerivAt hℓ
  convert! hasDerivAt_inverseSolution hA hf u hu.symm using 1
  simp only [← hu, Ring.inverse_unit]
  rfl

/-- The actual density-dependent optimizer is differentiable, derived from density/source inputs. -/
theorem differentiableAt_densitySolution
    {ρ : ℝ → (Point d →ᵇ ℝ)} {ρ' : Point d →ᵇ ℝ}
    {ℓ : ℝ → (gradientClosure μ →L[ℝ] ℝ)} {ℓ' : gradientClosure μ →L[ℝ] ℝ} {t a : ℝ}
    (hρ : HasDerivAt ρ ρ' t) (hℓ : HasDerivAt ℓ ℓ' t)
    (ha : 0 < a) (hp : ∀ᵐ x ∂μ, a ≤ ρ t x) :
    DifferentiableAt ℝ (fun s => densitySolution μ (ρ s) (ℓ s)) t := by
  exact (hasDerivAt_densitySolution μ hρ hℓ ha hp).differentiableAt

/-- The weighted variational energy derivative, with the actual density derivative integral.
The hypothesis is differentiability of the input density in supremum norm and source in dual norm;
no differentiability of the optimizer is assumed. -/
theorem hasDerivAt_densityEnergy
    {ρ : ℝ → (Point d →ᵇ ℝ)} {ρ' : Point d →ᵇ ℝ}
    {ℓ : ℝ → (gradientClosure μ →L[ℝ] ℝ)} {ℓ' : gradientClosure μ →L[ℝ] ℝ} {t a : ℝ}
    (hρ : HasDerivAt ρ ρ' t) (hℓ : HasDerivAt ℓ ℓ' t)
    (ha : 0 < a) (hp : ∀ᵐ x ∂μ, a ≤ ρ t x) :
    HasDerivAt (fun s => densityEnergy μ (ρ s) (ℓ s))
      (2 * ℓ' (densitySolution μ (ρ t) (ℓ t)) -
        ∫ x, ρ' x * ‖(densitySolution μ (ρ t) (ℓ t) : Lp (Point d) 2 μ) x‖ ^ 2 ∂μ) t := by
  obtain ⟨u, hu⟩ := weightedOperator_isUnit μ (ρ t) ha hp
  have hA : HasDerivAt (fun s => weightedOperator μ (ρ s)) (weightedOperator μ ρ') t := by
    exact HasFDerivAt.comp_hasDerivAt (F := Point d →ᵇ ℝ)
      (E := gradientClosure μ →L[ℝ] gradientClosure μ) t (weightedOperator μ).hasFDerivAt hρ
  have hf : HasDerivAt (fun s => TangentEnergy.rieszRepresentative (ℓ s))
      (TangentEnergy.rieszRepresentative ℓ') t := by
    exact HasFDerivAt.comp_hasDerivAt (F := gradientClosure μ →L[ℝ] ℝ)
      (E := gradientClosure μ) t (rieszMap μ).hasFDerivAt hℓ
  have he := hasDerivAt_optimizedEnergy hA hf u hu.symm (weightedOperator_symmetric μ (ρ t))
  have he' : HasDerivAt (fun s => ℓ s (densitySolution μ (ρ s) (ℓ s)))
      (2 * ℓ' (densitySolution μ (ρ t) (ℓ t)) -
        ∫ x, ρ' x * ‖(densitySolution μ (ρ t) (ℓ t) : Lp (Point d) 2 μ) x‖ ^ 2 ∂μ) t := by
    convert! he using 1
    · funext s
      exact (TangentEnergy.inner_rieszRepresentative (ℓ s) _).symm
    · change 2 * ℓ' _ - _ = 2 * ⟪TangentEnergy.rieszRepresentative ℓ', densitySolution μ (ρ t) (ℓ t)⟫_ℝ -
        ⟪weightedOperator μ ρ' (densitySolution μ (ρ t) (ℓ t)), densitySolution μ (ρ t) (ℓ t)⟫_ℝ
      rw [TangentEnergy.inner_rieszRepresentative, weightedOperator_inner]
      simp_rw [real_inner_self_eq_norm_sq]
  apply he'.congr_of_eventuallyEq
  filter_upwards [eventually_density_positive μ hρ.continuousAt ha hp] with s hs
  exact densityEnergy_eq_solution μ (ρ s) (ℓ s) (half_pos ha) hs

/-- The same derivative for the original weighted tangent energy at the actual varying measure. -/
theorem hasDerivAt_weightedTangentEnergy
    {ρ : ℝ → (Point d →ᵇ ℝ)} {ρ' : Point d →ᵇ ℝ}
    {ℓ : ℝ → (gradientClosure μ →L[ℝ] ℝ)} {ℓ' : gradientClosure μ →L[ℝ] ℝ} {t a : ℝ}
    (hρ : HasDerivAt ρ ρ' t) (hℓ : HasDerivAt ℓ ℓ' t)
    (ha : 0 < a) (hp : ∀ᵐ x ∂μ, a ≤ ρ t x) :
    HasDerivAt (fun s => WeightedTangent.energy
      (μ.withDensity (fun x => ENNReal.ofReal (ρ s x))) (densityDistribution μ (ℓ s)))
      (2 * ℓ' (densitySolution μ (ρ t) (ℓ t)) -
        ∫ x, ρ' x * ‖(densitySolution μ (ρ t) (ℓ t) : Lp (Point d) 2 μ) x‖ ^ 2 ∂μ) t := by
  apply (hasDerivAt_densityEnergy μ hρ hℓ ha hp).congr_of_eventuallyEq
  filter_upwards [eventually_density_positive μ hρ.continuousAt ha hp] with s hs
  exact (densityEnergy_eq_weightedTangent μ (ρ s) (ℓ s)
    (hs.mono fun x hx => (half_pos ha).le.trans hx)).symm

end SharpWasserstein.WeightedEnergyDerivative
