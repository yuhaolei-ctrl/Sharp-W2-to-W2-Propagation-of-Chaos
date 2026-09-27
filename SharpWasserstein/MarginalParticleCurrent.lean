import SharpWasserstein.Dynamics
import SharpWasserstein.ExchangeableConditionalSource
import SharpWasserstein.InternalSourceProfile
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! Actual marginal particle currents from exchangeability and disintegration.
The full particle drift retains self-interaction. Its tested conditional current
is identified from the genuine law before entropy estimates are applied. -/

noncomputable section
namespace SharpWasserstein
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal BigOperators

/-- Observe the actual retained configuration and an arbitrary full particle. -/
def particleObservation {d m N : ℕ} (hm : m ≤ N) (j : Fin N)
    (x : Configuration d N) : Configuration d m × Position d :=
  (restrictCoordinates hm x, x j)

theorem measurable_particleObservation {d m N : ℕ} (hm : m ≤ N) (j : Fin N) :
    Measurable (particleObservation (d := d) hm j) :=
  (measurable_restrictCoordinates hm).prodMk (measurable_pi_apply j)

/-- The existing disintegrated next-particle joint law is precisely the actual prefix observation. -/
theorem nextParticleJoint_eq_map_observation {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) :
    nextParticleJoint hm P = P.map (particleObservation hm.le ⟨m, hm⟩) := by
  unfold nextParticleJoint marginal
  rw [Measure.map_map (splitLastParticle d m).measurable (measurable_restrictCoordinates _)]
  congr 1
  funext x
  rw [Function.comp_apply, splitLastParticle_apply]
  rfl

/-- Exchangeability identifies every external particle joint law with the genuine next-particle joint law. -/
theorem map_particleObservation_external {d m N : ℕ} (hm : m < N)
    {P : Measure (Configuration d N)} (hex : Exchangeable P) (j : Fin N) (hj : m ≤ j) :
    P.map (particleObservation hm.le j) = nextParticleJoint hm P := by
  let a : Fin N := ⟨m, hm⟩
  let e := Equiv.swap a j
  have he : Measurable (fun x : Configuration d N => fun i => x (e i)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))
  have hfun : particleObservation hm.le a ∘ (fun x : Configuration d N => fun i => x (e i)) =
      particleObservation hm.le j := by
    funext x
    apply Prod.ext
    · funext i
      change x (e (Fin.castLE hm.le i)) = x (Fin.castLE hm.le i)
      have hia : Fin.castLE hm.le i ≠ a := by
        intro hi
        have hv := congrArg Fin.val hi
        change (i : ℕ) = m at hv
        omega
      have hij : Fin.castLE hm.le i ≠ j := by
        intro hi
        have hv := congrArg Fin.val hi
        change (i : ℕ) = (j : ℕ) at hv
        omega
      rw [show e (Fin.castLE hm.le i) = Fin.castLE hm.le i from
        Equiv.swap_apply_of_ne_of_ne hia hij]
    · change x (e a) = x j
      simp only [e, Equiv.swap_apply_left]
  rw [← hfun, ← Measure.map_map (measurable_particleObservation hm.le a) he,
    hex e, nextParticleJoint_eq_map_observation]

/-- A bounded measurable scalar observable is genuinely integrable under a finite law. -/
theorem integrable_bounded_scalar {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [IsFiniteMeasure μ] {f : A → ℝ} {C : ℝ} (hf : Measurable f) (hC : ∀ x, |f x| ≤ C) :
    Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)

/-- Disintegration of an actual external-particle observable. -/
theorem integral_external_particle_eq_conditional {d m N : ℕ} (hm : m < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    (hex : Exchangeable P) (j : Fin N) (hj : m ≤ j)
    {F : Configuration d m → Position d → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (hC : ∀ x y, |F x y| ≤ C) :
    ∫ z, F (restrictCoordinates hm.le z) (z j) ∂P =
      ∫ x, ∫ y, F x y ∂(nextParticleJoint hm P).condKernel x ∂marginal hm.le P := by
  let Q := nextParticleJoint hm P
  have hi : Integrable (Function.uncurry F) Q :=
    integrable_bounded_scalar Q hF (fun p => hC p.1 p.2)
  calc
    _ = ∫ p, F p.1 p.2 ∂P.map (particleObservation hm.le j) :=
      (integral_map (measurable_particleObservation hm.le j).aemeasurable
        hF.aestronglyMeasurable).symm
    _ = ∫ p, F p.1 p.2 ∂Q := by rw [map_particleObservation_external hm hex j hj]
    _ = ∫ p, F p.1 p.2 ∂(Q.fst ⊗ₘ Q.condKernel) := by rw [Q.disintegrate Q.condKernel]
    _ = ∫ x, ∫ y, F x y ∂Q.condKernel x ∂Q.fst :=
      Measure.integral_compProd (by
        rw [Q.disintegrate Q.condKernel]
        convert! hi using 1)
    _ = _ := by rw [nextParticleJoint_fst]

/-- Summing all actual interactions and then disintegrating yields the internal
sum plus the exact number of external particles. -/
theorem integral_particle_sum_eq_conditional {d m N : ℕ} (hm : m < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    (hex : Exchangeable P) {F : Configuration d m → Position d → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (hC : ∀ x y, |F x y| ≤ C) :
    ∫ z, ∑ j : Fin N, F (restrictCoordinates hm.le z) (z j) ∂P =
      ∫ x, (∑ j : Fin m, F x (x j)) +
        ((N : ℝ) - m) * (∫ y, F x y ∂(nextParticleJoint hm P).condKernel x)
        ∂marginal hm.le P := by
  have hFi (j : Fin N) : Integrable (fun z => F (restrictCoordinates hm.le z) (z j)) P :=
    integrable_bounded_scalar P (hF.comp (measurable_particleObservation hm.le j))
      (fun z => hC _ _)
  have hFint (j : Fin m) : Integrable (fun x => F x (x j)) (marginal hm.le P) :=
    integrable_bounded_scalar _ (hF.comp (measurable_id.prodMk (measurable_pi_apply j)))
      (fun x => hC _ _)
  have hFcond : Integrable
      (fun x => ∫ y, F x y ∂(nextParticleJoint hm P).condKernel x) (marginal hm.le P) :=
    integrable_bounded_scalar _ hF.stronglyMeasurable.integral_kernel_prod_right.measurable
      (fun x => integral_bounded_observable_abs_le
        (hF.comp measurable_prodMk_left) (hC x))
  rw [integral_finsetSum _ (fun j _ => hFi j),
    integral_add (integrable_finsetSum _ (fun j _ => hFint j)) (hFcond.const_mul _),
    integral_finsetSum _ (fun j _ => hFint j), integral_const_mul]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hm.le
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    exact (integral_map (measurable_restrictCoordinates hm.le).aemeasurable
      (hF.comp (measurable_id.prodMk (measurable_pi_apply j))).aestronglyMeasurable).symm
  · simp_rw [integral_external_particle_eq_conditional hm hex _
      (show m ≤ (Fin.natAdd m _ : Fin (m + q)).val from Nat.le_add_right _ _) hF hC]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, add_sub_cancel_left]

/-- Scalar coordinates of the genuine conditional drift of the retained particles.
The internal sum includes the self-interaction. -/
def marginalScalarDrift {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (b : Position d → Position d → Position d)
    (i : Fin m) (a : Fin d) (x : Configuration d m) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j : Fin m, b (x i) (x j) a +
    (((N : ℝ) - m) / N) * ∫ y, b (x i) y a ∂(nextParticleJoint hm P).condKernel x

/-- The actual particle drift has exactly the stated conditional marginal current
when paired with every bounded measurable prefix observable. -/
theorem integral_particleDrift_eq_marginalScalarDrift {d m N : ℕ} (hm : m < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    (hex : Exchangeable P) {b : Position d → Position d → Position d}
    {M G : ℝ} (hM : 0 ≤ M) (hb : Measurable (Function.uncurry b))
    (hbound : ∀ u v a, |b u v a| ≤ M)
    {g : Configuration d m → ℝ} (hg : Measurable g) (hgBound : ∀ x, |g x| ≤ G)
    (i : Fin m) (a : Fin d) :
    ∫ z, g (restrictCoordinates hm.le z) * particleDrift b z (Fin.castLE hm.le i) a ∂P =
      ∫ x, g x * marginalScalarDrift hm P b i a x ∂marginal hm.le P := by
  have hF : Measurable (Function.uncurry
      (fun (x : Configuration d m) (y : Position d) => g x * b (x i) y a)) :=
    (hg.comp measurable_fst).mul (show Measurable
      (fun p : Configuration d m × Position d => b (p.1 i) p.2 a) from
      (show Measurable (Function.uncurry (fun u v => b u v a)) from
        (measurable_pi_apply a).comp hb).comp
          (show Measurable (fun p : Configuration d m × Position d => (p.1 i, p.2)) from
            ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd))
  have hFC (x : Configuration d m) (y : Position d) : |g x * b (x i) y a| ≤ G * M := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hbound _ _ _) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (hgBound x) hM)
  calc
    _ = (N : ℝ)⁻¹ * (∫ z, ∑ j : Fin N,
        g (restrictCoordinates hm.le z) * b ((restrictCoordinates hm.le z) i) (z j) a ∂P) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [particleDrift, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, ← Finset.mul_sum,
        restrictCoordinates]
      ring
    _ = (N : ℝ)⁻¹ * (∫ x, (∑ j : Fin m, g x * b (x i) (x j) a) +
        ((N : ℝ) - m) * (∫ y, g x * b (x i) y a ∂(nextParticleJoint hm P).condKernel x)
          ∂marginal hm.le P) := by
      rw [integral_particle_sum_eq_conditional hm hex hF hFC]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Finset.mul_sum, integral_const_mul]
      unfold marginalScalarDrift
      simp only [div_eq_mul_inv]
      ring

/-- The actual marginal drift minus the nonlinear reference drift. -/
def marginalSourceCurrent {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d))
    (b : Position d → Position d → Position d)
    (i : Fin m) (a : Fin d) (x : Configuration d m) : ℝ :=
  marginalScalarDrift hm P b i a x - ∫ y, b (x i) y a ∂r

/-- Exact internal/external decomposition, with no diagonal deletion or conditional-law assumption. -/
theorem marginalSourceCurrent_decomposition {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d))
    (b : Position d → Position d → Position d)
    (i : Fin m) (a : Fin d) (x : Configuration d m) :
    marginalSourceCurrent hm P r b i a x =
      (N : ℝ)⁻¹ * internalScalarCurrent r (fun u v => b u v a) i x +
      (((N : ℝ) - m) / N) *
        ((∫ y, b (x i) y a ∂(nextParticleJoint hm P).condKernel x) - ∫ y, b (x i) y a ∂r) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [marginalSourceCurrent, marginalScalarDrift, internalScalarCurrent,
    centeredKernel, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- Scalar external discrepancy of the actual disintegration against the reference law. -/
def externalScalarDiscrepancy {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) (b : Position d → Position d → Position d)
    (i : Fin m) (a : Fin d) (x : Configuration d m) : ℝ :=
  (∫ y, b (x i) y a ∂(nextParticleJoint hm P).condKernel x) - ∫ y, b (x i) y a ∂r

/-- The energy uses the Euclidean double sum, not the configuration sup norm. -/
def marginalSourceSquare {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) (b : Position d → Position d → Position d)
    (x : Configuration d m) : ℝ :=
  ∑ i : Fin m, ∑ a : Fin d, marginalSourceCurrent hm P r b i a x ^ 2

theorem measurable_externalScalarDiscrepancy {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    {b : Position d → Position d → Position d} (hb : Measurable (Function.uncurry b))
    (i : Fin m) (a : Fin d) : Measurable (externalScalarDiscrepancy hm P r b i a) := by
  have hF : StronglyMeasurable (Function.uncurry
      (fun (x : Configuration d m) (y : Position d) => b (x i) y a)) :=
    ((show Measurable (Function.uncurry (fun u v => b u v a)) from
      (measurable_pi_apply a).comp hb).comp
        (show Measurable (fun p : Configuration d m × Position d => (p.1 i, p.2)) from
          ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  exact hF.integral_kernel_prod_right.measurable.sub hF.integral_prod_right.measurable

theorem measurable_marginalSourceCurrent {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    {b : Position d → Position d → Position d} (hb : Measurable (Function.uncurry b))
    (i : Fin m) (a : Fin d) : Measurable (marginalSourceCurrent hm P r b i a) := by
  simp_rw [show marginalSourceCurrent hm P r b i a = fun x =>
      (N : ℝ)⁻¹ * internalScalarCurrent r (fun u v => b u v a) i x +
      (((N : ℝ) - m) / N) * externalScalarDiscrepancy hm P r b i a x from
      funext (marginalSourceCurrent_decomposition hm P r b i a)]
  exact (measurable_const.mul (measurable_internalScalarCurrent
    (r := r) (b := fun u v => b u v a) ((measurable_pi_apply a).comp hb) i)).add (measurable_const.mul
      (measurable_externalScalarDiscrepancy hm P r hb i a))

theorem marginalSourceSquare_nonneg {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) (b : Position d → Position d → Position d)
    (x : Configuration d m) : 0 ≤ marginalSourceSquare hm P r b x := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Pointwise genuine current bound, with exactly the internal and conditional currents already estimated. -/
theorem marginalSourceSquare_le_parts {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) (b : Position d → Position d → Position d)
    (x : Configuration d m) :
    marginalSourceSquare hm P r b x ≤
      (2 / (N : ℝ) ^ 2) * (∑ i : Fin m, internalCurrentSquare r b i x) +
      (2 * (((N : ℝ) - m) / N) ^ 2) *
        (∑ a : Fin d, ∑ i : Fin m, externalScalarDiscrepancy hm P r b i a x ^ 2) := by
  calc
    _ ≤ ∑ i : Fin m, ∑ a : Fin d,
        ((2 / (N : ℝ) ^ 2) * internalScalarCurrent r (fun u v => b u v a) i x ^ 2 +
        (2 * (((N : ℝ) - m) / N) ^ 2) * externalScalarDiscrepancy hm P r b i a x ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro a _
      rw [marginalSourceCurrent_decomposition]
      change ((N : ℝ)⁻¹ * internalScalarCurrent r (fun u v => b u v a) i x +
        (((N : ℝ) - m) / N) * externalScalarDiscrepancy hm P r b i a x) ^ 2 ≤ _
      have h := sq_nonneg ((N : ℝ)⁻¹ * internalScalarCurrent r (fun u v => b u v a) i x -
        (((N : ℝ) - m) / N) * externalScalarDiscrepancy hm P r b i a x)
      simp only [div_eq_mul_inv, ← inv_pow] at *
      nlinarith
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, internalCurrentSquare]
      congr 1
      rw [Finset.sum_comm]

/-- The actual marginal source is square-integrable and has the quadratic particle
profile. Both terms come from the full law's KL and marginal entropy bounds. -/
theorem marginalSourceSquare_integrable_and_le_profile {d m N : ℕ} {H M : ℝ}
    (hm0 : 0 < m) (hm : m < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    {b : Position d → Position d → Position d}
    (hex : Exchangeable P) (hfinite : klDiv P (tensorLaw r N) ≠ ∞)
    (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ u v a, |b u v a| ≤ M)
    (hprofile : ∀ j, j ≤ N → marginalEntropy P r j ≤ H * (j : ℝ) ^ 2 / (N : ℝ) ^ 2) :
    Integrable (marginalSourceSquare hm P r b) (marginal hm.le P) ∧
    (∫ x, marginalSourceSquare hm P r b x ∂marginal hm.le P) ≤
      (2 * (d * internalSourceConstant M) * (1 + H) + 16 * d * M ^ 2 * H) *
        (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  let μ := marginal hm.le P
  let A := fun x : Configuration d m => ∑ i : Fin m, internalCurrentSquare r b i x
  let B := fun x : Configuration d m =>
    ∑ a : Fin d, ∑ i : Fin m, externalScalarDiscrepancy hm P r b i a x ^ 2
  let α := ((N : ℝ) - m) / N
  have hF (i : Fin m) (a : Fin d) : StronglyMeasurable (Function.uncurry
      (fun (x : Configuration d m) (y : Position d) => b (x i) y a)) :=
    ((show Measurable (Function.uncurry (fun u v => b u v a)) from
      (measurable_pi_apply a).comp hb).comp
        (show Measurable (fun p : Configuration d m × Position d => (p.1 i, p.2)) from
          ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  have hFb (i : Fin m) (a : Fin d) :
      ∀ᵐ x ∂μ, ∀ᵐ y ∂r, ‖b (x i) y a‖ ≤ M :=
    Eventually.of_forall fun x => Eventually.of_forall fun y =>
      by simpa only [Real.norm_eq_abs] using hbound (x i) y a
  have hext (a : Fin d) (i : Fin m) :
      Integrable (fun x => externalScalarDiscrepancy hm P r b i a x ^ 2) μ := by
    have h := integrable_conditional_discrepancy_sq hm hfinite hM (hF i a) (hFb i a)
    simpa only [Real.norm_eq_abs, sq_abs, externalScalarDiscrepancy] using h
  have hAi : Integrable A μ := integrable_finsetSum _ (fun i _ =>
    integrable_internalCurrentSquare hb hbound i μ)
  have hBi : Integrable B μ := integrable_finsetSum _ (fun a _ =>
    integrable_finsetSum _ (fun i _ => hext a i))
  have hright : Integrable (fun x => (2 / (N : ℝ) ^ 2) * A x + (2 * α ^ 2) * B x) μ :=
    (hAi.const_mul _).add (hBi.const_mul _)
  have hmeas : Measurable (marginalSourceSquare hm P r b) := by
    exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun a _ => (measurable_marginalSourceCurrent hm P r hb i a).pow_const 2))
  have hcur : Integrable (marginalSourceSquare hm P r b) μ :=
    hright.mono_nonneg hmeas.aestronglyMeasurable
      (Eventually.of_forall (marginalSourceSquare_nonneg hm P r b))
      (Eventually.of_forall (marginalSourceSquare_le_parts hm P r b))
  refine ⟨hcur, ?_⟩
  have hmono := integral_mono_ae hcur hright
    (Eventually.of_forall (marginalSourceSquare_le_parts hm P r b))
  rw [integral_add (hAi.const_mul _) (hBi.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  have hInt : (∫ x, A x ∂μ) / (N : ℝ) ^ 2 ≤
      (d * internalSourceConstant M) * (1 + H) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 :=
    internal_source_marginal_energy_le_profile (by omega) hm.le hH hM hb hbound hfinite hprofile
  have hExt : α ^ 2 * (∫ x, B x ∂μ) ≤
      8 * d * M ^ 2 * H * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
    change α ^ 2 * (∫ x, ∑ a : Fin d, ∑ i : Fin m,
      externalScalarDiscrepancy hm P r b i a x ^ 2 ∂μ) ≤ _
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun i _ => hext a i)),
      Finset.mul_sum]
    calc
      _ ≤ ∑ _a : Fin d, 8 * M ^ 2 * H * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        have h := exchangeable_conditional_source_quadratic_bound hm0 hm hex hfinite
          hH hM hprofile (fun i => hF i a) (fun i => hFb i a)
        simpa only [Real.norm_eq_abs, sq_abs, externalScalarDiscrepancy] using h
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  calc
    _ ≤ (2 / (N : ℝ) ^ 2) * (∫ x, A x ∂μ) + (2 * α ^ 2) * (∫ x, B x ∂μ) := hmono
    _ = 2 * ((∫ x, A x ∂μ) / (N : ℝ) ^ 2) + 2 * (α ^ 2 * (∫ x, B x ∂μ)) := by ring
    _ ≤ 2 * ((d * internalSourceConstant M) * (1 + H) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2) +
        2 * (8 * d * M ^ 2 * H * (m : ℝ) ^ 2 / (N : ℝ) ^ 2) := by gcongr
    _ = _ := by ring

/-- Coordinate evaluation commutes with the actual reference drift integral. -/
theorem nonlinearDrift_coordinate {d : ℕ}
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    {b : Position d → Position d → Position d} {M : ℝ}
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ u v a, |b u v a| ≤ M)
    (x : Position d) (a : Fin d) :
    nonlinearDrift b r x a = ∫ y, b x y a ∂r := by
  exact eval_integral (fun c => integrable_bounded_scalar r
    (((measurable_pi_apply c).comp hb).comp measurable_prodMk_left) (fun y => hbound x y c)) a

/-- At the full-particle endpoint the source is exactly the internal current,
including the diagonal. There is no unused next-particle conditional law. -/
theorem fullSourceCurrent_eq_internal {d N : ℕ} (hN : 0 < N)
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    {b : Position d → Position d → Position d} {M : ℝ}
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ u v a, |b u v a| ≤ M)
    (x : Configuration d N) (i : Fin N) (a : Fin d) :
    particleDrift b x i a - nonlinearDrift b r (x i) a =
      (N : ℝ)⁻¹ * internalScalarCurrent r (fun u v => b u v a) i x := by
  have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [nonlinearDrift_coordinate r hb hbound]
  simp only [particleDrift, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    internalScalarCurrent, centeredKernel, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The exact full-endpoint source has the same internal quadratic profile. -/
theorem fullSourceSquare_le_profile {d N : ℕ} {H M : ℝ} (hN : 0 < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    {b : Position d → Position d → Position d}
    (hfinite : klDiv P (tensorLaw r N) ≠ ∞) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ u v a, |b u v a| ≤ M)
    (hprofile : ∀ j, j ≤ N → marginalEntropy P r j ≤ H * (j : ℝ) ^ 2 / (N : ℝ) ^ 2) :
    ∫ x, ∑ i : Fin N, ∑ a : Fin d,
      (particleDrift b x i a - nonlinearDrift b r (x i) a) ^ 2 ∂P ≤
        (d * internalSourceConstant M) * (1 + H) := by
  have he (x : Configuration d N) :
      (∑ i : Fin N, ∑ a : Fin d,
        (particleDrift b x i a - nonlinearDrift b r (x i) a) ^ 2) =
      ((N : ℝ) ^ 2)⁻¹ * ∑ i : Fin N, internalCurrentSquare r b i x := by
    simp_rw [fullSourceCurrent_eq_internal hN r hb hbound, mul_pow]
    simp only [← Finset.mul_sum, internalCurrentSquare, inv_pow]
  simp_rw [he]
  rw [integral_const_mul]
  have h := internal_source_marginal_energy_le_profile hN le_rfl hH hM hb hbound hfinite hprofile
  have hmarg : marginal (d := d) (le_refl N) P = P := marginal_self P
  rw [hmarg] at h
  have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp at h ⊢
  nlinarith

end SharpWasserstein
