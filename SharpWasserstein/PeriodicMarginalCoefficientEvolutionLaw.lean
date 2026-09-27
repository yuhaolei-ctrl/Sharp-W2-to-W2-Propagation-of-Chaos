import SharpWasserstein.PeriodicMarginalCoefficientEvolutionPhysical

/-! The actual carrying-law part of the marginal coefficient equations.
External labels are averaged using the genuine exchangeable full law, so
both Gram and source derivatives use the same actual observed measures. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation PeriodicSourceConvolution
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution
open ExternalInteractionPeriodic ExternalInteractionSymmetry PropagatedSourcePermutation
open WeightedPeriodicFourierScale (PeriodicOf)
variable {d m N : ℕ}
  [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]

/-- Every actual external observation has the same integral as the next
particle, by a genuine prefix-fixing permutation of the carrying law. -/
theorem external_integral_eq (hm : m < N) (μ : Measure (Point (N*d)))
    (hμ : ∀ e : Equiv.Perm (Fin N),μ.map (euclideanPermutation e)=μ)
    (j : Fin N) (hj : m ≤ j.val) {F : Point (m*d+d) → ℝ} (hF : Continuous F) :
    (∫ x,F (observation hm.le j x) ∂μ) =
      ∫ y,F y ∂μ.map (observation hm.le ⟨m,hm⟩) := by
  rw [integral_map (observation hm.le ⟨m,hm⟩).continuous.measurable.aemeasurable
    hF.aestronglyMeasurable]
  have he := observation_test_swap hm j hj F
  change (∫ x,(F ∘ observation hm.le j) x ∂μ) = _
  rw [← he]
  change (∫ x,(F ∘ observation hm.le ⟨m,hm⟩)
    (euclideanPermutation (Equiv.swap ⟨m,hm⟩ j) x) ∂μ) = _
  rw [← integral_map (euclideanPermutation (Equiv.swap ⟨m,hm⟩ j)).continuous.measurable.aemeasurable
    (hF.comp (observation hm.le ⟨m,hm⟩).continuous).aestronglyMeasurable,hμ]
  rfl

/-- Literal finite-N external averaging under the actual observed law. -/
theorem external_integral_meanField (hm : m < N) (μ : Measure (Point (N*d)))
    (hμ : ∀ e : Equiv.Perm (Fin N),μ.map (euclideanPermutation e)=μ)
    {F : Point (m*d+d) → ℝ} (hF : Continuous F) :
    (N:ℝ)⁻¹*(∑ j : Fin N with m ≤ j.val,∫ x,F (observation hm.le j x) ∂μ) =
      (((N:ℝ)-m)/N)*(∫ y,F y ∂μ.map (observation hm.le ⟨m,hm⟩)) := by
  have he : (∑ j : Fin N with m ≤ j.val,∫ x,F (observation hm.le j x) ∂μ) =
      ((N:ℝ)-m)*(∫ y,F y ∂μ.map (observation hm.le ⟨m,hm⟩)) := by
    calc
      _ = ∑ _j ∈ Finset.univ.filter (fun j : Fin N => m ≤ j.val),
          ∫ y,F y ∂μ.map (observation hm.le ⟨m,hm⟩) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact external_integral_eq hm μ hμ j (Finset.mem_filter.mp hj).2 hF
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,external_card hm,Nat.cast_sub hm.le]
  rw [he,div_eq_mul_inv]
  ring

/-- The actual integrated particle generator is the internal marginal
generator plus the exact averaged next-particle interaction. -/
theorem splitGenerator_integral {P : ℝ} (hP : 0 < P) (hm : m < N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N),μ.map (euclideanPermutation e)=μ)
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm)) :
    (∫ x,splitGenerator hm.le b f x ∂μ) =
      (∫ y,internalGenerator N b f y ∂μ.map (marginalProjection hm.le))+
      (((N:ℝ)-m)/N)*(∫ y,ExternalInteraction.interaction b f y
        ∂μ.map (observation hm.le ⟨m,hm⟩)) := by
  have hi := internalGenerator_smooth hb N hf
  obtain ⟨A,_,hA⟩ := (physical_allDerivativesBounded hP hi (internalGenerator_periodic hx hy N hp)).bounded
  have hI : Integrable (cylinder hm.le (internalGenerator N b f)) μ :=
    Integrable.of_bound (cylinder_smooth hm.le hi).continuous.aestronglyMeasurable A
      (Eventually.of_forall fun x => hA (marginalProjection hm.le x))
  have he := ExternalInteraction.interaction_smooth hb hf
  obtain ⟨B,_,hB⟩ := (physical_allDerivativesBounded hP he (interaction_periodic hx hy hp)).bounded
  have hE (j : Fin N) : Integrable (particleInteraction hm.le j b f) μ :=
    Integrable.of_bound (he.continuous.comp (observation hm.le j).continuous).aestronglyMeasurable B
      (Eventually.of_forall fun x => hB (observation hm.le j x))
  change (∫ x,cylinder hm.le (internalGenerator N b f) x+
    (N:ℝ)⁻¹*∑ j : Fin N with m ≤ j.val,particleInteraction hm.le j b f x ∂μ) = _
  rw [integral_add hI ((integrable_finsetSum _ (fun j _ => hE j)).const_mul _),
    integral_const_mul,integral_finsetSum _ (fun j _ => hE j)]
  rw [show (∫ x,cylinder hm.le (internalGenerator N b f) x ∂μ) =
      ∫ y,internalGenerator N b f y ∂μ.map (marginalProjection hm.le) from
    (integral_map (marginalProjection hm.le).continuous.measurable.aemeasurable
      hi.continuous.aestronglyMeasurable).symm]
  congr 1
  exact external_integral_meanField hm μ hμ he.continuous

/-- The true gradient-product test retains the physical coordinate period. -/
theorem gramTest_periodic {n : ℕ} {P : ℝ} {f g : Point n → ℝ}
    (hf : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv n).symm))
    (hg : PeriodicOf P (g ∘ (PeriodicBochner.coordinateEquiv n).symm)) :
    PeriodicOf P (gramTest f g ∘ (PeriodicBochner.coordinateEquiv n).symm) := by
  apply of_euclidean_lattice_periodic
  intro k x
  unfold gramTest
  rw [gradient_lattice_periodic hf,gradient_lattice_periodic hg]

variable {b : Position d → Position d → Position d} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => (particleDrift b : Configuration d N → _))))
  (hb : ∀ _ : ℝ,∀ x : Configuration d N,‖particleDrift b x‖ ≤ M)
  (hl : ∀ _ : ℝ,LipschitzWith K (particleDrift b : Configuration d N → _))
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) (particleDrift b))))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) (particleDrift b) y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) (particleDrift b)))
  {T : ℝ} (hT : 0 ≤ T) (hbs : BoundedSmoothKernel b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
include hv hb hl hbs hμ

/-- The marginal Gram coefficient differentiates into integrals over the
actual m and m+1 observations of the same Brownian carrying law. -/
theorem brownian_marginal_periodic_gramEntry_hasDerivWithinAt
    {P : ℝ} (hP : 0 < P) (hm : m < N) (hex : Exchangeable μ)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    {f g : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm))
    (hpg : PeriodicOf P (g ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t
    HasDerivWithinAt
      (fun s => gramEntry ((Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) s).map
        (marginalProjection hm.le)) f g)
      ((∫ y,internalGenerator N b (gramTest f g) y ∂ν.map (marginalProjection hm.le))+
        (((N:ℝ)-m)/N)*(∫ y,ExternalInteraction.interaction b (gramTest f g) y
          ∂ν.map (observation hm.le ⟨m,hm⟩))) (Icc 0 T) t := by
  have hd := brownian_marginal_gramEntry_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ hm.le
    hf hg (physical_allDerivativesBounded hP hf hpf) (physical_allDerivativesBounded hP hg hpg) ht
  rw [splitGenerator_integral hP hm _
    (fun e => brownian_lawAt_permutation hv' hb' hl' hT _ e (euclideanLaw_permutation μ hex e) t)
    hbs hx hy (gramTest_smooth hf hg) (gramTest_periodic hpf hpg)] at hd
  exact hd

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
