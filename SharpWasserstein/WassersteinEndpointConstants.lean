import SharpWasserstein.PrescribedDecoupledTransport
import SharpWasserstein.RegularizedBrownianSourceBound

/-! Quantifier and horizon adapters for the manuscript's original target.
Level zero is discharged from the actual zero-dimensional transport cost;
all uniform constants retain only the permitted parameter dependence. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace SharpWasserstein.WassersteinEndpoint
open RegularizedBrownianSource

/-- Probability laws on the empty particle configuration have zero transport cost. -/
theorem wassersteinSq_zero_particles {d : ℕ} (μ ν : Measure (Configuration d 0))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : wassersteinSq μ ν = 0 := by
  apply le_antisymm _ bot_le
  apply (wassersteinSq_le_cost (product_isCoupling μ ν)).trans
  simp [transportCost,productCost]

/-- The original positive-level hierarchy supplies the all-level interface;
the missing zero level is a proved zero-cost case. -/
theorem initialHierarchy_allLevels {d N : ℕ} {C₀ : ℝ} (μ : Measure (Position d))
    [IsProbabilityMeasure μ] (P : (N : ℕ) → Measure (Configuration d N))
    [IsProbabilityMeasure (P N)] (hN : 1 ≤ N) (h : InitialHierarchy C₀ μ P) :
    ∀ k,∀ hk : k ≤ N,wassersteinSq (marginal hk (P N)) (tensorLaw μ k) ≤
      ENNReal.ofReal (C₀*(k:ℝ)^2/(N:ℝ)^2) := by
  intro k hk
  by_cases hk0 : k=0
  · subst k
    simp [wassersteinSq_zero_particles]
  · exact h N hN k (Nat.one_le_iff_ne_zero.mpr hk0) hk

theorem sourceHorizonConstant_mono {d : ℕ} {M L₁ C₀ t T : ℝ}
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hC₀ : 0 ≤ C₀) (ht : 0 ≤ t) (htT : t ≤ T) :
    RegularizationRates.sourceHorizonConstant d M C₀ (Real.sqrt (d:ℝ)*L₁) t ≤
      RegularizationRates.sourceHorizonConstant d M C₀ (Real.sqrt (d:ℝ)*L₁) T := by
  have hi := internalSourceConstant_nonneg hM
  unfold RegularizationRates.sourceHorizonConstant RegularizationRates.bridgeHorizonFactor
  gcongr

theorem propagationConstant_mono {d : ℕ} {M L₁ L₂ C₀ t T : ℝ}
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hC₀ : 0 ≤ C₀) (ht : 0 ≤ t) (htT : t ≤ T) :
    propagationConstant d M L₁ L₂ C₀ t ≤ propagationConstant d M L₁ L₂ C₀ T := by
  apply mul_le_mul (sourceHorizonConstant_mono hM hL₁ hC₀ ht htT)
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left htT
      (mul_nonneg (by norm_num) (BrownianPeriodicHierarchy.comparisonConstant_nonneg d M L₁ L₂))
  · exact (Real.exp_pos _).le
  · exact sourceHorizonConstant_nonneg d hM hL₁ hC₀ (ht.trans htT)

/-- The actual geometric endpoint length coefficient is uniform in the horizon. -/
theorem switchLengthCoefficient_mono {d : ℕ} {M L₁ L₂ C₀ t T : ℝ}
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hC₀ : 0 ≤ C₀) (ht : 0 ≤ t) (htT : t ≤ T) :
    Real.sqrt (propagationConstant d M L₁ L₂ C₀ t)*(t+3*Real.sqrt t) ≤
      Real.sqrt (propagationConstant d M L₁ L₂ C₀ T)*(T+3*Real.sqrt T) := by
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (propagationConstant_mono hM hL₁ hC₀ ht htT)
  · gcongr
  · positivity
  · positivity

/-- One explicit endpoint constant for the original uniform-in-time target. -/
def coefficient (d : ℕ) (M L₁ L₂ C₀ T : ℝ) : ℝ :=
  2*(propagationConstant d M L₁ L₂ C₀ T*(T+3*Real.sqrt T)^2+
    PrescribedDecoupledTransport.coefficient d L₁ C₀ T)

theorem coefficient_nonneg (d : ℕ) {M L₁ L₂ C₀ T : ℝ}
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hC₀ : 0 ≤ C₀) (hT : 0 ≤ T) :
    0 ≤ coefficient d M L₁ L₂ C₀ T :=
  mul_nonneg (by norm_num) (add_nonneg
    (mul_nonneg (propagationConstant_nonneg d hM hL₁ hC₀ hT) (sq_nonneg _))
    (PrescribedDecoupledTransport.coefficient_nonneg d hC₀))

/-- Squared actual Wasserstein triangle with a real endpoint-length estimate. -/
theorem transport_triangle_bound {d k : ℕ}
    (μ ν ρ : Measure (Configuration d k))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν) (hρ : HasSecondMoment ρ)
    {S D r : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hleft : Real.sqrt (wassersteinSq μ ν).toReal ≤ S*r)
    (hright : wassersteinSq ν ρ ≤ ENNReal.ofReal (D*r^2)) :
    wassersteinSq μ ρ ≤ ENNReal.ofReal (2*(S^2+D)*r^2) := by
  have ha := ENNReal.toReal_nonneg (a := wassersteinSq μ ν)
  have hb := ENNReal.toReal_nonneg (a := wassersteinSq ν ρ)
  have hc := ENNReal.toReal_nonneg (a := wassersteinSq μ ρ)
  have ht := wassersteinSq_sqrt_triangle μ ν ρ hμ hν hρ
  have hright' : (wassersteinSq ν ρ).toReal ≤ D*r^2 := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hD (sq_nonneg r))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hright
  have hs := Real.sq_sqrt hc
  have hs' := Real.sq_sqrt hb
  have hsum : Real.sqrt (wassersteinSq μ ρ).toReal ≤ S*r+Real.sqrt (wassersteinSq ν ρ).toReal :=
    ht.trans (add_le_add hleft le_rfl)
  have hsumsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hsum
  have hreal : (wassersteinSq μ ρ).toReal ≤ 2*(S^2+D)*r^2 := by
    nlinarith [sq_nonneg (S*r-Real.sqrt (wassersteinSq ν ρ).toReal),
      mul_nonneg (sub_nonneg.mpr hright') (show (0:ℝ) ≤ 2 by norm_num)]
  rw [← ENNReal.ofReal_toReal (wassersteinSq_lt_top μ ρ hμ hρ).ne]
  exact ENNReal.ofReal_le_ofReal hreal

end SharpWasserstein.WassersteinEndpoint
