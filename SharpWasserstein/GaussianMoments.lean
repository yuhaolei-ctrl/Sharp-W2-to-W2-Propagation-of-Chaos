import SharpWasserstein.GaussianCovariance

/-! Exact means and covariances of the Gaussian sharpness construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace SharpWasserstein.GaussianSharpness

theorem covariance_weightedSum (k : ℕ) (w z : Fin k → ℝ) :
    cov[fun ω : Fin k → ℝ => ∑ i, w i * ω i,
      fun ω : Fin k → ℝ => ∑ i, z i * ω i; standardLabels k] = ∑ i, w i*z i := by
  letI := standardLabels_probability k
  have h := variance_add (weightedSum_memLp k w) (weightedSum_memLp k z)
  have he : ((fun ω : Fin k → ℝ => ∑ i, w i * ω i) +
      (fun ω : Fin k → ℝ => ∑ i, z i * ω i)) =
      (fun ω : Fin k → ℝ => ∑ i, (w i + z i) * ω i) := by
    funext ω
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [he, variance_weightedSum, variance_weightedSum, variance_weightedSum] at h
  have hs : (∑ i, (w i+z i)^2) =
      (∑ i, (w i)^2) + (∑ i, (z i)^2) + 2*(∑ i, w i*z i) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

theorem matrixLaw_mean {m k : ℕ} (A : Fin k → Fin m → ℝ) (i : Fin k) :
    (∫ x, x i ∂matrixLaw A) = 0 := by
  unfold matrixLaw
  rw [integral_map (matrixMap A).continuous.measurable.aemeasurable
    (continuous_apply i).aestronglyMeasurable]
  simp only [matrixMap_apply]
  exact integral_weightedSum m _

theorem matrixLaw_covariance {m k : ℕ} (A : Fin k → Fin m → ℝ) (i j : Fin k) :
    cov[fun x => x i, fun x => x j; matrixLaw A] = ∑ l, A i l * A j l := by
  unfold matrixLaw
  rw [covariance_map_fun (continuous_apply i).aestronglyMeasurable
    (continuous_apply j).aestronglyMeasurable (matrixMap A).continuous.measurable.aemeasurable]
  simp_rw [matrixMap_apply]
  exact covariance_weightedSum m _ _

theorem commonNoiseLaw_mean (k : ℕ) (a s : ℝ) (i : Fin k) (j : Fin 1) :
    (∫ x, x i j ∂commonNoiseLaw k a s) = 0 := by
  unfold commonNoiseLaw
  rw [integral_map (scalarPositions k).continuous.measurable.aemeasurable
    ((continuous_apply j).comp (continuous_apply i)).aestronglyMeasurable]
  exact matrixLaw_mean _ i

theorem commonNoiseLaw_covariance (k : ℕ) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    (i j : Fin k) (p q : Fin 1) :
    cov[fun x => x i p, fun x => x j q; commonNoiseLaw k a s] =
      (if i = j then a else 0) + s := by
  unfold commonNoiseLaw
  rw [covariance_map_fun
    ((continuous_apply p).comp (continuous_apply i)).aestronglyMeasurable
    ((continuous_apply q).comp (continuous_apply j)).aestronglyMeasurable
    (scalarPositions k).continuous.measurable.aemeasurable]
  change cov[fun x => x i, fun x => x j; matrixLaw (commonNoiseMatrix k a s)] = _
  rw [matrixLaw_covariance, commonNoiseMatrix_gram k ha hs]

/-- The covariance is exactly aI+(1/N)11ᵀ on the first k coordinates. -/
theorem particleGaussianLaw_marginal_covariance {k N : ℕ} (hkN : k ≤ N) {a : ℝ}
    (ha : 0 ≤ a) (i j : Fin k) (p q : Fin 1) :
    cov[fun x => x i p, fun x => x j q; marginal hkN (particleGaussianLaw N a)] =
      (if i = j then a else 0) + 1/(N : ℝ) := by
  unfold particleGaussianLaw
  rw [marginal_commonNoiseLaw hkN ha (by positivity)]
  exact commonNoiseLaw_covariance k ha (by positivity) i j p q

theorem commonNoiseLaw_coordinate_memLp (k : ℕ) (a s : ℝ) (i : Fin k) (j : Fin 1) :
    MemLp (fun x : Configuration 1 k => x i j) 2 (commonNoiseLaw k a s) := by
  letI := commonNoiseLaw_isGaussian k a s
  let L : Configuration 1 k →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Position 1) i)
  exact IsGaussian.memLp_dual (commonNoiseLaw k a s) L 2 (by norm_num)

theorem commonNoiseLaw_coordinate_sq_integral (k : ℕ) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (i : Fin k) (j : Fin 1) :
    (∫ x, (x i j)^2 ∂commonNoiseLaw k a s) = a+s := by
  have h := commonNoiseLaw_covariance k ha hs i i j j
  have hm := (commonNoiseLaw_coordinate_memLp k a s i j).aemeasurable
  rw [covariance_self hm, variance_eq_integral hm, commonNoiseLaw_mean] at h
  simpa using h

theorem commonNoiseLaw_momentIntegral (k : ℕ) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    (∫ x, productCost x 0 ∂commonNoiseLaw k a s) = (k : ℝ)*(a+s) := by
  simp only [productCost, Pi.zero_apply, sub_zero]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (commonNoiseLaw_coordinate_memLp k a s i j).integrable_sq))]
  simp_rw [integral_finsetSum _ (fun j _ =>
    (commonNoiseLaw_coordinate_memLp k a s _ j).integrable_sq),
    commonNoiseLaw_coordinate_sq_integral k ha hs]
  simp
  ring

theorem commonNoiseLaw_secondMoment_value (k : ℕ) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    (∫⁻ x, ENNReal.ofReal (productCost x 0) ∂commonNoiseLaw k a s) =
      ENNReal.ofReal ((k : ℝ)*(a+s)) := by
  have hi : Integrable (fun x : Configuration 1 k => productCost x 0) (commonNoiseLaw k a s) := by
    simp only [productCost, Pi.zero_apply, sub_zero]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (commonNoiseLaw_coordinate_memLp k a s i j).integrable_sq))
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => productCost_nonneg x 0)),
    commonNoiseLaw_momentIntegral k ha hs]

/-- The actual Euclidean second moments are bounded on every compact time interval. -/
theorem particleGaussianLaw_uniform_momentBound (N : ℕ) {T : ℝ} (_hT : 0 ≤ T) :
    ∃ M : ℝ≥0∞, M < ∞ ∧ ∀ t ∈ Set.Icc 0 T,
      (∫⁻ x, ENNReal.ofReal (productCost x 0) ∂particleGaussianLaw N (1+2*t)) ≤ M := by
  refine ⟨ENNReal.ofReal ((N : ℝ)*(1+2*T+1/(N : ℝ))), ENNReal.ofReal_lt_top, ?_⟩
  intro t ht
  unfold particleGaussianLaw
  rw [commonNoiseLaw_secondMoment_value N (by linarith [ht.1]) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  gcongr
  exact ht.2

end SharpWasserstein.GaussianSharpness
