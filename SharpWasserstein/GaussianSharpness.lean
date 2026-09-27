import SharpWasserstein.RankOneTransport
import SharpWasserstein.Rates
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The genuine Gaussian rank-one transport cost

The laws are concrete linear images of a finite product of standard real
Gaussian probability measures. The exact transport cost is obtained from the
constructed coupling and the proved universal scalar-projection lower bound.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace SharpWasserstein.GaussianSharpness

open RankOneTransport

def standardLabels (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

theorem standardLabels_probability (k : ℕ) : IsProbabilityMeasure (standardLabels k) := by
  unfold standardLabels
  infer_instance

def standardVector (k : ℕ) (ω : Fin k → ℝ) : Vector 1 k :=
  WithLp.toLp 2 (fun i => ω i.1)

theorem standardVector_stronglyMeasurable (k : ℕ) : StronglyMeasurable (standardVector k) := by
  apply Continuous.stronglyMeasurable
  apply (PiLp.continuous_toLp 2 (fun _ : Fin k × Fin 1 => ℝ)).comp
  fun_prop

def commonDirection (k : ℕ) : Vector 1 k :=
  WithLp.toLp 2 (fun _ => (Real.sqrt (k : ℝ))⁻¹)

theorem commonDirection_norm {k : ℕ} (hk : 0 < k) : ‖commonDirection k‖ = 1 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hsq := Real.sq_sqrt hkR.le
  have hn : ‖commonDirection k‖ ^ 2 = 1 := by
    simp only [EuclideanSpace.real_norm_sq_eq, commonDirection,
      Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, mul_one, nsmul_eq_mul]
    rw [inv_pow, hsq]
    exact mul_inv_cancel₀ hkR.ne'
  nlinarith [norm_nonneg (commonDirection k)]

theorem commonMode_formula (k : ℕ) (ω : Fin k → ℝ) :
    ⟪commonDirection k, standardVector k ω⟫_ℝ =
      (Real.sqrt (k : ℝ))⁻¹ * ∑ i, ω i := by
  simp [PiLp.inner_apply, commonDirection, standardVector, Fintype.sum_prod_type,
    Finset.sum_mul, mul_comm]

theorem coordinate_memLp (k : ℕ) (i : Fin k) :
    MemLp (fun ω : Fin k → ℝ => ω i) 2 (standardLabels k) := by
  exact (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin k => gaussianReal 0 1) i)

theorem sum_memLp (k : ℕ) :
    MemLp (fun ω : Fin k → ℝ => ∑ i, ω i) 2 (standardLabels k) := by
  exact memLp_finsetSum Finset.univ (fun i _ => coordinate_memLp k i)

theorem integral_sum (k : ℕ) :
    (∫ ω : Fin k → ℝ, ∑ i, ω i ∂standardLabels k) = 0 := by
  letI := standardLabels_probability k
  rw [integral_finsetSum _ (fun i _ => (coordinate_memLp k i).integrable (by norm_num))]
  simp [standardLabels, integral_eval]

theorem variance_sum (k : ℕ) :
    Var[fun ω : Fin k → ℝ => ∑ i, ω i; standardLabels k] = (k : ℝ) := by
  have h := variance_sum_pi (μ := fun _ : Fin k => gaussianReal 0 1)
    (X := fun _ => id) (fun _ => memLp_id_gaussianReal' 2 (by norm_num))
  have he : (∑ i : Fin k, fun ω : Fin k → ℝ => id (ω i)) = (fun ω => ∑ i, ω i) := by
    funext ω
    simp
  rw [he] at h
  simpa [standardLabels] using h

theorem integral_sum_sq (k : ℕ) :
    (∫ ω : Fin k → ℝ, (∑ i, ω i) ^ 2 ∂standardLabels k) = (k : ℝ) := by
  have h := variance_sum k
  rw [variance_eq_integral (sum_memLp k).aemeasurable, integral_sum] at h
  simpa only [sub_zero] using h

theorem commonMode_eLpNorm {k : ℕ} (hk : 0 < k) :
    eLpNorm (fun ω => ⟪commonDirection k, standardVector k ω⟫_ℝ) 2 (standardLabels k) = 1 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkR
  simp only [commonMode_formula]
  change eLpNorm ((Real.sqrt (k : ℝ))⁻¹ • (fun ω : Fin k → ℝ => ∑ i, ω i)) 2
    (standardLabels k) = 1
  rw [eLpNorm_const_smul, (sum_memLp k).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [integral_sum_sq, ← Real.sqrt_eq_rpow]
  rw [← ofReal_norm, Real.norm_eq_abs, abs_inv, abs_of_pos hs,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hs.le), inv_mul_cancel₀ hs.ne', ENNReal.ofReal_one]

theorem weightedSum_memLp (k : ℕ) (w : Fin k → ℝ) :
    MemLp (fun ω : Fin k → ℝ => ∑ i, w i * ω i) 2 (standardLabels k) := by
  exact memLp_finsetSum Finset.univ (fun i _ => (coordinate_memLp k i).const_mul (w i))

theorem integral_weightedSum (k : ℕ) (w : Fin k → ℝ) :
    (∫ ω : Fin k → ℝ, ∑ i, w i * ω i ∂standardLabels k) = 0 := by
  letI := standardLabels_probability k
  rw [integral_finsetSum _ (fun i _ =>
    ((coordinate_memLp k i).const_mul (w i)).integrable (by norm_num))]
  simp [standardLabels, integral_const_mul, integral_eval]

theorem variance_weightedSum (k : ℕ) (w : Fin k → ℝ) :
    Var[fun ω : Fin k → ℝ => ∑ i, w i * ω i; standardLabels k] = ∑ i, (w i)^2 := by
  have h := variance_sum_pi (μ := fun _ : Fin k => gaussianReal 0 1)
    (X := fun i x => w i * x)
    (fun i => (memLp_id_gaussianReal' 2 (by norm_num)).const_mul (w i))
  have he : (∑ i : Fin k, fun ω : Fin k → ℝ => w i * ω i) =
      (fun ω => ∑ i, w i * ω i) := by funext ω; simp
  rw [he] at h
  have hv (i : Fin k) : Var[fun x : ℝ => w i * x; gaussianReal 0 1] = w i ^ 2 := by
    change Var[fun x => w i * id x; gaussianReal 0 1] = _
    rw [variance_const_mul, variance_id_gaussianReal]
    simp
  simp_rw [hv] at h
  exact h

theorem dual_eq_weightedSum (k : ℕ) (L : StrongDual ℝ (Fin k → ℝ)) (ω : Fin k → ℝ) :
    L ω = ∑ i, L (Pi.single i 1) * ω i := by
  rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : Fin k => ℝ) L ω]
  apply Finset.sum_congr rfl
  intro i _
  have h : Pi.single i (ω i) = ω i • Pi.single i (1 : ℝ) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, h,
    map_smul, smul_eq_mul]
  ring

theorem integral_dual (k : ℕ) (L : StrongDual ℝ (Fin k → ℝ)) :
    (∫ ω, L ω ∂standardLabels k) = 0 := by
  exact (integral_congr_ae (Filter.Eventually.of_forall (dual_eq_weightedSum k L))).trans
    (integral_weightedSum k _)

theorem variance_dual (k : ℕ) (L : StrongDual ℝ (Fin k → ℝ)) :
    Var[L; standardLabels k] = ∑ i, L (Pi.single i 1)^2 := by
  change Var[fun ω => L ω; standardLabels k] = _
  rw [show (fun ω => L ω) = (fun ω => ∑ i, L (Pi.single i 1) * ω i) from
    funext (dual_eq_weightedSum k L)]
  exact variance_weightedSum k _

theorem charFunDual_standardLabels (k : ℕ) (L : StrongDual ℝ (Fin k → ℝ)) :
    charFunDual (standardLabels k) L =
      Complex.exp (-((∑ i, L (Pi.single i 1)^2 : ℝ) : ℂ) / 2) := by
  rw [standardLabels, charFunDual_pi]
  have hi (i : Fin k) : charFunDual (gaussianReal 0 1)
      (L.comp (.single ℝ (fun _ : Fin k => ℝ) i)) =
      Complex.exp (-((L (Pi.single i 1)^2 : ℝ) : ℂ) / 2) := by
    rw [IsGaussian.charFunDual_eq, integral_complex_ofReal]
    have h : (fun x : ℝ => (L.comp (.single ℝ (fun _ : Fin k => ℝ) i)) x) =
        (fun x : ℝ => L (Pi.single i 1) * id x) := by
      funext x
      have he : Pi.single i x = x • Pi.single i (1 : ℝ) := by
        ext j
        by_cases hj : j = i <;> simp [hj]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, he,
        map_smul, smul_eq_mul, id_eq]
      ring
    change Complex.exp (((∫ x, (L.comp (.single ℝ (fun _ : Fin k => ℝ) i)) x
      ∂gaussianReal 0 1) : ℝ) * Complex.I -
      (Var[fun x => (L.comp (.single ℝ (fun _ : Fin k => ℝ) i)) x; gaussianReal 0 1] : ℂ) / 2) = _
    rw [h, integral_const_mul, variance_const_mul, variance_id_gaussianReal]
    simp [id_eq, integral_id_gaussianReal, neg_div]
  simp_rw [hi]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

/-- This is Gaussian in Mathlib's characteristic-functional sense, not merely by naming. -/
theorem standardLabels_isGaussian (k : ℕ) : IsGaussian (standardLabels k) := by
  letI := standardLabels_probability k
  apply isGaussian_of_charFunDual_eq
  intro L
  rw [charFunDual_standardLabels, integral_complex_ofReal, integral_dual, variance_dual]
  simp [neg_div]

/-- The isotropic Gaussian law with variance `a` in every coordinate, for `a ≥ 0`. -/
def independentLaw (k : ℕ) (a : ℝ) : Measure (Configuration 1 k) :=
  Measure.map (scaleLabel (Real.sqrt a) (standardVector k)) (standardLabels k)

/-- Increase only the normalized all-ones mode from variance `a` to `a+r`.
This is an explicit linear image of independent standard Gaussian coordinates. -/
def correlatedLaw (k : ℕ) (a r : ℝ) : Measure (Configuration 1 k) :=
  Measure.map (stretchLabel (Real.sqrt a) (Real.sqrt (a + r)) (commonDirection k)
    (standardVector k)) (standardLabels k)

/-- A one-dimensional position with law N(0,a), for nonnegative `a`. -/
def oneParticleGaussian (a : ℝ) : Measure (Position 1) :=
  Measure.map (fun z : ℝ => fun _ : Fin 1 => Real.sqrt a * z) (gaussianReal 0 1)

/-- The reference is exactly the product of the one-particle Gaussian law. -/
theorem independentLaw_tensor (k : ℕ) (a : ℝ) :
    independentLaw k a = tensorLaw (oneParticleGaussian a) k := by
  change (Measure.pi fun _ : Fin k => gaussianReal 0 1).map
    (fun ω i (_ : Fin 1) => Real.sqrt a * ω i) =
    Measure.pi (fun _ : Fin k =>
      (gaussianReal 0 1).map (fun z : ℝ => fun _ : Fin 1 => Real.sqrt a * z))
  exact Measure.pi_map_pi (μ := fun _ : Fin k => gaussianReal 0 1)
    (f := fun _ : Fin k => fun z : ℝ => fun _ : Fin 1 => Real.sqrt a * z)
    (fun _ => (by fun_prop))

theorem independentLaw_probability (k : ℕ) (a : ℝ) : IsProbabilityMeasure (independentLaw k a) := by
  letI := standardLabels_probability k
  exact Measure.isProbabilityMeasure_map
    (measurable_scaleLabel (Real.sqrt a) (standardVector_stronglyMeasurable k)).aemeasurable

theorem correlatedLaw_probability (k : ℕ) (a r : ℝ) : IsProbabilityMeasure (correlatedLaw k a r) := by
  letI := standardLabels_probability k
  exact Measure.isProbabilityMeasure_map
    (measurable_stretchLabel (Real.sqrt a) (Real.sqrt (a+r)) (commonDirection k)
      (standardVector_stronglyMeasurable k)).aemeasurable

/-- Exact cost for the concrete Gaussian laws; neither optimality nor the cost is assumed. -/
theorem gaussian_rankOne_transport {k : ℕ} (hk : 0 < k) (a r : ℝ) (hr : 0 ≤ r) :
    wassersteinSq (correlatedLaw k a r) (independentLaw k a) = ENNReal.ofReal (gaussianModeCost a r) := by
  letI := standardLabels_probability k
  exact wassersteinSq_stretch_scale (standardLabels k) (standardVector_stronglyMeasurable k)
    (commonDirection k) (commonDirection_norm hk) (commonMode_eLpNorm hk)
    (Real.sqrt_nonneg a) (Real.sqrt_le_sqrt (by linarith))

/-- The exact rationalized expression in the manuscript, for the constructed laws. -/
theorem gaussian_rankOne_transport_rationalized {k N : ℕ} (hk : 0 < k) (a : ℝ) (ha : 0 < a) :
    wassersteinSq (correlatedLaw k a ((k : ℝ) / N)) (tensorLaw (oneParticleGaussian a) k) =
      ENNReal.ofReal (localRate k N / (Real.sqrt (a + (k : ℝ) / N) + Real.sqrt a) ^ 2) := by
  rw [← independentLaw_tensor, gaussian_rankOne_transport hk a _ (by positivity),
    gaussianModeCost_rationalized ha (by positivity)]
  simp only [localRate, div_pow]

/-- The initial cost bound at each positive level has the concrete constant C₀=1/4. -/
theorem gaussian_initial_bound {k N : ℕ} (hk : 0 < k) (hN : 0 < N) :
    wassersteinSq (correlatedLaw k 1 ((k : ℝ) / N)) (tensorLaw (oneParticleGaussian 1) k) ≤
      ENNReal.ofReal ((1 / 4 : ℝ) * localRate k N) := by
  have hr : 0 ≤ (k : ℝ) / N :=
    div_nonneg (Nat.cast_nonneg k) (by exact_mod_cast Nat.le_of_lt hN)
  rw [← independentLaw_tensor, gaussian_rankOne_transport hk 1 _ hr]
  apply ENNReal.ofReal_le_ofReal
  have h := gaussianModeCost_initial_upper hr
  convert h using 1
  simp [localRate]
  ring

/-- At each fixed nonnegative time, the actual costs have the matching (k/N)² lower bound. -/
theorem gaussian_fixed_time_lower {k N : ℕ} (hk : 0 < k) (hkN : k ≤ N)
    (t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (localRate k N /
      (Real.sqrt ((1 + 2 * t) + 1) + Real.sqrt (1 + 2 * t)) ^ 2) ≤
      wassersteinSq (correlatedLaw k (1 + 2 * t) ((k : ℝ) / N))
        (tensorLaw (oneParticleGaussian (1 + 2 * t)) k) := by
  have hN : 0 < N := hk.trans_le hkN
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hr : 0 ≤ (k : ℝ) / N := by positivity
  have hr1 : (k : ℝ) / N ≤ 1 := (div_le_one hNr).mpr (by exact_mod_cast hkN)
  rw [← independentLaw_tensor, gaussian_rankOne_transport hk (1 + 2*t) _ hr]
  apply ENNReal.ofReal_le_ofReal
  simpa only [localRate, div_pow] using gaussianModeCost_lower (by linarith : 0 < 1 + 2*t) hr hr1

end SharpWasserstein.GaussianSharpness
